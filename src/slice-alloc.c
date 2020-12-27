/*
 * slice-alloc - a memory allocation library.
 *
 * Copyright (C) 2020  Aleksey Demakov
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301
 * USA
 */

#include "slice-alloc.h"

#include <errno.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdnoreturn.h>
#include <string.h>
#include <unistd.h>

#include <pthread.h>

#include <sys/mman.h>

/**********************************************************************
 * Common macros.
 **********************************************************************/

// Minimum alignment.
#define ALIGNMENT		(16)
// CPU cache-line size.
#define CACHELINE		(64)
// Virtual memory page size.
#define PAGE_SIZE		(4096)

#define likely(x)		__builtin_expect(!!(x), 1)
#define unlikely(x)		__builtin_expect(!!(x), 0)

#define ALIGN(x)		__attribute__((__aligned__(x)))
#define CACHE_ALIGN		ALIGN(CACHELINE)

#define min(a, b) ({			\
		typeof(a) _a = (a);	\
		typeof(b) _b = (b);	\
		_a < _b ? _a : _b;	\
	})

#define max(a, b) ({			\
		typeof(a) _a = (a);	\
		typeof(b) _b = (b);	\
		_a > _b ? _a : _b;	\
	})

#define containerof(field_ptr, type, field) \
	((type *) ((char *)(field_ptr) - offsetof(type, field)))

#define stringify_(x)		#x
#define stringify(x)		stringify_(x)

#define LOCATION		__FILE__ ":" stringify(__LINE__)

/**********************************************************************
 * Abnormal termination.
 **********************************************************************/

#define ASSERT(e)	(likely(e) ? (void) 0 : panic("panic: " LOCATION ": assertion failed\n"))
#define VERIFY(e, msg)	(likely(e) ? (void) 0 : panic("panic: " LOCATION ": " msg "\n"))

static void noreturn
panic(const char *msg)
{
	size_t len = strlen(msg);
	while (len) {
		ssize_t rc = write(2, msg, len);
		if (rc < 0)
			break;
		msg += rc;
		len -= rc;
	}
	abort();
}

/**********************************************************************
 * Bit operations.
 **********************************************************************/

/* Count leading zeros (from MSB). Zero argument is not allowed. */
#define clz(x) ({					\
		unsigned _r;				\
		typeof(x) _x = x;			\
		if (sizeof(_x) <= sizeof(int))		\
			_r = __builtin_clz(_x);		\
		else if (sizeof(_x) <= sizeof(long))	\
			_r = __builtin_clzl(_x);	\
		else					\
			_r = __builtin_clzll(_x);	\
		_r;					\
	})

/* Count trailing zeros (from LSB). Zero argument is not allowed. */
#define ctz(x) ({					\
		unsigned _r;				\
		typeof(x) _x = x;			\
		if (sizeof(_x) <= sizeof(int))		\
			_r = __builtin_ctz(_x);		\
		else if (sizeof(_x) <= sizeof(long))	\
			_r = __builtin_ctzl(_x);	\
		else					\
			_r = __builtin_ctzll(_x);	\
		_r;					\
	})

/* Count all bits in an integer. */
#define nbits(x) ({						\
		unsigned _r;					\
		if (sizeof(typeof(x)) <= sizeof(int))		\
			_r = 8 * sizeof(int);			\
		else if (sizeof(typeof(x)) <= sizeof(long))	\
			_r = 8 * sizeof(long);			\
		else						\
			_r = 8 * sizeof(long long);		\
		_r;						\
	})

/* Check if a number is a power of 2 or zero. */
#define is_pow2z(x) ({					\
		typeof(x) _x = (x);			\
		(_x & (_x - 1)) == 0;			\
	})

// Round up to a power of 2 multiple.
#define pow2_round_up(x, p) ({				\
		typeof(x) _x = (x);			\
		typeof(p) _p = (p);			\
		(_x + _p - 1) & ~(_p - 1);		\
	})


/**********************************************************************
 * Spin lock.
 **********************************************************************/

#define SPINLOCK_INIT { ATOMIC_VAR_INIT(false) }

typedef struct CACHE_ALIGN
{
	atomic_bool lock;
} spinlock_t;

static inline void
spin_pause(void)
{
#if defined(__x86_64__) || defined(__i386__)
	__builtin_ia32_pause();
#endif
}

static inline bool
spin_is_locked(spinlock_t *lock)
{
	return atomic_load_explicit(&lock->lock, memory_order_relaxed);
}

static inline bool
spin_try_lock(spinlock_t *lock)
{
	return !atomic_exchange_explicit(&lock->lock, true, memory_order_acquire);
}

static inline void
spin_lock(spinlock_t *lock)
{
	while (!spin_try_lock(lock)) {
		do
			spin_pause();
		while (spin_is_locked(lock));
	}
}

static inline void
spin_unlock(spinlock_t *lock)
{
	atomic_store_explicit(&lock->lock, false, memory_order_release);
}

/**********************************************************************
 * MPSC concurrent queue.
 **********************************************************************/

/*
 * This is basically Dmitry Vyukov's intrusive MPSC node-based queue:
 *
 * http://www.1024cores.net/home/lock-free-algorithms/queues/intrusive-mpsc-node-based-queue
 *
 * The only thing is that here the 'tail' and 'head' have reverse meanining.
 */

struct mpsc_qlink
{
	 struct mpsc_qlink *_Atomic next;
};

struct mpsc_queue
{
	CACHE_ALIGN struct mpsc_qlink *_Atomic tail;
	CACHE_ALIGN struct mpsc_qlink *head;
	struct mpsc_qlink stub;
};

static inline void
mpsc_qlink_prepare(struct mpsc_qlink *link)
{
	atomic_init(&link->next, NULL);
}

static inline void
mpsc_queue_prepare(struct mpsc_queue *list)
{
	list->head = &list->stub;
	atomic_init(&list->tail, &list->stub);
	mpsc_qlink_prepare(&list->stub);
}

static inline void
mpsc_queue_append_span(struct mpsc_queue *list, struct mpsc_qlink *head, struct mpsc_qlink *tail)
{
	struct mpsc_qlink *prev = atomic_exchange(&list->tail, tail);
	atomic_store_explicit(&prev->next, head, memory_order_release);
}

static inline void
mpsc_queue_append(struct mpsc_queue *list, struct mpsc_qlink *link)
{
	mpsc_queue_append_span(list, link, link);
}

static struct mpsc_qlink *
mpsc_queue_remove(struct mpsc_queue *list)
{
	struct mpsc_qlink *head = list->head;
	struct mpsc_qlink *next = atomic_load_explicit(&head->next, memory_order_acquire);
	if (head == &list->stub) {
		if (next == NULL)
			return NULL;
		list->head = head = next;
		next = atomic_load_explicit(&next->next, memory_order_acquire);
	}
	if (next != NULL) {
		list->head = next;
		return head;
	}

	struct mpsc_qlink *tail = atomic_load_explicit(&list->tail, memory_order_acquire);
	if (tail != head)
		return NULL;

	mpsc_qlink_prepare(&list->stub);
	mpsc_queue_append(list, &list->stub);
	next = atomic_load_explicit(&head->next, memory_order_acquire);
	if (next) {
		list->head = next;
		return head;
	}
	return NULL;
}

/**********************************************************************
 * Double linked lists.
 **********************************************************************/

static inline void
list_prepare(struct slice_cache_list *list)
{
	list->node.next = list->node.prev = &list->node;
}

static inline const struct slice_cache_node *
list_stub(const struct slice_cache_list *list)
{
	return &list->node;
}

static inline struct slice_cache_node *
list_head(struct slice_cache_list *list)
{
	return list->node.next;
}

static inline struct slice_cache_node *
list_tail(struct slice_cache_list *list)
{
	return list->node.prev;
}

static inline bool
list_empty(const struct slice_cache_list *list)
{
	return list->node.next == list_stub(list);
}

static inline void
list_delete(struct slice_cache_node *node)
{
	node->prev->next = node->next;
	node->next->prev = node->prev;
}

static inline void
list_splice_after(struct slice_cache_node *node, struct slice_cache_node *head, struct slice_cache_node *tail)
{
	head->prev = node;
	tail->next = node->next;
	node->next->prev = tail;
	node->next = head;
}

static inline void
list_insert_after(struct slice_cache_node *node, struct slice_cache_node *node2)
{
	list_splice_after(node, node2, node2);
}

static inline void
list_splice_first(struct slice_cache_list *list, struct slice_cache_node *head, struct slice_cache_node *tail)
{
	list_splice_after(&list->node, head, tail);
}

static inline void
list_insert_first(struct slice_cache_list *list, struct slice_cache_node *node)
{
	list_insert_after(&list->node, node);
}

static inline struct slice_cache_node *
list_remove_first(struct slice_cache_list *list)
{
	struct slice_cache_node *head = list_head(list);
	list_delete(head);
	return head;
}

/**********************************************************************
 * Memory spans.
 **********************************************************************/

/*
 * A memory span is a big memory area allocated with a mmap() system call.
 * A span always starts at an address that is aligned to a 2 MiB boundary.
 * And it always starts with a header that describes the span.
 *
 * There are two kinds of spans:
 *   -- regular spans used to store a number of smaller memory chunks;
 *   -- singular spans used to store a single large chunk that doesn't fit
 *      a regular span.
 *
 * Regular spans always take 2 MiB of memory. Singular spans vary in size.
 */

// Span alignment values.
#define SPAN_ALIGNMENT		(((size_t) 1) << 21)
#define SPAN_ALIGNMENT_MASK	(SPAN_ALIGNMENT - 1)

// The size of a regular span.
#define SPAN_REGULAR_SIZE	SPAN_ALIGNMENT

// The value that tags regular spans.
#define SPAN_REGULAR_TAG	((size_t) 0)

// Span header.
struct span_header
{
	// The tag for regular spans or usable size for singular spans.
	size_t tag_or_size;
	// The memory size that is actually mmap()-ed.
	size_t virtual_size;

	// The memory cache the span belongs to.
	struct slice_cache *cache;
};

// Singular span header.
struct singular_span
{
	struct span_header header;

	// The offset of the allocated memory chunk.
	size_t offset;
};

// Singular span creation parameters.
struct singular_span_params
{
	// The memory size to be actually mmap()-ed.
	size_t virtual_size;
	// The offset of the allocated memory chunk.
	size_t offset;
};

// Get the span header for an address within 2MiB from it.
static inline struct span_header *
span_from_ptr(const void *ptr)
{
	return (struct span_header *) ((uintptr_t) ptr & ~SPAN_ALIGNMENT_MASK);
}

// Get the actual size of virtual memory occupied by the span.
static inline size_t
span_virtual_size(const struct span_header *hdr)
{
	return hdr->virtual_size;
}

// Check to see if the span is for regular chunks.
static inline bool
span_is_regular(const struct span_header *hdr)
{
	return (hdr->tag_or_size == SPAN_REGULAR_TAG);
}

// Check to see if the span is for a single large chunk.
static inline bool
span_is_singular(const struct span_header *hdr)
{
	return (hdr->tag_or_size != SPAN_REGULAR_TAG);
}

static inline size_t
span_singular_size(const struct span_header *hdr)
{
	return hdr->tag_or_size;
}

static inline void *
span_singular_data(const struct span_header *hdr)
{
	const struct singular_span *span = containerof(hdr, struct singular_span, header);
	return (uint8_t *) hdr + span->offset;
}

static void
span_free_space(void *const addr, const size_t size)
{
	if (unlikely(munmap(addr, size) < 0))
		panic("panic: failed munmap() call\n");
}

static void *
span_alloc_space(const size_t size, const size_t addr_mask)
{
	// Allocate a span speculatively assuming that it will be aligned as required.
	void *addr = mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
	if (addr == MAP_FAILED)
		return NULL;

	// If failed to align then repeat allocation with required padding.
	if ((((uintptr_t) addr) & addr_mask) != 0) {
		span_free_space(addr, size);

		const size_t upsized_size = size + addr_mask - PAGE_SIZE + 1;
		if (upsized_size < size) {
			// Integer aritmetic overflow.
			return NULL;
		}

		void *upsized_addr = mmap(NULL, upsized_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
		if (upsized_addr == MAP_FAILED)
			return NULL;

		addr = (void *) ((((uintptr_t) upsized_addr) + addr_mask) & ~addr_mask);
		const size_t leading_size = addr - upsized_addr;
		const size_t trailing_size = upsized_size - leading_size - size;
		if (leading_size)
			span_free_space(upsized_addr, leading_size);
		if (trailing_size)
			span_free_space(addr + size, trailing_size);
	}

	return addr;
}

static struct span_header *
span_create_regular(struct slice_cache *const cache)
{
	struct span_header *hdr = span_alloc_space(SPAN_REGULAR_SIZE, SPAN_ALIGNMENT_MASK);
	if (likely(hdr != NULL)) {
		hdr->tag_or_size = SPAN_REGULAR_TAG;
		hdr->virtual_size = SPAN_REGULAR_SIZE;
		hdr->cache = cache;
	}
	return hdr;
}

static inline struct singular_span_params
span_compute_singular(const size_t size, const size_t alignment)
{
	size_t offset = alignment;
	if (offset < sizeof(struct singular_span)) {
		if (offset == 0)
			offset = sizeof(struct singular_span);
		else
			offset *= (sizeof(struct singular_span) + offset - 1) / offset;
	}

	const size_t total_size = pow2_round_up(offset + size, PAGE_SIZE);
	if (unlikely(total_size < size)) {
		// Integer aritmetic overflow.
		return (struct singular_span_params) { 0, 0 };
	}

	return (struct singular_span_params) { total_size, offset };
}

static struct span_header *
span_create_singular(struct slice_cache *const cache, const size_t size, const size_t alignment)
{
	const struct singular_span_params params = span_compute_singular(size, alignment);
	if (params.virtual_size == 0)
		return NULL;

	struct singular_span *span = span_alloc_space(params.virtual_size, SPAN_ALIGNMENT_MASK);
	if (likely(span != NULL)) {
		span->header.tag_or_size = params.virtual_size - params.offset;
		span->header.virtual_size = params.virtual_size;
		span->header.cache = cache;
		span->offset = params.offset;
	}
	return &span->header;
}

static void
span_destroy(struct span_header *const hdr)
{
	span_free_space(hdr, span_virtual_size(hdr));
}

/**********************************************************************
 * Regular memory spans.
 **********************************************************************/

typedef enum
{
	SPAN_ACTIVE = 0,
	SPAN_STAGING = 1
} span_status_t;

// The number of chunk ranks. 
#define INNER_CHUNK_RANKS	(16u)
#define OUTER_CHUNK_RANKS	(20u)
#define CHUNK_RANKS		(INNER_CHUNK_RANKS + OUTER_CHUNK_RANKS)
#define SLICE_RANKS		(36u)
#define CACHE_RANKS		(CHUNK_RANKS + SLICE_RANKS)

// The number of ranks that are allocated by halving.
#define BUDDY_RANKS		(SLICE_RANKS - 12u)

// The rank distance between an inner chunk and its parent outer chunk.
#define INNER_TO_OUTER		(20u)
// The rank distance between an outer chunk and its parent slice.
#define OUTER_TO_SLICE		(20u)

// Sizes of the memory map units in a regular span.
#define HEAD_SIZE		(4096u)
#define UNIT_SIZE		(1024u)
#define UNIT_NUMBER		(2048u)

// Constants used for encoding of chunk ranks.
#define UNIT_LBITS		(6u)
#define UNIT_HBITS		(5u)
#define UNIT_LMASK		((1u << UNIT_LBITS) - 1u)
#define UNIT_HMASK		((1u << UNIT_HBITS) - 1u)

#define BASE_TAG		(128u)
#define NEXT_TAG		(192u)

#define MAKE_SIZE(r, m)		((size_t) (4u | (m)) << (r + 1u))

#define MAGIC_SHIFT		(18u)
#define MAGIC_FACTOR		(1u << MAGIC_SHIFT)
#define MAKE_MAGIC(r, m)	((MAGIC_FACTOR + MAKE_SIZE(r, m) - 1u) / MAKE_SIZE(r, m))

#define RANKS_ROW(r, _)		_(r, 0u), _(r, 1u), _(r, 2u), _(r, 3u)
#define LOWER_RANKS(_)		\
	RANKS_ROW(0u, _),	\
	RANKS_ROW(1u, _),	\
	RANKS_ROW(2u, _),	\
	RANKS_ROW(3u, _),	\
	RANKS_ROW(4u, _),	\
	RANKS_ROW(5u, _),	\
	RANKS_ROW(6u, _),	\
	RANKS_ROW(7u, _),	\
	RANKS_ROW(8u, _)
#define UPPER_RANKS(_)		\
	RANKS_ROW(9u, _),	\
	RANKS_ROW(10u, _),	\
	RANKS_ROW(11u, _),	\
	RANKS_ROW(12u, _),	\
	RANKS_ROW(13u, _),	\
	RANKS_ROW(14u, _),	\
	RANKS_ROW(15u, _),	\
	RANKS_ROW(16u, _),	\
	RANKS_ROW(17u, _)

// The header struct for a block of small chunks.
struct inner_block
{
        // A bitset of free chunks. The very first chunk is never free as
	// it is used for the header itself.
	uint32_t free;
};

// The header struct for a block of medium chunks.
struct outer_block
{
	struct outer_block *next;
	struct outer_block *inner_next;

        // A bitset of free chunks. The very first chunk is never free as
	// it is used for the header itself.
	uint32_t chunk_free;

        // A bitset of chunks used for small chunks.
	uint32_t inner_used;
	// A bitset of chunks with some free small chunks.
	uint32_t inner_free;
};

// Regular span header.
struct slice_alloc_span
{
	struct span_header header;

	struct slice_cache_node staging_node;
	span_status_t status;

	/* Statistics. */
	uint64_t alloc_num;
	uint64_t free_num;

	// The list of chunks freed remotely.
	struct mpsc_queue remote_free_list;

	// Cached chunk blocks and slices.
	struct outer_block *blocks[CHUNK_RANKS];
	uint16_t slices[SLICE_RANKS];

	// The map of units.
	uint8_t units[UNIT_NUMBER];
};

// Memory rank sizes.
static const uint32_t memory_sizes[] = {
	LOWER_RANKS(MAKE_SIZE),
	UPPER_RANKS(MAKE_SIZE)
};

// Chunk size magic numbers.
static const uint32_t memory_magic[] = {
	LOWER_RANKS(MAKE_MAGIC)
};

static inline uint32_t
get_rank(size_t size)
{
	if (size-- <= 8)
		return 0;

	// Search for most significant set bit, on x86 this should translate
	// to a single BSR instruction.
	const uint32_t msb = clz(size) ^ (nbits(size) - 1);

	// Calcualte the rank.
	return (msb << 2u) + (size >> (msb - 2u)) - 15u;
}

static inline uint32_t
decode_base(uint8_t hi, uint8_t lo)
{
	return ((uint32_t) hi << UNIT_LBITS) | (lo & UNIT_LMASK);
}

static uint32_t
deduce_base(const struct slice_alloc_span *const span, const void *const ptr)
{
	const uint32_t offset = (uint8_t *) ptr - (uint8_t *) span;
	const uint32_t unit = offset / UNIT_SIZE;

	const uint8_t x = span->units[unit];
	if (x <= UNIT_HMASK) {
		const uint8_t y = span->units[unit - 1];
		VERIFY(y >= BASE_TAG, "bad pointer");
		return decode_base(x, y);
	}
	if (x >= BASE_TAG) {
		const uint8_t y = span->units[unit - 1];
		if (y <= UNIT_HMASK)
			return decode_base(y, x);
		return unit - 1;
	}

	return unit;
}

static void
free_slice(struct slice_alloc_span *const span, const uint32_t base, const uint32_t rank)
{
	ASSERT(rank >= CHUNK_RANKS);
	const uint32_t next = span->slices[rank - CHUNK_RANKS];
	span->units[base + 1] = next | NEXT_TAG;
	span->units[base + 2] = next >> UNIT_LBITS;
	span->slices[rank - CHUNK_RANKS] = base;
}

static uint32_t
find_slice(const struct slice_alloc_span *const span, uint32_t rank)
{
	ASSERT(rank >= CHUNK_RANKS && rank < CACHE_RANKS);

	while (rank < (CHUNK_RANKS + BUDDY_RANKS)) {
		if (span->slices[rank - CHUNK_RANKS])
			return rank;
		rank += 4;
	}
	while (rank < CACHE_RANKS) {
		if (span->slices[rank - CHUNK_RANKS])
			return rank;
		rank += 1;
	}

	return rank;
}

static void
cut_one(struct slice_alloc_span *const span, const uint32_t base, const uint32_t rank)
{
	span->units[base] = rank;
	free_slice(span, base, rank);
}

static void
cut_two(struct slice_alloc_span *const span, const uint32_t base, const uint32_t first, const uint32_t second)
{
	cut_one(span, base, first);
	cut_one(span, base + memory_sizes[first] / UNIT_SIZE, second);
}

static void
split_slice(struct slice_alloc_span *const span, const uint32_t original_base, const uint32_t original_rank, const uint32_t required_rank)
{
	// Here the rank value is adjusted to large-only sizes.
	ASSERT(original_rank > CHUNK_RANKS && original_rank <= CACHE_RANKS);
	ASSERT(required_rank >= CHUNK_RANKS && required_rank < CACHE_RANKS);
	ASSERT(original_rank > required_rank);

	uint32_t base = original_base;
	uint32_t rank = required_rank;

	// Set the required slice on top of the original slice.
	span->units[base] = rank;
	base += memory_sizes[rank] / UNIT_SIZE;

	// Cut off the extra space from it slice-by-slice with doubling
	// slice sizes:
	//
	//    +-------------------- <original slice>
	//    V
	//   [..............................]
	//
	//    +-------------------- <required slice>
	//    |   +---------------- <extra slices>
	//    |   |
	//    V   V
	//   [..][..][......][..............]
	//
	while (rank < (CHUNK_RANKS + BUDDY_RANKS)) {
		cut_one(span, base, rank);
		base += memory_sizes[rank] / UNIT_SIZE;

		rank += 4;
		if (rank == original_rank) {
			// Done.
			return;
		}
	}

	// For the few topmost ranks it is impossible to use doubling as
	// the result would exceed the maximum possible slice size. For
	// the preceding top ranks doubling is techically possibe but is
	// too wasteful. So large slices are cut off with a finer method.
	const uint32_t distance = original_rank - rank;
	switch (distance) {
	case 1:
		cut_one(span, base, (rank & ~3u) - 8);
		break;
	case 2:
		switch ((rank & 3)) {
		case 0:
			cut_one(span, base, rank - 4);
			break;
		case 1: case 3:
			cut_one(span, base, rank - 5);
			break;
		case 2:
			cut_one(span, base, rank - 6);
			break;
		}
		break;
	case 3:
		switch ((rank & 3)) {
		case 0: case 2: case 3:
			cut_one(span, base, rank - 2);
			break;
		case 1:
			cut_one(span, base, rank - 3);
			break;
		}
		break;
	case 4:
		cut_one(span, base, rank);
		break;
	case 5:
		switch ((rank & 3)) {
		case 0:	case 1: case 2:
			cut_one(span, base, rank + 2);
			break;
		case 3:
			cut_two(span, base, rank - 3, rank - 2);
			break;
		}
		break;
	case 6:
		switch ((rank & 3)) {
		case 0:
			cut_one(span, base, rank + 4);
			break;
		case 1:
			cut_two(span, base, rank - 1, rank);
			break;
		case 2:
			cut_one(span, base, rank + 3);
			break;
		case 3:
			cut_two(span, base, rank - 2, rank + 1);
			break;
		}
		break;
	case 7:
		switch ((rank & 3)) {
		case 0: case 2:
			cut_one(span, base, rank + 5);
			break;
		case 1:
			cut_two(span, base, rank - 1, rank + 2);
			break;
		case 3:
			cut_two(span, base, rank - 2, rank + 3);
			break;
		}
		break;
	case 8:
		switch ((rank & 3)) {
		case 0:
			cut_one(span, base, rank + 6);
			break;
		case 1:	case 2:
			cut_two(span, base, rank + 2, rank + 3);
			break;
		case 3:
			cut_two(span, base, rank - 2, rank + 5);
			break;
		}
		break;
	case 9:
		if (rank == (CACHE_RANKS - 12)) {
			cut_one(span, base, CACHE_RANKS - 4);
		} else if (rank == (CACHE_RANKS - 11)) {
			cut_two(span, base, CACHE_RANKS - 9, CACHE_RANKS - 6);
		} else if (rank == (CACHE_RANKS - 10)) {
			cut_two(span, base, CACHE_RANKS - 8, CACHE_RANKS - 5);
		} else {
			ASSERT(rank == (CACHE_RANKS - 9));
			cut_two(span, base, CACHE_RANKS - 11, CACHE_RANKS - 3);
		}
		break;
	case 10:
		if (rank == (CACHE_RANKS - 12)) {
			cut_one(span, base, CACHE_RANKS - 3);
		} else if (rank == (CACHE_RANKS - 11)) {
			cut_two(span, base, CACHE_RANKS - 9, CACHE_RANKS - 4);
		} else {
			ASSERT(rank == (CACHE_RANKS - 10));
			cut_two(span, base, CACHE_RANKS - 7, CACHE_RANKS - 4);
		}
		break;
	case 11:
		if (rank == (CACHE_RANKS - 12)) {
			cut_one(span, base, CACHE_RANKS - 2);
		} else {
			ASSERT(rank == (CACHE_RANKS - 11));
			cut_two(span, base, CACHE_RANKS - 9, CACHE_RANKS - 3);
		}
		break;
	case 12:
		ASSERT(rank == (CACHE_RANKS - 12));
		cut_one(span, base, CACHE_RANKS - 1);
		break;
	default:
		ASSERT(false);
	}
}

static void
prepare_span(struct slice_alloc_span *const span)
{
	// As the span comes after a fresh mmap() call there is no need
	// to zero it out manually.
#if 0
	span->status = SPAN_ACTIVE;
	span->alloc_num = 0;
	span->free_num = 0;

	for (uint32_t i = 0; i < CHUNK_RANKS; i++)
		span->blocks[i] = NULL;
	for (uint32_t i = 0; i < SLICE_RANKS; i++)
		span->slices[i] = 0;

	memset(span->units, 0, sizeof span->units);
#endif

	// Initialize the remote free list.
	mpsc_queue_prepare(&span->remote_free_list);

	// The initial heap layout takes out the very first 4KiB slice
	// from the span. It is used up for the very span header that is
	// initialized here.
	split_slice(span, 0, CACHE_RANKS, CHUNK_RANKS);
}

static void *
alloc_slice(struct slice_cache *const cache, const uint32_t required_rank, const bool block)
{
	ASSERT(required_rank >= CHUNK_RANKS && required_rank < CACHE_RANKS);

	struct slice_alloc_span *span = cache->active;
	uint32_t original_rank = find_slice(span, required_rank);
	if (original_rank >= CACHE_RANKS) {
		// TODO: Try to coalesce freed memory in the active span.

		span = NULL;

		// Try to find a suitable span in the staging list.
		struct slice_cache_node *node = list_head(&cache->staging);
		while (node != list_stub(&cache->staging)) {
			struct slice_alloc_span *next = containerof(node, struct slice_alloc_span, staging_node);
			original_rank = find_slice(next, required_rank);
			if (original_rank < CACHE_RANKS) {
				next->status = SPAN_ACTIVE;
				list_delete(node);
				span = next;
				break;
			}
			node = node->next;
		}

		// Allocate a new span if none found.
		if (span == NULL) {
			span = (struct slice_alloc_span *) span_create_regular(cache);
			if (span == NULL) {
				// Out of memory.
				return NULL;
			}

			prepare_span(span);
			original_rank = find_slice(span, required_rank);
			ASSERT(original_rank < CACHE_RANKS);
		}

		cache->active->status = SPAN_STAGING;
		list_insert_first(&cache->staging, &cache->active->staging_node);
		cache->active = span;
	}

	// Remove the slice from the free list.
	const uint32_t index = original_rank - CHUNK_RANKS;
	const uint32_t base = span->slices[index];
	span->slices[index] = decode_base(span->units[base + 2], span->units[base + 1]);

	// If the slice is bigger than required then split it.
	if (original_rank != required_rank)
		split_slice(span, base, original_rank, required_rank);

	if (!block) {
		// The slice is to be used as such.
		span->units[base + 1] = 0;
		span->units[base + 2] = 0;

		span->alloc_num++;
		cache->regular_alloc_num++;
	} else {
		// The slice is to be used as a block. Fill the unit map.
		const uint8_t bytes[4] = {
			(base & UNIT_LMASK) | BASE_TAG,
			base >> UNIT_LBITS,
			(base & UNIT_LMASK) | BASE_TAG,
			base >> UNIT_LBITS
		};

		uint8_t *const map = &span->units[base + 1];
		const uint32_t end = memory_sizes[required_rank] / UNIT_SIZE - 1;
		const uint32_t loop_end = end & ~3u;
		const uint32_t tail = end & 3u;

		uint32_t i = 0;
		while (i < loop_end) {
			memcpy(&map[i], bytes, 4);
			i += 4;
		}
		if ((tail & 2) != 0) {
			memcpy(&map[i], bytes, 2);
			i += 2;
		}
		if ((tail & 1) != 0) {
			map[i] = bytes[0];
		}
	}

	return (uint8_t *) span + base * UNIT_SIZE;
}

static struct outer_block *
alloc_outer(struct slice_cache *const cache, const uint32_t rank)
{
	// Allocate a large chunk.
	struct outer_block *const block = alloc_slice(cache, rank + OUTER_TO_SLICE, true);
	if (unlikely(block == NULL))
		return NULL;

	// Set it up as a block.
	block->inner_next = NULL;
	block->inner_used = 0;
	block->inner_free = 0;

	// One slot is used for 'struct mm_memory_block', another will be used
	// for allocation right away.
	block->chunk_free = 0xfffc;

	// TODO: allocating a slice may take a span from the staging list with
	// existing blocks of the required size. Thus we allocated a slice for
	// no reason. Fix this.

	// Cache the block for futher use.
	block->next = cache->active->blocks[rank];
	cache->active->blocks[rank] = block;

	return block;
}

static void *
alloc_chunk(struct slice_cache *const cache, const uint32_t rank)
{
	if (rank >= INNER_CHUNK_RANKS) {
		// Handle medium sizes.

		// Use a cached block if any.
		struct outer_block *block = cache->active->blocks[rank];
		if (block != NULL) {
			ASSERT(block->chunk_free);
			const uint32_t shift = ctz(block->chunk_free);
			block->chunk_free ^= (1u << shift);
			if (block->chunk_free == 0) {
				// Remove a fully used block.
				cache->active->blocks[rank] = block->next;
			}

			cache->active->alloc_num++;
			cache->regular_alloc_num++;
			return (uint8_t *) block + shift * memory_sizes[rank];
		}

		// Allocate a new block.
		block = alloc_outer(cache, rank);
		if (unlikely(block == NULL))
			return NULL;

		cache->active->alloc_num++;
		cache->regular_alloc_num++;
		return (uint8_t *) block + memory_sizes[rank];

	} else {
		// Handle small sizes.

		// Use a cached inner block if any.
		struct outer_block *block = cache->active->blocks[rank];
		const uint32_t outer_rank = rank + INNER_TO_OUTER;
		if (block != NULL) {
			ASSERT(block->inner_free);
			const uint32_t shift = ctz(block->inner_free);
			uint8_t *const inner_base = ((uint8_t *) block) + shift * memory_sizes[outer_rank];

			struct inner_block *const inner = (struct inner_block *) inner_base;
			ASSERT(inner->free);
			const uint32_t inner_shift = ctz(inner->free);
			inner->free ^= (1u << inner_shift);
			if (inner->free == 0) {
				block->inner_free ^= (1u << shift);
				if (block->inner_free == 0) {
					// Remove a fully used inner block.
					cache->active->blocks[rank] = block->inner_next;
				}
			}

			cache->active->alloc_num++;
			cache->regular_alloc_num++;
			return inner_base + inner_shift * memory_sizes[rank];
		}

		// Allocate a medium chunk and use it as an inner block.
		uint8_t *inner_base;
		block = cache->active->blocks[outer_rank];
		if (block != NULL) {
			// Use a cached block.
			ASSERT(block->chunk_free);
			const uint32_t shift = ctz(block->chunk_free);
			// Mark the medium chunk as an inner block.
			block->inner_used |= (1u << shift);
			block->inner_free |= (1u << shift);
			block->chunk_free ^= (1u << shift);
			if (block->chunk_free == 0) {
				// Remove a fully used block.
				cache->active->blocks[outer_rank] = block->next;
			}
			inner_base = (uint8_t *) block + shift * memory_sizes[outer_rank];
		} else {
			// Allocate a new block.
			block = alloc_outer(cache, outer_rank);
			if (unlikely(block == NULL))
				return NULL;
			// Mark the medium chunk as an inner block.
			block->inner_used |= 2;
			block->inner_free |= 2;
			inner_base = (uint8_t *) block + memory_sizes[outer_rank];
		}

		// Mark the remaining small chunks as free.
		((struct inner_block *) inner_base)->free = 0xfffc;

		// TODO: allocating a slice may take a span from the staging list with
		// existing blocks of the required size. Thus we allocated a slice for
		// no reason. Fix this.

		// Cache the block for futher use.
		block->inner_next = cache->active->blocks[rank];
		cache->active->blocks[rank] = block;

		cache->active->alloc_num++;
		cache->regular_alloc_num++;
		return inner_base + memory_sizes[rank];
	}
}

static void
free_chunk(struct slice_cache *const cache, struct slice_alloc_span *const span, void *const ptr)
{
	span->free_num++;
	cache->regular_free_num++;

	// Identify the chunk.
	const uint32_t base = deduce_base(span, ptr);
	VERIFY(base >= 4 && base < UNIT_NUMBER, "bad pointer");
	const uint8_t rank = span->units[base];
	const uint8_t mark = span->units[base + 1];
	VERIFY(rank >= CHUNK_RANKS && rank < CACHE_RANKS, "bad pointer");

	// Free a whole slice.
	if ((mark & ~UNIT_LMASK) != BASE_TAG) {
		VERIFY((mark & ~UNIT_LMASK) != NEXT_TAG, "double free");
		VERIFY(mark == 0, "bad pointer");
		free_slice(span, base, rank);
		return;
	}

	// Locate the outer block.
	const uint32_t outer_rank = rank - OUTER_TO_SLICE;
	struct outer_block *const block = (struct outer_block *) ((uint8_t *) span + base * UNIT_SIZE);
	const uint32_t shift = (((uint8_t *) ptr - (uint8_t *) block) * memory_magic[outer_rank]) >> MAGIC_SHIFT;
	VERIFY(shift > 0 || shift < 32, "bad pointer");

	// Free a chunk from the outer block.
	const uint32_t mask = 1u << shift;
	if ((block->inner_used & mask) == 0) {
		VERIFY((block->chunk_free & mask) == 0, "double free");
		if (block->chunk_free == 0) {
			block->next = span->blocks[outer_rank];
			span->blocks[outer_rank] = block;
		}
		block->chunk_free |= mask;
		return;
	}

	// Locate the inner block.
	const uint32_t inner_rank = outer_rank - INNER_TO_OUTER;
	struct inner_block *const inner = (struct inner_block *) ((uint8_t *) block + shift * memory_sizes[outer_rank]);
	const uint32_t inner_shift = (((uint8_t *) ptr - (uint8_t *) inner) * memory_magic[inner_rank]) >> MAGIC_SHIFT;
	VERIFY(inner_shift > 0 || inner_shift < 32, "bad pointer");

	// Free a chunk from the inner block.
	const uint32_t inner_mask = 1u << inner_shift;
	VERIFY((inner->free & inner_mask) == 0, "double free");
	inner->free |= inner_mask;
	if (inner->free != 0xfffe) {
		if (block->inner_free == 0) {
			block->inner_next = span->blocks[inner_rank];
			span->blocks[inner_rank] = block;
		}
		block->inner_free |= mask;
	} else {
		if (block->chunk_free == 0) {
			block->next = span->blocks[outer_rank];
			span->blocks[outer_rank] = block;
		}
		block->chunk_free |= mask;

		block->inner_used ^= mask;
		block->inner_free ^= mask;
		if (block->inner_free == 0) {
			struct outer_block *prev = span->blocks[inner_rank];
			if (prev == block) {
				span->blocks[inner_rank] = block->inner_next;
			} else {
				while (prev) {
					if (prev->inner_next == block) {
						prev->inner_next = block->inner_next;
						break;
					}
					prev = prev->inner_next;
				}
			}
		}
	}
}

static uint32_t
get_chunk_rank(const struct span_header *const hdr, const void *const ptr)
{
	// Identify the chunk.
	struct slice_alloc_span *const span = (struct slice_alloc_span *) hdr;
	const uint32_t base = deduce_base(span, ptr);
	const uint8_t rank = span->units[base];
	const uint8_t mark = span->units[base + 1];
	VERIFY(rank >= CHUNK_RANKS && rank < CACHE_RANKS, "bad pointer");
	VERIFY(mark == 0 || (mark & ~UNIT_LMASK) == BASE_TAG, "bad pointer");

	// Handle a whole slice.
	if (mark == 0)
		return rank;

	// Locate the outer block.
	const uint32_t outer_rank = rank - OUTER_TO_SLICE;
	struct outer_block *const block = (struct outer_block *) ((uint8_t *) span + base * UNIT_SIZE);
	const uint32_t shift = (((uint8_t *) ptr - (uint8_t *) block) * memory_magic[outer_rank]) >> MAGIC_SHIFT;
	VERIFY(shift > 0 || shift < 32, "bad pointer");

	// Handle a chunk from the outer block.
	const uint32_t mask = 1u << shift;
	if ((block->inner_used & mask) == 0)
		return outer_rank;

	// Handle a chunk from an inner block.
	return outer_rank - INNER_TO_OUTER;
}

static uint32_t
get_chunk_size(const struct span_header *const hdr, const void *const ptr)
{
	uint32_t rank = get_chunk_rank(hdr, ptr);
	return memory_sizes[rank];
}

/**********************************************************************
 * Slice cache management.
 **********************************************************************/

static void
handle_remote_free_list(struct slice_cache *const cache, struct slice_alloc_span *const span)
{
	for (;;) {
		struct mpsc_qlink *link = mpsc_queue_remove(&span->remote_free_list);
		if (link == NULL)
			break;
		free_chunk(cache, span, link);
	}
}

static bool
slice_cache_all_free(const struct slice_cache *const cache)
{
	if (cache->regular_alloc_num != cache->regular_free_num)
		return false;
	if (cache->singular_alloc_num != atomic_load_explicit(&cache->singular_free_num, memory_order_relaxed))
		return false;
	return true;
}

static void
slice_cache_collect_staging(struct slice_cache *const cache)
{
	struct slice_cache_node *node = list_head(&cache->staging);
	while (node != list_stub(&cache->staging)) {
		struct slice_alloc_span *span = containerof(node, struct slice_alloc_span, staging_node);
		struct slice_cache_node *next = node->next;
		handle_remote_free_list(cache, span);
		if (span->alloc_num == span->free_num) {
			list_delete(node);
			span_destroy(&span->header);
		}
		node = next;
	}
}

static void
slice_cache_release(struct slice_cache *const cache)
{
	if (cache->release_callback != NULL) {
		(cache->release_callback)(cache, cache->release_callback_data);
	}
}

static inline bool
is_valid_alignment(size_t alignment)
{
	if (!is_pow2z(alignment))
		return false;

	// Too large alignment value would defeat the logic that
	// finds the start of the span from a given pointer.
	if (alignment > (SPAN_ALIGNMENT / 2))
		return false;

	return true;
}

/**********************************************************************
 * Slice cache management - public API.
 **********************************************************************/

/* Pending cache release list. */
static struct slice_cache_list slice_cache_release_list = {
	.node = {
		.next = &slice_cache_release_list.node,
		.prev = &slice_cache_release_list.node,
	}
};

static spinlock_t slice_cache_release_list_lock = SPINLOCK_INIT;

void
slice_cache_prepare(struct slice_cache *const cache)
{
	list_prepare(&cache->staging);

	cache->active = (struct slice_alloc_span *) span_create_regular(cache);
	VERIFY(cache->active, "failed to create an initial memory span");
	prepare_span(cache->active);

	cache->regular_alloc_num = 0;
	cache->regular_free_num = 0;
	cache->singular_alloc_num = 0;
	cache->singular_free_num = 0;
}

void
slice_cache_cleanup(struct slice_cache *const cache, slice_cache_release_t cb, void *cb_data)
{
	// Store the release callback.
	cache->release_callback = cb;
	cache->release_callback_data = cb_data;

	// Move the active span to the staging list.
	if (cache->active != NULL) {
		list_insert_first(&cache->staging, &cache->active->staging_node);
		cache->active->status = SPAN_STAGING;
		cache->active = NULL;
	}

	// Try to free all the spans in the staging list.
	slice_cache_collect_staging(cache);
	if (slice_cache_all_free(cache)) {
		// If done then release the cache immediately.
		slice_cache_release(cache);
	} else {
		// If not then keep the cache around for a while.
		spin_lock(&slice_cache_release_list_lock);
		list_insert_first(&slice_cache_release_list, &cache->release_node);
		spin_unlock(&slice_cache_release_list_lock);
	}
}

void
slice_cache_collect(struct slice_cache *const cache)
{
	// Try to free some slices in the active span.
	handle_remote_free_list(cache, cache->active);

	// Try to free some spans in the staging list.
	slice_cache_collect_staging(cache);
}

void *
slice_cache_alloc(struct slice_cache *const cache, const size_t size)
{
	void *ptr;

	const uint32_t rank = get_rank(size);
	if (rank < CHUNK_RANKS) {
		// Handle small amd medium sizes.
		ptr = alloc_chunk(cache, rank);
	} else if (rank < CACHE_RANKS) {
		// Handle large sizes.
		ptr = alloc_slice(cache, rank, false);
	} else {
		// Handle super-large sizes.
		struct span_header *hdr = span_create_singular(cache, size, ALIGNMENT);
		if (unlikely(hdr == NULL)) {
			errno = ENOMEM;
			return NULL;
		}

		cache->singular_alloc_num++;
		return span_singular_data(hdr);
	}

	if (unlikely(ptr == NULL))
		errno = ENOMEM;
	return ptr;
}

void *
slice_cache_zalloc(struct slice_cache *const cache, const size_t size)
{
	void *ptr;

	const uint32_t rank = get_rank(size);
	if (rank < CHUNK_RANKS) {
		// Handle small amd medium sizes.
		ptr = alloc_chunk(cache, rank);
	} else if (rank < CACHE_RANKS) {
		// Handle large sizes.
		ptr = alloc_slice(cache, rank, false);
	} else {
		// Handle super-large sizes.
		struct span_header *hdr = span_create_singular(cache, size, ALIGNMENT);
		if (unlikely(hdr == NULL)) {
			errno = ENOMEM;
			return NULL;
		}

		cache->singular_alloc_num++;
		return span_singular_data(hdr);
	}

	if (unlikely(ptr == NULL)) {
		errno = ENOMEM;
		return NULL;
	}

	memset(ptr, 0, size);
	return ptr;
}

void *
slice_cache_calloc(struct slice_cache *const cache, const size_t num, const size_t size)
{
	size_t total;
	if(__builtin_mul_overflow(num, size, &total)) {
		errno = EOVERFLOW;
		return NULL;
	}
	return slice_cache_zalloc(cache, total);
}

void *
slice_cache_aligned_alloc(struct slice_cache *const cache, const size_t alignment, const size_t size)
{
	if (!is_valid_alignment(alignment)) {
		errno = EINVAL;
		return NULL;
	}

	// Try to use natural alignment of chunks.
	const uint32_t rank = get_rank(size);
	if (rank < CHUNK_RANKS) {
		// Handle small amd medium sizes.
		size_t alloc_align;
		switch ((rank & 3)) {
		case 0:
			alloc_align = memory_sizes[rank];
			break;
		case 1:
			alloc_align = memory_sizes[rank - 1] / 4;
			break;
		case 2:
			alloc_align = memory_sizes[rank - 2] / 2;
			break;
		case 3:
			alloc_align = memory_sizes[rank - 3] / 4;
			break;
		}
		if (alignment <= alloc_align) {
			return alloc_chunk(cache, rank);
		}
	} else if (rank < CACHE_RANKS) {
		// Handle large sizes.
		if (alignment <= UNIT_SIZE) {
			// All slices are UNIT_SIZE-aligned.
			return alloc_slice(cache, rank, false);
		}
	} else {
		// Handle super-large sizes.
		struct span_header *hdr = span_create_singular(cache, size,
							       max(alignment, ALIGNMENT));
		if (unlikely(hdr == NULL)) {
			errno = ENOMEM;
			return NULL;
		}

		cache->singular_alloc_num++;
		return span_singular_data(hdr);
	}

	// Fall back to allocating a larger chunk and aligning within it.
	// TODO: extend the unit map for large slices with large alignment
	// to be able to free them with pointers shifted by alignment.
	const size_t align_mask = alignment - 1;
	void *const ptr = slice_cache_alloc(cache, size + align_mask);
	return (void *) ((((uintptr_t) ptr) + align_mask) & ~align_mask);
}

void *
slice_cache_realloc(struct slice_cache *const cache, void *const ptr, const size_t size)
{
	if (ptr == NULL) {
		return slice_cache_alloc(cache, size);
	} else if (size == 0) {
		slice_cache_free(cache, ptr);
		return NULL;
	}

	struct span_header *const hdr = span_from_ptr(ptr);
	ASSERT(cache == hdr->cache);

	// Try to reuse the original chunk.
	size_t old_size;
	if (span_is_singular(hdr)) {
		// Handle super-large chunks.
		old_size = span_singular_size(hdr);
		const struct singular_span_params params = span_compute_singular(size, ALIGNMENT);
		if (old_size == (params.virtual_size - params.offset))
			return ptr;
		// TODO: use munmap to shorten singular spans.
	} else {
		// Handle chunks from regular spans.
		const uint32_t old_rank = get_chunk_rank(hdr, ptr);
		const uint32_t rank = get_rank(size);
		if (old_rank == rank)
			return ptr;
		old_size = memory_sizes[old_rank];
	}

	// Allocate a new chunk.
	void *new_ptr = slice_cache_alloc(cache, size);
	if (new_ptr == NULL)
		return NULL;

	memcpy(new_ptr, ptr, min(old_size, size));
	slice_cache_free(cache, ptr);

	return new_ptr;
}

void
slice_cache_free(struct slice_cache *const cache, void *const ptr)
{
	if (ptr == NULL)
		return;

	struct span_header *const hdr = span_from_ptr(ptr);
	ASSERT(cache == hdr->cache);

	if (span_is_singular(hdr)) {
		// Free super-large chunks.
		atomic_fetch_add_explicit(&cache->singular_free_num, 1, memory_order_relaxed);
		span_destroy(hdr);
		return;
	}

	// Free chunks from regular spans.
	struct slice_alloc_span *const span = (struct slice_alloc_span *) hdr;
	free_chunk(cache, span, ptr);
}

void
slice_cache_free_maybe_remotely(struct slice_cache *const local_cache, void *const ptr)
{
	if (ptr == NULL)
		return;

	struct span_header *const hdr = span_from_ptr(ptr);

	if (span_is_singular(hdr)) {
		// Free super-large chunks.
		atomic_fetch_add_explicit(&hdr->cache->singular_free_num, 1, memory_order_relaxed);
		span_destroy(hdr);
		return;
	}

	// Free chunks from regular spans.
	struct slice_alloc_span *const span = (struct slice_alloc_span *) hdr;
	if (hdr->cache == local_cache) {
		// Nice, this is a local free actually.
		free_chunk(local_cache, span, ptr);
	} else {
		// Well, this is really a remote free.
		struct mpsc_qlink *const link = ptr;
		mpsc_qlink_prepare(link);
		mpsc_queue_append(&span->remote_free_list, link);
	}
}

/**********************************************************************
 * Common functions - public API.
 **********************************************************************/

void
slice_scrap_collect(void)
{
	struct slice_cache_list list;
	list_prepare(&list);

	if (spin_try_lock(&slice_cache_release_list_lock)) {
		if (!list_empty(&slice_cache_release_list)) {
			list_splice_first(&list,
					  list_head(&slice_cache_release_list),
					  list_tail(&slice_cache_release_list));
			list_prepare(&slice_cache_release_list);
		}
		spin_unlock(&slice_cache_release_list_lock);

		struct slice_cache_node *node = list_head(&list);
		while (node != list_stub(&list)) {
			struct slice_cache *cache = containerof(node, struct slice_cache, release_node);
			struct slice_cache_node *next = node->next;
			slice_cache_collect_staging(cache);
			if (slice_cache_all_free(cache)) {
				list_delete(node);
				slice_cache_release(cache);
			}
			node = next;
		}

		if (!list_empty(&list)) {
			spin_lock(&slice_cache_release_list_lock);
			list_splice_first(&slice_cache_release_list,
					  list_head(&list),
					  list_tail(&list));
			spin_unlock(&slice_cache_release_list_lock);
		}
	}
}

size_t
slice_usable_size(const void *const ptr)
{
	if (ptr == NULL)
		return 0;

	const struct span_header *const hdr = span_from_ptr(ptr);
	if (span_is_singular(hdr)) {
		// Handle a super-large chunk.
		return span_singular_size(hdr);
	}

	// Handle a chunk in a regular span.
	return get_chunk_size(hdr, ptr);
}

/**********************************************************************
 * Thread-specific memory management - public API.
 **********************************************************************/

// Thread-local cache.
static __thread struct slice_cache *local_cache = NULL;

// This is used for thread-local cache cleanup.
static pthread_key_t local_cache_key;
static pthread_once_t local_cache_once = PTHREAD_ONCE_INIT;

// Initial cache used for bootstrapping.
static struct slice_cache initial_cache;

static void
release_local_cache(struct slice_cache *cache, void *data __attribute__((unused)))
{
	if (cache != &initial_cache) {
		slice_cache_free(&initial_cache, cache);
	} else {
		pthread_key_delete(local_cache_key);
	}
	slice_scrap_collect();
}

static void
destroy_initial_cache(void)
{
	slice_cache_cleanup(&initial_cache, release_local_cache, NULL);
}

static void
destroy_local_cache(void *ptr)
{
	slice_cache_cleanup((struct slice_cache *) ptr, release_local_cache, NULL);
}

static void
prepare_local_cache(void)
{
	// Create initial cache.
	slice_cache_prepare(&initial_cache);
	local_cache = &initial_cache;

	// Create the key needed for cleanup on thread exit.
	pthread_key_create(&local_cache_key, destroy_local_cache);

	// Register for cleanup on process exit.
	atexit(destroy_initial_cache);
}

static struct slice_cache *
get_local_cache(void)
{
	struct slice_cache *cache = local_cache;
	if (unlikely(cache == NULL)) {
		// Initialize local cache global data if needed.
		pthread_once(&local_cache_once, prepare_local_cache);

		// Create a new cache unless the slice_cache_boot cache has
		// just been initialized in this thread.
		cache = local_cache;
		if (likely(cache == NULL)) {
			cache = slice_cache_alloc(&initial_cache, sizeof(struct slice_cache));
			if (cache == NULL)
				return NULL;
			slice_cache_prepare(cache);
			local_cache = cache;

			// This is only for cleanup. We don't use pthread_getspecific().
			pthread_setspecific(local_cache_key, cache);
		}
	}
	return cache;
}

void
slice_local_collect(void)
{
	struct slice_cache *cache = get_local_cache();
	if (unlikely(cache == NULL)) {
		errno = ENOMEM;
		return;
	}
	slice_cache_collect(cache);
}

void *
slice_alloc(const size_t size)
{
	struct slice_cache *cache = get_local_cache();
	if (unlikely(cache == NULL)) {
		errno = ENOMEM;
		return NULL;
	}
	return slice_cache_alloc(cache, size);
}

void *
slice_zalloc(const size_t size)
{
	struct slice_cache *cache = get_local_cache();
	if (unlikely(cache == NULL)) {
		errno = ENOMEM;
		return NULL;
	}
	return slice_cache_zalloc(cache, size);
}

void *
slice_calloc(const size_t num, const size_t size)
{
	struct slice_cache *cache = get_local_cache();
	if (unlikely(cache == NULL)) {
		errno = ENOMEM;
		return NULL;
	}
	return slice_cache_calloc(cache, num, size);
}

void *
slice_aligned_alloc(const size_t alignment, const size_t size)
{
	struct slice_cache *cache = get_local_cache();
	if (unlikely(cache == NULL)) {
		errno = ENOMEM;
		return NULL;
	}
	return slice_cache_aligned_alloc(cache, alignment, size);
}

void *
slice_realloc(void *const ptr, const size_t size)
{
	struct slice_cache *cache = get_local_cache();
	if (unlikely(cache == NULL)) {
		errno = ENOMEM;
		return NULL;
	}
	return slice_cache_realloc(cache, ptr, size);
}

void
slice_free(void *const ptr)
{
	slice_cache_free_maybe_remotely(local_cache, ptr);
}

/**********************************************************************
 * Overrides of libc functions.
 **********************************************************************/

#define ALIAS(name) __attribute__((alias(#name), used, visibility("default")))

void *malloc(size_t size) ALIAS(slice_alloc);
void *calloc(size_t num, size_t size) ALIAS(slice_calloc);
void *realloc(void *ptr, size_t size) ALIAS(slice_realloc);
void *aligned_alloc(size_t alignment, size_t size) ALIAS(slice_aligned_alloc);
void *memalign(size_t alignment, size_t size) ALIAS(slice_aligned_alloc);
void free(void *ptr) ALIAS(slice_free);

size_t malloc_usable_size(void *const ptr) ALIAS(slice_usable_size);

int
posix_memalign(void **pptr, size_t alignment, size_t size)
{
	if (pptr == NULL || !is_valid_alignment(alignment))
		return EINVAL;

	struct slice_cache *cache = get_local_cache();
	if (unlikely(cache == NULL))
		return ENOMEM;

	void *ptr = slice_cache_aligned_alloc(cache, alignment, size);
	if (ptr == NULL)
		return ENOMEM;

	*pptr = ptr;
	return 0;
}

void *
valloc(size_t size)
{
	return slice_aligned_alloc(PAGE_SIZE, size);
}

void *
pvalloc(size_t size)
{
	size = (size + PAGE_SIZE - 1) & ~(PAGE_SIZE - 1);
	return slice_aligned_alloc(PAGE_SIZE, size);
}
