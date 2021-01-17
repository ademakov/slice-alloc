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

#define TRACE 0
#define CHECK_LEVEL 0

#if TRACE
#include <stdio.h>
#endif

/**********************************************************************
 * Common macros.
 **********************************************************************/

// Minimum alignment.
#define ALIGNMENT		(16)
// Virtual memory page size.
#define PAGE_SIZE		(4096)

#define likely(x)		__builtin_expect(!!(x), 1)
#define unlikely(x)		__builtin_expect(!!(x), 0)

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

#if CHECK_LEVEL > 1
# define ASSERT(e)	(likely(e) ? (void) 0 : panic("panic: " LOCATION ": assertion failed\n"))
#else
# define ASSERT(e)	((void) (e))
#endif
#if CHECK_LEVEL > 0
# define VERIFY(e, msg)	(likely(e) ? (void) 0 : panic("panic: " LOCATION ": " msg "\n"))
#else
# define VERIFY(e, msg)	((void) (e))
#endif

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

typedef SLICE_CACHE_ALIGN struct
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

static inline void
mpsc_qlink_prepare(struct slice_cache_mpsc_node *link)
{
	atomic_init(&link->next, NULL);
}

static inline void
mpsc_queue_prepare(struct slice_cache_mpsc_queue *list)
{
	list->head = &list->stub;
	atomic_init(&list->tail, &list->stub);
	mpsc_qlink_prepare(&list->stub);
}

static inline void
mpsc_queue_append_span(struct slice_cache_mpsc_queue *list,
		       struct slice_cache_mpsc_node *head,
		       struct slice_cache_mpsc_node *tail)
{
	struct slice_cache_mpsc_node *prev = atomic_exchange(&list->tail, tail);
	atomic_store_explicit(&prev->next, head, memory_order_release);
}

static inline void
mpsc_queue_append(struct slice_cache_mpsc_queue *list,
		  struct slice_cache_mpsc_node *link)
{
	mpsc_queue_append_span(list, link, link);
}

static struct slice_cache_mpsc_node *
mpsc_queue_remove(struct slice_cache_mpsc_queue *list)
{
	struct slice_cache_mpsc_node *head = list->head;
	struct slice_cache_mpsc_node *next = atomic_load_explicit(&head->next, memory_order_acquire);
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

	struct slice_cache_mpsc_node *tail = atomic_load_explicit(&list->tail, memory_order_acquire);
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

#if TRACE
		void *addr0 = addr;
#endif

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

#if TRACE
		printf("mmap %zx (%p) %zx %p %p %zx %zx\n", size, addr0, upsized_size, upsized_addr, addr, leading_size, trailing_size);
	} else {
		printf("mmap %zx %p\n", size, addr);
#endif
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

/*
  Chunk Ranks
  ===========

  row | msb | 0            | 1            | 2            | 3            |
 -----+-----+--------------+--------------+--------------+--------------+--------------
   0  |  -  |       8 (0)  |      16 (1)  |      32 (2)  |      48 (3)  | SMALL SIZES
 -----+-----+--------------+--------------+--------------+-----------------------------
   1  |  6  |      64 (4)  |      80 (5)  |      96 (6)  |     112 (7)  | MEDIUM SIZES
   2  |  7  |     128 (8)  |     160 (9)  |     192 (10) |     224 (11) |
   3  |  8  |     256 (12) |     320 (13) |     384 (14) |     448 (15) |
   4  |  9  |     512 (16) |     640 (17) |     768 (18) |     896 (19) |
   5  | 10  |    1024 (20) |    1280 (21) |    1536 (22) |    1792 (23) |
   6  | 11  |    2048 (24) |    2560 (25) |    3072 (26) |    3584 (27) |
 -----+-----+--------------+--------------+--------------+--------------+--------------
   7  | 12  |    4096 (28) |    5120 (29) |    6144 (30) |    7168 (31) | LARGE SIZES
   8  | 13  |    8192 (32) |   10240 (23) |   12288 (34) |   14336 (35) |
   9  | 14  |   16384 (36) |   20480 (37) |   24576 (38) |   28672 (39) |
  10  | 15  |   32768 (40) |   40960 (41) |   49152 (42) |   57344 (43) |
  11  | 16  |   65536 (44) |   81920 (45) |   98304 (46) |  114688 (47) |
  12  | 17  |  131072 (48) |  163840 (49) |  196608 (50) |  229376 (51) |
  13  | 18  |  262144 (52) |  327680 (53) |  393216 (54) |  458752 (55) |
  14  | 19  |  524288 (56) |  655360 (57) |  786432 (58) |  917504 (59) |
  15  | 20  | 1048576 (60) | 1310720 (61) | 1572864 (62) | 1835008 (63) |
 -----+-----+--------------+--------------+--------------+--------------+--------------
  16  | 21  | 2097152 (64)  ...                                         | SUPER SIZES


  Unit Map Encoding
  =================

  byte 0
  ------
  chunk rank:
    value >= 0x00 --   0 -- 0 0 0 0 | 0 0 0 0
    value <= 0x3f --  63 -- 0 0 1 1 | 1 1 1 1
    0 0 x x | x x x x

  byte 1
  ------
  for a used slice -- base of itself, lo 6 bits
    value >= 0x40 --  64 -- 0 1  0 0 | 0 0 0 0
    value <= 0x7f -- 127 -- 0 1  1 1 | 1 1 1 1
    0 1 x x | x x x x
  [ for blocks also repeated at bytes 3, 5, ... ]

  for a free slice
    value == 0xfe -- 254
    1 1 1 1 | 1 1 1 0

  byte 2
  ------
  for a used slice -- base of itself, hi 5 bits
    value >= 0x80 -- 128 -- 1 0 0 0 | 0 0 0 0
    value <= 0x9f -- 159 -- 1 0 0 1 | 1 1 1 1
    1 0 x x | x x x x
  [ for blocks also repeated at bytes 4, 6, ... ]

  for a free slice
    value == 0xff -- 255
    1 1 1 1 | 1 1 1 1

*/

typedef enum
{
	SPAN_ACTIVE = 0,
	SPAN_STAGING = 1
} span_status_t;

// The number of chunk ranks. 
#define SMALL_RANKS		(4u)
#define MEDIUM_RANKS		(24u)
#define SLICE_RANKS		(36u)
#define BLOCK_RANKS		(SMALL_RANKS + MEDIUM_RANKS)
#define CACHE_RANKS		(BLOCK_RANKS + SLICE_RANKS)

// The number of ranks that are allocated by halving.
#define BUDDY_RANKS		(SLICE_RANKS - 12u)

// Sizes of the memory map units in a regular span.
#define HEAD_SIZE		(4096u)
#define UNIT_SIZE		(1024u)
#define UNIT_NUMBER		(2048u)

// Constants used for encoding of chunk ranks.
#define UNIT_LBITS		(6u)
#define UNIT_HBITS		(5u)
#define UNIT_LMASK		((1u << UNIT_LBITS) - 1u)
#define UNIT_HMASK		((1u << UNIT_HBITS) - 1u)

#define BASE_LFLAG		(4u << 4u)
#define BASE_HFLAG		(8u << 4u)
#define BASE_STUB3		(10u << 4u)
#define BASE_STUB4		(11u << 4u)
#define BASE_STUB5		(12u << 4u)
#define BASE_STUB6		(13u << 4u)

#define FREE_TAG1		(254u)
#define FREE_TAG2		(255u)

#define FIRST_ROW(_)		_(3u, 0u), _(4u, 0u), _(5u, 0u), _(5u, 2u)
#define OTHER_ROW(r, _)		_(r, 0u), _(r, 1u), _(r, 2u), _(r, 3u)
#define BLOCK_ROWS(_)		\
	OTHER_ROW(6u, _),	\
	OTHER_ROW(7u, _),	\
	OTHER_ROW(8u, _),	\
	OTHER_ROW(9u, _),	\
	OTHER_ROW(10u, _),	\
	OTHER_ROW(11u, _)
#define SLICE_ROWS(_)		\
	OTHER_ROW(12u, _),	\
	OTHER_ROW(13u, _),	\
	OTHER_ROW(14u, _),	\
	OTHER_ROW(15u, _),	\
	OTHER_ROW(16u, _),	\
	OTHER_ROW(17u, _),	\
	OTHER_ROW(18u, _),	\
	OTHER_ROW(19u, _),	\
	OTHER_ROW(20u, _)

// Header for a block of small or medium chunks.
struct block
{
	void *free_list;
	uint32_t free_num;
	uint32_t free_max;
	struct slice_cache_node node;
};

// Regular span header.
struct slice_alloc_span
{
	struct span_header header;

	struct slice_cache_node staging_node;
	span_status_t status;

	uint32_t slice_num;
	uint32_t block_num;

	// Cached blocks and slices.
	struct slice_cache_list blocks[BLOCK_RANKS];
	void *slices[SLICE_RANKS];

	// The map of units.
	uint8_t units[UNIT_NUMBER];
};

#define RANK_SIZE(r, m)		((4u | (m)) << ((r) - 2u))
#define SMALL_SLICE(r, m)	(((r) + 4u) * 4u + (m))
#define MEDIUM_SLICE(r, m)	(((r) + 1u) * 4u + (m))
#define SMALL_BLOCK_SIZE(r, m)	(512u)
#define MEDIUM_BLOCK_SIZE(r, m)	(64u)
#define BLOCK_USED(r, m)	((RANK_SIZE(r, m) + sizeof(struct block) - 1) / RANK_SIZE(r, m))

// Memory rank sizes.
static const uint32_t memory_sizes[] = {
	FIRST_ROW(RANK_SIZE),
	BLOCK_ROWS(RANK_SIZE),
	SLICE_ROWS(RANK_SIZE),
};

static const uint32_t block_slice[] = {
	FIRST_ROW(SMALL_SLICE),
	BLOCK_ROWS(MEDIUM_SLICE),
};

static const uint32_t block_size[] = {
	FIRST_ROW(SMALL_BLOCK_SIZE),
	BLOCK_ROWS(MEDIUM_BLOCK_SIZE),
};

static const uint32_t block_used[] = {
	FIRST_ROW(BLOCK_USED),
	BLOCK_ROWS(BLOCK_USED),
};

static inline uint32_t
get_rank(size_t size)
{
	if (size-- <= 8)
		return 0;
	if (size < 128)
		return (size + 16) >> 4;

	// Search for most significant set bit, on x86 this should translate
	// to a single BSR instruction.
	const uint32_t msb = clz(size) ^ (nbits(size) - 1);

	// Calcualte the rank.
	return (msb << 2u) + (size >> (msb - 2u)) - 23u;
}

static inline uint32_t
unit_from_ptr(const struct slice_alloc_span *const span, const void *ptr)
{
#if 0
	return ((uintptr_t) ptr & SPAN_ALIGNMENT_MASK) / UNIT_SIZE;
#else
	return ((uintptr_t) ptr - (uintptr_t) span) / UNIT_SIZE;
#endif
}

static inline uint32_t
find_slice_info(const struct slice_alloc_span *const span, const uint32_t unit)
{
	const uint8_t index = span->units[unit] >> 4u;
	VERIFY(index < 14u, "bad pointer");

	static uint8_t table[] = {
		0, 0, 0, 0,
		1, 1, 1, 1,
		2, 2, 3, 4,
		5, 6, 7, 8
	};

	return unit - table[index];
}

static inline uint32_t
get_slice_rank(const struct slice_alloc_span *const span, const uint32_t unit)
{
	return span->units[unit];
}

static inline uint32_t
get_slice_base(const struct slice_alloc_span *const span, const uint32_t unit)
{
	const uint32_t lo = span->units[unit + 1] & UNIT_LMASK;
	const uint32_t hi = span->units[unit + 2] & UNIT_HMASK;
	return lo | (hi << UNIT_LBITS);
}

static void
free_slice(struct slice_alloc_span *const span, const uint32_t base, const uint32_t rank)
{
	ASSERT(rank >= BLOCK_RANKS);

	void *const ptr = (uint8_t *) span + base * UNIT_SIZE;
	const uint32_t index = rank - BLOCK_RANKS;
	*((void **) ptr) = span->slices[index];
	span->slices[index] = ptr;

	span->units[base + 1] = FREE_TAG1;
	span->units[base + 2] = FREE_TAG2;
}

static uint32_t
find_slice(const struct slice_alloc_span *const span, uint32_t rank)
{
	ASSERT(rank >= BLOCK_RANKS && rank < CACHE_RANKS);

	while (rank < (BLOCK_RANKS + BUDDY_RANKS)) {
		if (span->slices[rank - BLOCK_RANKS])
			return rank;
		rank += 4;
	}
	while (rank < CACHE_RANKS) {
		if (span->slices[rank - BLOCK_RANKS])
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
split_slice(struct slice_alloc_span *const span, uint32_t base, uint32_t rank, const uint32_t original_rank)
{
	// Here the rank value is adjusted to large-only sizes.
	ASSERT(original_rank > BLOCK_RANKS && original_rank <= CACHE_RANKS);
	ASSERT(rank >= BLOCK_RANKS && rank < CACHE_RANKS);
	ASSERT(rank < original_rank);

	// Cut off the extra space from it slice-by-slice with doubling
	// slice sizes:
	//
	//    +-------------------- <original slice>
	//    |
	//    V
	//   [..............................]
	//
	//    +-------------------- <required slice>
	//    |   +---------------- <extra slices>
	//    |   |
	//    V   V
	//   [..][..][......][..............]
	//
	base += memory_sizes[rank] / UNIT_SIZE;
	while (rank < (BLOCK_RANKS + BUDDY_RANKS)) {
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
	span->block_num = 0;
	span->slice_num = 0;

	for (uint32_t i = 0; i < SLICE_RANKS; i++)
		span->slices[i] = 0;

	memset(span->units, 0, sizeof span->units);
#endif

	for (uint32_t i = 0; i < BLOCK_RANKS; i++)
		list_prepare(&span->blocks[i]);

	// The initial heap layout takes out the very first 4KiB slice
	// from the span. It is used up for the very span header that is
	// initialized here.
	split_slice(span, 0, BLOCK_RANKS, CACHE_RANKS);
	span->units[0] = BLOCK_RANKS;
}

static void
coalesce_chunks(struct slice_alloc_span *const span)
{
	// Convert empty blocks to slices.
	for (uint32_t rank = 0; rank < BLOCK_RANKS; rank++) {
		struct slice_cache_node *node = list_head(&span->blocks[rank]);
		while (node != list_stub(&span->blocks[rank])) {
			struct block *block = containerof(node, struct block, node);
			struct slice_cache_node *next = node->next;
			if (block->free_num == block->free_max) {
				const uint32_t base = unit_from_ptr(span, block);
				span->units[base] = block_slice[rank];
				list_delete(&block->node);
				span->block_num--;
			}
			node = next;
		}
	}

	// TODO: coalesce free slices
}

static inline void
free_chunk(struct slice_alloc_span *const span, void *const ptr)
{
	// Identify the chunk.
	const uint32_t unit = unit_from_ptr(span, ptr);
	const uint32_t info = find_slice_info(span, unit);
	const uint32_t rank = get_slice_rank(span, info);
	VERIFY(rank < CACHE_RANKS, "bad pointer");
	const uint32_t base = get_slice_base(span, info);
	VERIFY(base >= 4 && base < UNIT_NUMBER, "bad pointer");
	VERIFY(span->units[base + 1] != FREE_TAG1, "double free");

	if (rank >= BLOCK_RANKS) {
		// Free a whole slice.
		span->slice_num--;
		free_slice(span, base, rank);
	} else {
		// Free a chunk from a block.
		VERIFY(span->block_num > 0, "bad pointer");
		struct block *const block = (struct block *) ((uint8_t *) span + base * UNIT_SIZE);
		VERIFY(block->free_num < block->free_max, "double free");

		// If the block was empty it becomes usable again.
		if (block->free_num++ == 0)
			list_insert_first(&span->blocks[rank], &block->node);

		// Add the chunk to the free list.
		*((void **) ptr) = block->free_list;
		block->free_list = ptr;
	}
}

static void
release_remote(struct slice_cache *const cache)
{
	for (;;) {
		void *ptr = mpsc_queue_remove(&cache->remote_free_list);
		if (ptr == NULL)
			break;

		struct span_header *const hdr = span_from_ptr(ptr);
		ASSERT(span_is_regular(hdr));
		ASSERT(cache == hdr->cache);

		free_chunk((struct slice_alloc_span *) hdr, ptr);
	}
}

static void *
alloc_slice(struct slice_cache *const cache, const uint32_t chunk_rank)
{
	ASSERT(chunk_rank < CACHE_RANKS);

	struct slice_alloc_span *span = cache->active;
	const uint32_t rank = chunk_rank >= BLOCK_RANKS ? chunk_rank : block_slice[chunk_rank];
	uint32_t original_rank = find_slice(span, rank);
	if (original_rank >= CACHE_RANKS) {
		release_remote(cache);
		coalesce_chunks(span);
		original_rank = find_slice(span, rank);
	}

	if (original_rank >= CACHE_RANKS) {
		span = NULL;

		// Try to find a suitable span in the staging list.
		struct slice_cache_node *node = list_head(&cache->staging);
		while (node != list_stub(&cache->staging)) {
			struct slice_alloc_span *next = containerof(node, struct slice_alloc_span, staging_node);
			original_rank = find_slice(next, rank);
			if (original_rank >= CACHE_RANKS) {
				coalesce_chunks(next);
				original_rank = find_slice(next, rank);
			}
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
			original_rank = find_slice(span, rank);
			ASSERT(original_rank < CACHE_RANKS);
		}

		cache->active->status = SPAN_STAGING;
		list_insert_first(&cache->staging, &cache->active->staging_node);
		cache->active = span;
	}

	// Remove the slice from the free list.
	void *const ptr = span->slices[original_rank - BLOCK_RANKS];
	span->slices[original_rank - BLOCK_RANKS] = *((void **) ptr);

	const uint32_t base = unit_from_ptr(span, ptr);

	// If the slice is bigger than required then split it.
	if (rank != original_rank)
		split_slice(span, base, rank, original_rank);

	// Make the unit map pattern.
	const uint8_t pattern[4] = {
		chunk_rank,
		(base & UNIT_LMASK) + BASE_LFLAG,
		(base >> UNIT_LBITS) + BASE_HFLAG,
		BASE_STUB3
	};

	uint8_t *map = &span->units[base];
	if (chunk_rank >= BLOCK_RANKS) {
		// The slice is to be used as such.
		span->slice_num++;

		// Fill the unit map at the start only.
		memcpy(map, pattern, 4);

	} else {
		// The slice is to be used as a block.
		span->block_num++;

		// Fill the unit map for the whole slice.
		uint32_t num = memory_sizes[rank] / UNIT_SIZE;
		while (num >= 4) {
			memcpy(map, pattern, 4);
			map += 4;
			num -= 4;
		}
		if (num > 0) {
			static uint8_t tail[] = {
				BASE_STUB4, BASE_STUB5, BASE_STUB6
			};
			memcpy(map, tail, num);
		}
	}

	return ptr;
}

static struct block *
alloc_block(struct slice_cache *const cache, const uint32_t rank)
{
	// TODO: allocating a slice may take a span from the staging list with
	// existing blocks of the required size. Thus we allocated a slice for
	// no reason. Fix this.

	// Allocate a large chunk.
	struct block *const block = alloc_slice(cache, rank);
	if (unlikely(block == NULL))
		return NULL;

	// Cache the block for futher use.
	list_insert_first(&cache->active->blocks[rank], &block->node);

	// Total number of slots.
	const uint32_t size = block_size[rank];
	// Slots used for 'struct block'.
	const uint32_t used = block_used[rank];
	block->free_num = block->free_max = size - used;

	// Fill the free list.
	const uint32_t step = memory_sizes[rank];
	uint8_t *ptr = (uint8_t *) block + used * step;
	uint8_t *const end = (uint8_t *) block + size * step;
	block->free_list = ptr;
	for (;;) {
		uint8_t *const next = ptr + step;
		if (next == end) {
			*((void **) ptr) = NULL;
			break;
		}
		*((void **) ptr) = next;
		ptr = next;
	}

	return block;
}

static inline void *
alloc_chunk(struct slice_cache *const cache, const uint32_t rank)
{
	if (rank >= BLOCK_RANKS)
		return alloc_slice(cache, rank);

	struct block *block;
	struct slice_alloc_span *span = cache->active;
	if (!list_empty(&span->blocks[rank])) {
		// Use a cached block.
		struct slice_cache_node *node = list_head(&span->blocks[rank]);
		block = containerof(node, struct block, node);
	} else {
		// Allocate a new block.
		block = alloc_block(cache, rank);
		if (unlikely(block == NULL))
			return NULL;
	}

	// Get a chunk from the free list.
	void *ptr = block->free_list;
	block->free_list = *((void **) ptr);

	// If the block becomes empty delete it from the cache.
	if (--(block->free_num) == 0)
		list_delete(&block->node);

	return ptr;
}

static inline uint32_t
get_chunk_rank(const struct span_header *const hdr, const void *const ptr)
{
	struct slice_alloc_span *const span = (struct slice_alloc_span *) hdr;
	const uint32_t unit = unit_from_ptr(span, ptr);
	const uint32_t info = find_slice_info(span, unit);
	VERIFY(info >= 4 && info < UNIT_NUMBER, "bad pointer");
	const uint32_t rank = get_slice_rank(span, info);
	VERIFY(rank < CACHE_RANKS, "bad pointer");
	return rank;
}

static inline uint32_t
get_chunk_size(const struct span_header *const hdr, const void *const ptr)
{
	uint32_t rank = get_chunk_rank(hdr, ptr);
	return memory_sizes[rank];
}

/**********************************************************************
 * Slice cache management.
 **********************************************************************/

static bool
slice_cache_all_free(struct slice_cache *const cache)
{
	struct slice_cache_node *node = list_head(&cache->staging);
	while (node != list_stub(&cache->staging)) {
		struct slice_alloc_span *span = containerof(node, struct slice_alloc_span, staging_node);
		if ((span->slice_num + span->block_num) != 0)
			return false;
		node = node->next;
	}

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
		if (span->block_num != 0)
			coalesce_chunks(span);
		if ((span->slice_num + span->block_num) == 0) {
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
is_valid_alignment(const size_t alignment)
{
	if (!is_pow2z(alignment))
		return false;

	// Too large alignment value would defeat the logic that
	// finds the start of the span from a given pointer.
	if (alignment > (SPAN_ALIGNMENT / 2))
		return false;

	return true;
}

static size_t
chunk_alignment(const uint32_t rank)
{
	if (rank < BLOCK_RANKS) {
		switch ((rank & 3)) {
		case 0:
			return memory_sizes[rank];
		case 1:
			return memory_sizes[rank - 1] / 4;
		case 2:
			return memory_sizes[rank - 2] / 2;
		case 3:
			return memory_sizes[rank - 3] / 4;
		}
	}
	return UNIT_SIZE;
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

	// Initialize the remote free list.
	mpsc_queue_prepare(&cache->remote_free_list);

	cache->active = (struct slice_alloc_span *) span_create_regular(cache);
	VERIFY(cache->active, "failed to create an initial memory span");
	prepare_span(cache->active);

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
	// Check for remotely freed chunks.
	release_remote(cache);

	// Try to free some spans in the staging list.
	slice_cache_collect_staging(cache);
}

inline void *
slice_cache_alloc(struct slice_cache *const cache, const size_t size)
{
	const uint32_t rank = get_rank(size);
	if (rank < CACHE_RANKS) {
		// Handle small, medium, and large sizes.
		void *ptr = alloc_chunk(cache, rank);
		if (unlikely(ptr == NULL))
			errno = ENOMEM;
		return ptr;
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
}

void *
slice_cache_zalloc(struct slice_cache *const cache, const size_t size)
{
	const uint32_t rank = get_rank(size);
	if (rank < CACHE_RANKS) {
		// Handle small, medium, and large sizes.
		void *ptr = alloc_chunk(cache, rank);
		if (unlikely(ptr == NULL))
			errno = ENOMEM;
		else
			memset(ptr, 0, memory_sizes[rank]);
		return ptr;
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
	if (rank < CACHE_RANKS) {
		// Handle small, medium, and large sizes.
		if (alignment <= chunk_alignment(rank)) {
			void *ptr = alloc_chunk(cache, rank);
			if (unlikely(ptr == NULL))
				errno = ENOMEM;
			return ptr;
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
	if (ptr == NULL)
		return ptr;
	return (void *) ((((uintptr_t) ptr) + align_mask) & ~align_mask);
}

void *
slice_cache_aligned_zalloc(struct slice_cache *const cache, const size_t alignment, const size_t size)
{
	if (!is_valid_alignment(alignment)) {
		errno = EINVAL;
		return NULL;
	}

	// Try to use natural alignment of chunks.
	const uint32_t rank = get_rank(size);
	if (rank < CACHE_RANKS) {
		// Handle small, medium, and large sizes.
		if (alignment <= chunk_alignment(rank)) {
			void *ptr = alloc_chunk(cache, rank);
			if (unlikely(ptr == NULL))
				errno = ENOMEM;
			else
				memset(ptr, 0, memory_sizes[rank]);
			return ptr;
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
	void *const ptr = slice_cache_zalloc(cache, size + align_mask);
	if (ptr == NULL)
		return ptr;
	return (void *) ((((uintptr_t) ptr) + align_mask) & ~align_mask);
}

void *
slice_cache_aligned_calloc(struct slice_cache *const cache, const size_t alignment, const size_t num, const size_t size)
{
	size_t total;
	if(__builtin_mul_overflow(num, size, &total)) {
		errno = EOVERFLOW;
		return NULL;
	}
	return slice_cache_aligned_zalloc(cache, alignment, total);
}

void *
slice_cache_realloc(struct slice_cache *const cache, void *const ptr, const size_t size)
{
	// Try to reuse the original chunk.
	size_t old_size;
	struct span_header *const hdr = span_from_ptr(ptr);
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

inline void
slice_cache_free(struct slice_cache *const local_cache, void *const ptr)
{
	struct span_header *const hdr = span_from_ptr(ptr);
	if (unlikely(hdr == NULL)) {
		if (likely(ptr == 0))
			return;
		abort();
	}

	if (likely(hdr->cache == local_cache) && likely(span_is_regular(hdr))) {
		// Nice, this is a regular local free.
		free_chunk((struct slice_alloc_span *) hdr, ptr);
	} else if (likely(span_is_regular(hdr))) {
		// Well, this is really a remote free.
		struct slice_cache_mpsc_node *const link = ptr;
		mpsc_qlink_prepare(link);
		mpsc_queue_append(&hdr->cache->remote_free_list, link);
	} else {
		// Free super-large chunks.
		atomic_fetch_add_explicit(&hdr->cache->singular_free_num, 1, memory_order_relaxed);
		span_destroy(hdr);
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

	// TODO: support over-aligned chunks

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
#if 1
# define TLS_ATTR
#else
# define TLS_ATTR __attribute__((tls_model("initial-exec")))
#endif
static __thread struct slice_cache *local_cache TLS_ATTR = NULL;

// This is used for thread-local cache cleanup.
static pthread_key_t local_cache_key;
static pthread_once_t local_cache_once = PTHREAD_ONCE_INIT;

// Initial cache used for bootstrapping.
static struct slice_cache initial_cache;
static spinlock_t initial_cache_lock = SPINLOCK_INIT;

static void
release_local_cache(struct slice_cache *cache, void *data __attribute__((unused)))
{
	if (cache != &initial_cache) {
		spin_lock(&initial_cache_lock);
		slice_cache_free(&initial_cache, cache);
		spin_unlock(&initial_cache_lock);
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
		// Initialize global data needed for local caches if needed.
		pthread_once(&local_cache_once, prepare_local_cache);

		// Create a new local cache.
		spin_lock(&initial_cache_lock);
		cache = slice_cache_alloc(&initial_cache, sizeof(struct slice_cache));
		spin_unlock(&initial_cache_lock);
		if (cache == NULL)
			return NULL;
		slice_cache_prepare(cache);
		local_cache = cache;

		// This is only for cleanup. We don't use pthread_getspecific().
		pthread_setspecific(local_cache_key, cache);
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
slice_aligned_zalloc(const size_t alignment, const size_t size)
{
	struct slice_cache *cache = get_local_cache();
	if (unlikely(cache == NULL)) {
		errno = ENOMEM;
		return NULL;
	}
	return slice_cache_aligned_zalloc(cache, alignment, size);
}

void *
slice_aligned_calloc(const size_t alignment, const size_t num, const size_t size)
{
	struct slice_cache *cache = get_local_cache();
	if (unlikely(cache == NULL)) {
		errno = ENOMEM;
		return NULL;
	}
	return slice_cache_aligned_calloc(cache, alignment, num, size);
}

void *
slice_realloc(void *const ptr, const size_t size)
{
	if (ptr == NULL) {
		return slice_alloc(size);
	} else if (size == 0) {
		slice_free(ptr);
		return NULL;
	}

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
	slice_cache_free(local_cache, ptr);
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
