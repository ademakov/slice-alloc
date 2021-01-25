/*
 * slice-alloc - a memory allocation library.
 *
 * Copyright (C) 2020,2021  Aleksey Demakov
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
#include <stdint.h>
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

// CPU cache-line size.
#define CACHE_ALIGN		__attribute__((__aligned__(64)))

#if 1
# define TLS_ATTR
#else
# define TLS_ATTR		__attribute__((tls_model("initial-exec")))
#endif

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

typedef CACHE_ALIGN struct
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

struct mpsc_node
{
	 struct mpsc_node *_Atomic next;
};

struct mpsc_queue
{
	CACHE_ALIGN struct mpsc_node *_Atomic tail;
	CACHE_ALIGN struct mpsc_node *head;
	struct mpsc_node stub;
};

static inline void
mpsc_qlink_prepare(struct mpsc_node *link)
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
mpsc_queue_append_span(struct mpsc_queue *list,
		       struct mpsc_node *head,
		       struct mpsc_node *tail)
{
	struct mpsc_node *prev = atomic_exchange(&list->tail, tail);
	atomic_store_explicit(&prev->next, head, memory_order_release);
}

static inline void
mpsc_queue_append(struct mpsc_queue *list, struct mpsc_node *link)
{
	mpsc_queue_append_span(list, link, link);
}

static struct mpsc_node *
mpsc_queue_remove(struct mpsc_queue *list)
{
	struct mpsc_node *head = list->head;
	struct mpsc_node *next = atomic_load_explicit(&head->next, memory_order_acquire);
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

	struct mpsc_node *tail = atomic_load_explicit(&list->tail, memory_order_acquire);
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

struct node
{
	struct node *next;
	struct node *prev;
};

struct list
{
	struct node node;
};

static inline void
list_prepare(struct list *list)
{
	list->node.next = list->node.prev = &list->node;
}

static inline const struct node *
list_stub(const struct list *list)
{
	return &list->node;
}

static inline struct node *
list_head(struct list *list)
{
	return list->node.next;
}

static inline struct node *
list_tail(struct list *list)
{
	return list->node.prev;
}

static inline bool
list_empty(const struct list *list)
{
	return list->node.next == list_stub(list);
}

static inline void
list_delete(struct node *node)
{
	node->prev->next = node->next;
	node->next->prev = node->prev;
}

static inline void
list_splice_after(struct node *node, struct node *head, struct node *tail)
{
	head->prev = node;
	tail->next = node->next;
	node->next->prev = tail;
	node->next = head;
}

static inline void
list_insert_after(struct node *node, struct node *node2)
{
	list_splice_after(node, node2, node2);
}

static inline void
list_splice_first(struct list *list, struct node *head, struct node *tail)
{
	list_splice_after(&list->node, head, tail);
}

static inline void
list_insert_first(struct list *list, struct node *node)
{
	list_insert_after(&list->node, node);
}

static inline struct node *
list_remove_first(struct list *list)
{
	struct node *head = list_head(list);
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

	// The memory cache the span belongs to.
	struct slice_cache *cache;
};

// Singular span header.
struct singular_span
{
	struct span_header header;

	// The memory size that is actually mmap()-ed.
	size_t virtual_size;
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
span_singular_size(const struct singular_span *span)
{
	return span->header.tag_or_size;
}

// Get the actual size of virtual memory occupied by the span.
static inline size_t
span_singular_virtual_size(const struct singular_span *span)
{
	return span->virtual_size;
}

static inline void *
span_singular_data(const struct singular_span *span)
{
	return (uint8_t *) span + span->offset;
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

static struct singular_span *
span_create_singular(struct slice_cache *const cache, const size_t size, const size_t alignment)
{
	const struct singular_span_params params = span_compute_singular(size, alignment);
	if (params.virtual_size == 0)
		return NULL;

	struct singular_span *span = span_alloc_space(params.virtual_size, SPAN_ALIGNMENT_MASK);
	if (likely(span != NULL)) {
		span->header.tag_or_size = params.virtual_size - params.offset;
		span->header.cache = cache;
		span->virtual_size = params.virtual_size;
		span->offset = params.offset;
	}
	return span;
}

static void
span_destroy_singular(struct singular_span *const span)
{
	span_free_space(span, span_singular_virtual_size(span));
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
  [ for blocks also repeated at bytes 4, 8, ... ]

  byte 1
  ------
  for a used slice
    value == 0xa0 -- 160 -- 1 0 1 0 | 0 0 0 0

  for a block
    value == 0xa1 -- 161 -- 1 0 1 0 | 0 0 0 1
  also repeated at bytes 5, 9, ...

  for a free slice
    value == 0xff -- 255
    1 1 1 1 | 1 1 1 1

  byte 2
  ------
  for a used slice -- base of itself, lo 6 bits
    value >= 0x40 --  64 -- 0 1  0 0 | 0 0 0 0
    value <= 0x7f -- 127 -- 0 1  1 1 | 1 1 1 1
    0 1 x x | x x x x
  [ for blocks also repeated at bytes 6, 10, ... ]

  for a free slice
    value == 0xfe -- 254
    1 1 1 1 | 1 1 1 0

  byte 3
  ------
  for a used slice -- base of itself, hi 5 bits
    value >= 0x80 -- 128 -- 1 0 0 0 | 0 0 0 0
    value <= 0x9f -- 159 -- 1 0 0 1 | 1 1 1 1
    1 0 x x | x x x x
  [ for blocks also repeated at bytes 7, 11, ... ]

  byte 4*n
  --------
  for a block
    value == 0xb0 -- 176 -- 1 0 1 1 | 0 0 0 0

  byte 4*n + 1
  ------------
  for a block
    value == 0xc0 -- 192 -- 1 1 0 0 | 0 0 0 0

  byte 4*n + 2
  ------------
  for a block
    value == 0xd0 -- 208 -- 1 1 0 1 | 0 0 0 0

*/

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

#define TAG_USED		(10u << 4u)
#define TAG_USED_ALIGN		(TAG_USED + 1u)
#define TAG_USED_BLOCK		(TAG_USED + 2u)

#define TAG_TAIL_1		(11u << 4u)
#define TAG_TAIL_2		(12u << 4u)
#define TAG_TAIL_3		(13u << 4u)

#define TAG_FREE		(255u)

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
	struct block *next;
};

// A group of regular spans allocated at once.
struct regular_extent
{
	uint8_t *base;
	uint64_t free;
	struct node node;
};

// A memory allocation cache.
struct slice_cache
{
	// Span list.
	struct list staging;

	// Cached blocks with free chunks.
	struct block *blocks[BLOCK_RANKS];

	// Cached free slices.
	void *slices[SLICE_RANKS];
};

// Regular span header.
struct regular_span
{
	struct span_header header;
	struct regular_extent *extent;

	uint32_t slice_num;
	uint32_t block_num;

	// Per-cache span list node.
	struct node staging_node;
	// Global release list node.
	struct node release_node;

	/* The list of chunks freed remotely. */
	struct mpsc_queue remote_free_list;

	// The map of units.
	uint8_t units[UNIT_NUMBER];

	bool contains_cache;

	// Reserved space for a memory cache. Some spans use it but most
	// of them don't.
	struct slice_cache space_for_cache;
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

static spinlock_t initial_cache_lock = SPINLOCK_INIT;
static spinlock_t span_release_lock = SPINLOCK_INIT;
static spinlock_t extents_lock = SPINLOCK_INIT;

// The initial cache (contains other caches).
static struct slice_cache *initial_cache;
static struct regular_extent initial_extent;

static struct list full_extents = {
	.node = {
		.next = &full_extents.node,
		.prev = &full_extents.node,
	}
};

static struct list non_full_extents = {
	.node = {
		.next = &non_full_extents.node,
		.prev = &non_full_extents.node,
	}
};

// Pending cache release list.
static struct list span_release_list = {
	.node = {
		.next = &span_release_list.node,
		.prev = &span_release_list.node,
	}
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

static inline size_t
unit_from_ptr(const struct regular_span *const span, const void *ptr)
{
#if 0
	return ((uintptr_t) ptr & SPAN_ALIGNMENT_MASK) / UNIT_SIZE;
#else
	return ((uintptr_t) ptr - (uintptr_t) span) / UNIT_SIZE;
#endif
}

static inline uint32_t
find_slice_info(const struct regular_span *const span, const size_t unit)
{
	const size_t value = span->units[unit];
	const size_t index = value >> 4u;
	VERIFY(index < 14u, "bad pointer");

	static uint8_t table[] = {
		0, 0, 0, 0,
		2, 2, 2, 2,
		3, 3, 1, 4,
		5, 6, 1, 1 // the last 2 values should never be encountered
	};

	return unit - table[index];
}

static inline uint32_t
get_slice_rank(const struct regular_span *const span, const uint32_t unit)
{
	return *(span->units + unit);
}

static inline uint32_t
get_slice_tag(const struct regular_span *const span, const uint32_t unit)
{
	return *(span->units + unit + 1u);
}

static inline uint32_t
get_slice_base(const struct regular_span *const span, const uint32_t unit)
{
	const uint32_t lo = *(span->units + unit + 2u) & UNIT_LMASK;
	const uint32_t hi = *(span->units + unit + 3u) & UNIT_HMASK;
	return lo | (hi << UNIT_LBITS);
}

static uint32_t
find_slice(const struct slice_cache *const cache, uint32_t rank)
{
	ASSERT(rank >= BLOCK_RANKS && rank < CACHE_RANKS);

	while (rank < (BLOCK_RANKS + BUDDY_RANKS)) {
		if (cache->slices[rank - BLOCK_RANKS])
			return rank;
		rank += 4;
	}
	while (rank < CACHE_RANKS) {
		if (cache->slices[rank - BLOCK_RANKS])
			return rank;
		rank += 1;
	}

	return rank;
}

static void
cut_one(struct regular_span *const span, const uint32_t base, const uint32_t rank)
{
	*(span->units + base) = rank;
	*(span->units + base + 1u) = TAG_FREE;

	void *const ptr = (uint8_t *) span + base * UNIT_SIZE;
	*((void **) ptr) = *(span->header.cache->slices + rank - BLOCK_RANKS);
	*(span->header.cache->slices + rank - BLOCK_RANKS) = ptr;
}

static void
cut_two(struct regular_span *const span, const uint32_t base, const uint32_t first, const uint32_t second)
{
	cut_one(span, base, first);
	cut_one(span, base + memory_sizes[first] / UNIT_SIZE, second);
}

static void
split_slice(struct regular_span *const span, uint32_t base, uint32_t rank, const uint32_t original_rank)
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
coalesce_blocks(struct slice_cache *const cache)
{
	// Convert empty blocks to slices.
	for (uint32_t rank = 0; rank < BLOCK_RANKS; rank++) {
		struct block **pblock = &cache->blocks[rank];
		while (*pblock != NULL) {
			struct block *const block = *pblock;
			if (block->free_num < block->free_max) {
				pblock = &block->next;
				continue;
			}

			struct regular_span *span = (struct regular_span *) span_from_ptr(block);
			const size_t base = unit_from_ptr(span, block);

			*(span->units + base) = block_slice[rank];
			*(span->units + base + 1u) = TAG_USED;
			*pblock = block->next;

			span->block_num--;
		}
	}
}

static inline void
free_chunk(struct slice_cache *const cache, struct regular_span *const span, void *const ptr)
{
	// Identify the chunk.
	const size_t unit = unit_from_ptr(span, ptr);
	const uint32_t info = find_slice_info(span, unit);
	const uint32_t rank = get_slice_rank(span, info);
	VERIFY(rank < CACHE_RANKS, "bad pointer");

	if (likely(rank < BLOCK_RANKS)) {
		// Free a chunk from a block.
		const uint32_t base = get_slice_base(span, info);
		VERIFY(base >= 4 && base < UNIT_NUMBER, "bad pointer");
		VERIFY(get_slice_tag(span, base) == TAG_USED_BLOCK, "double free");

		VERIFY(span->block_num > 0, "bad pointer");
		struct block *const block = (struct block *) ((uint8_t *) span + base * UNIT_SIZE);
		VERIFY(block->free_num < block->free_max, "double free");

		// If the block was empty it now becomes usable again.
		if (block->free_num++ == 0) {
			block->next = cache->blocks[rank];
			cache->blocks[rank] = block;
		}

		// Add the chunk to the free list.
		*((void **) ptr) = block->free_list;
		block->free_list = ptr;
	} else {
		// Free a whole slice.
		span->slice_num--;

		if (likely(get_slice_tag(span, info) == TAG_USED)) {
			*(span->units + info + 1u) = TAG_FREE;

			// Add the chunk to the free list.
			*((void **) ptr) = *(cache->slices + rank - BLOCK_RANKS);
			*(cache->slices + rank - BLOCK_RANKS) = ptr;
		} else {
			// Take into account alignment.
			const uint32_t base = get_slice_base(span, info);
			VERIFY(base >= 4 && base < UNIT_NUMBER, "bad pointer");
			VERIFY(get_slice_tag(span, base) == TAG_USED_ALIGN, "bad pointer");
			*(span->units + base + 1u) = TAG_FREE;

			// Add the chunk to the free list.
			void *const ptr2 = ((uint8_t *) span + base * UNIT_SIZE);
			*((void **) ptr2) = *(cache->slices + rank - BLOCK_RANKS);
			*(cache->slices + rank - BLOCK_RANKS) = ptr2;
		}
	}
}

static void
release_remote_one(struct regular_span *const span)
{
	for (;;) {
		void *ptr = mpsc_queue_remove(&span->remote_free_list);
		if (ptr == NULL)
			break;
		free_chunk(span->header.cache, span, ptr);
	}
}

static void
release_remote(struct slice_cache *const cache)
{
	struct node *node = list_head(&cache->staging);
	while (node != list_stub(&cache->staging)) {
		struct regular_span *span = containerof(node, struct regular_span, staging_node);
		release_remote_one(span);
		node = node->next;
	}
}

static struct regular_span *
create_regular(struct slice_cache *const cache, const bool is_initial_cache)
{
	spin_lock(&extents_lock);
	if (list_empty(&non_full_extents)) {
		struct regular_extent *extent;
		if (!is_initial_cache) {
			spin_unlock(&extents_lock);

			spin_lock(&initial_cache_lock);
			extent = slice_cache_alloc(initial_cache, sizeof(struct regular_extent));
			if (unlikely(extent == NULL)) {
				spin_unlock(&initial_cache_lock);
				return NULL;
			}

			spin_lock(&extents_lock);
		} else {
			extent = &initial_extent;
		}

		if (!list_empty(&non_full_extents)) {
			if (!is_initial_cache) {
				slice_cache_free(initial_cache, extent);
				spin_unlock(&initial_cache_lock);
			}
		} else {
			void *space = span_alloc_space(64 * SPAN_REGULAR_SIZE, SPAN_ALIGNMENT_MASK);
			if (unlikely(space == NULL)) {
				spin_unlock(&extents_lock);
				if (!is_initial_cache) {
					slice_cache_free(initial_cache, extent);
					spin_unlock(&initial_cache_lock);
				}
				return NULL;
			}

			if (!is_initial_cache)
				spin_unlock(&initial_cache_lock);

			extent->base = space;
			extent->free = ~((uint64_t) 0);
			list_insert_first(&non_full_extents, &extent->node);
		}
	}

	struct node *const node = list_head(&non_full_extents);
	struct regular_extent *const extent = containerof(node, struct regular_extent, node);
	const size_t span_index = ctz(extent->free);

	extent->free ^= ((uint64_t) 1u) << span_index;
	if (extent->free == 0) {
		list_delete(node);
		list_insert_first(&full_extents, node);
	}
	spin_unlock(&extents_lock);

	struct regular_span *span = (struct regular_span *) (extent->base + span_index * SPAN_REGULAR_SIZE);
	span->contains_cache = (cache == NULL);
	span->header.tag_or_size = SPAN_REGULAR_TAG;
	span->header.cache = (span->contains_cache ? &span->space_for_cache : cache);
	span->extent = extent;

	// As the span comes after a fresh mmap() call there is no need
	// to zero it out manually.
#if 0
	span->block_num = 0;
	span->slice_num = 0;

	if (span->contains_cache) {
		for (size_t i = 0; i < BLOCK_RANKS; i++)
			span->space_for_cache.blocks[i] = NULL;
		for (uint32_t i = 0; i < SLICE_RANKS; i++)
			span->space_for_cache.slices[i] = NULL;
	}

	memset(span->units, 0, sizeof span->units);
#endif

	// Initialize the remote free list.
	mpsc_queue_prepare(&span->remote_free_list);

	// The initial heap layout takes out the very first 4KiB slice
	// from the span. It is used up for the very span header that is
	// initialized here.
	split_slice(span, 0, BLOCK_RANKS, CACHE_RANKS);
	span->units[0] = BLOCK_RANKS;

	return span;
}

static void
destroy_regular(struct regular_span *const span)
{
	struct regular_extent *const extent = span->extent;
	madvise(span, SPAN_REGULAR_SIZE, MADV_DONTNEED);

	spin_lock(&extents_lock);

	if (extent->free == 0) {
		list_delete(&extent->node);
		list_insert_first(&non_full_extents, &extent->node);
	}

	const size_t span_index = ((uint8_t *) span - extent->base) / SPAN_REGULAR_SIZE;
	extent->free |= ((uint64_t) 1u) << span_index;

	// TODO: release totally free extents.

	spin_unlock(&extents_lock);
}

static void *
alloc_slice(struct slice_cache *const cache, const uint32_t chunk_rank)
{
	ASSERT(chunk_rank < CACHE_RANKS);

	const uint32_t rank = chunk_rank >= BLOCK_RANKS ? chunk_rank : block_slice[chunk_rank];
	uint32_t original_rank = find_slice(cache, rank);
	if (original_rank >= CACHE_RANKS) {
		release_remote(cache);
		coalesce_blocks(cache);
		// TODO: coalesce free slices

		original_rank = find_slice(cache, rank);
		if (original_rank >= CACHE_RANKS) {
			struct regular_span *span = create_regular(cache, false);
			if (span == NULL) {
				// Out of memory.
				return NULL;
			}
			list_insert_first(&cache->staging, &span->staging_node);

			original_rank = find_slice(cache, rank);
			ASSERT(original_rank < CACHE_RANKS);
		}
	}

	// Remove the slice from the free list.
	void *const ptr = cache->slices[original_rank - BLOCK_RANKS];
	cache->slices[original_rank - BLOCK_RANKS] = *((void **) ptr);

	struct regular_span *const span = (struct regular_span *) span_from_ptr(ptr);
	const size_t base = unit_from_ptr(span, ptr);

	// If the slice is bigger than required then split it.
	if (rank != original_rank)
		split_slice(span, base, rank, original_rank);

	uint8_t *map = span->units + base;
	if (chunk_rank >= BLOCK_RANKS) {
		// The slice is to be used as such.
		span->slice_num++;

		// Fill the unit map at the start only.
		map[0] = chunk_rank;
		map[1] = TAG_USED;

	} else {
		// The slice is to be used as a block.
		span->block_num++;

		// Make the unit map pattern.
		const uint8_t pattern[4] = {
			chunk_rank,
			TAG_USED_BLOCK,
			(base & UNIT_LMASK) + BASE_LFLAG,
			(base >> UNIT_LBITS) + BASE_HFLAG,
		};

		// Fill the unit map for the whole slice.
		uint32_t num = memory_sizes[rank] / UNIT_SIZE;
		while (num >= 4) {
			memcpy(map, pattern, 4);
			map += 4;
			num -= 4;
		}
		if (num > 0) {
			static const uint8_t tail[] = {
				TAG_TAIL_1, TAG_TAIL_2, TAG_TAIL_3
			};
			memcpy(map, tail, num);
		}
	}

	return ptr;
}

static struct block *
alloc_block(struct slice_cache *const cache, const uint32_t rank)
{
	// Try to avoid allocation by releasing remotely freed chunks.
	release_remote(cache);
	if (cache->blocks[rank] != NULL)
		return cache->blocks[rank];

	// Allocate a large chunk.
	struct block *const block = alloc_slice(cache, rank);
	if (unlikely(block == NULL))
		return NULL;

	// Cache the block for futher use.
	block->next = cache->blocks[rank];
	cache->blocks[rank] = block;

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
	// Try to use a cached block.
	struct block *block = cache->blocks[rank];
	if (block != NULL) {
		// If the block becomes empty delete it from the cache.
		if (block->free_num == 1)
			cache->blocks[rank] = block->next;
	} else {
		// Allocate a new block.
		block = alloc_block(cache, rank);
		if (unlikely(block == NULL))
			return NULL;
	}
	block->free_num--;

	// Get a chunk from the free list.
	void *ptr = block->free_list;
	block->free_list = *((void **) ptr);

	return ptr;
}

static inline uint32_t
get_chunk_rank(const struct span_header *const hdr, const void *const ptr)
{
	struct regular_span *const span = (struct regular_span *) hdr;
	const size_t unit = unit_from_ptr(span, ptr);
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

static bool
is_cache_empty(struct slice_cache *const cache)
{
	struct node *node = list_head(&cache->staging);
	while (node != list_stub(&cache->staging)) {
		struct regular_span *span = containerof(node, struct regular_span, staging_node);
		if ((span->slice_num + span->block_num) != 0)
			return false;
		node = node->next;
	}
	return true;
}

static void
prepare_cache(struct slice_cache *const cache, struct regular_span *const span)
{
	list_prepare(&cache->staging);
	list_insert_first(&cache->staging, &span->staging_node);
}

/**********************************************************************
 * Slice cache management - public API.
 **********************************************************************/

struct slice_cache *
slice_cache_create(void)
{
	spin_lock(&initial_cache_lock);
	if (unlikely(initial_cache == NULL)) {
		struct regular_span *initial_span = create_regular(NULL, true);
		if (unlikely(initial_span == NULL)) {
			spin_unlock(&initial_cache_lock);
			return NULL;
		}

		initial_cache = &initial_span->space_for_cache;
		prepare_cache(initial_cache, initial_span);
	}
	spin_unlock(&initial_cache_lock);

	// Allocate the original span for the cache.
	struct regular_span *const span = create_regular(NULL, false);
	if (unlikely(span == NULL))
		return NULL;

	// Initialize the cache inside the original span.
	struct slice_cache *const cache = &span->space_for_cache;
	prepare_cache(cache, span);
	return cache;
}

void
slice_cache_destroy(struct slice_cache *cache)
{
	// Try to release some deffered spans.
	slice_scrap_collect();

	// Try to release some ordinary spans from the cache.
	slice_cache_collect(cache);

	// The original span of the cache contains the cache struct itself.
	struct regular_span *orig = (struct regular_span *) span_from_ptr(cache);
	const bool free_orig = ((orig->slice_num + orig->block_num) == 0);
	if (free_orig) {
		// If the original span is empty then it must be destroyed
		// on one of the following steps.
		list_delete(&orig->staging_node);
	} else {
		// Demote the original span to an ordinary one as the cache
		// is being destroyed now.
		orig->contains_cache = false;
	}

	// If there are some still used spans then keep them around until
	// they become totally free.
	if (!list_empty(&cache->staging)) {
		struct list list;
		list_prepare(&list);

		struct node *node = list_head(&cache->staging);
		while (node != list_stub(&cache->staging)) {
			struct node *const next = node->next;
			struct regular_span *span = containerof(node, struct regular_span, staging_node);
			list_delete(node);

			span->header.cache = &span->space_for_cache;
			prepare_cache(span->header.cache, span);
			list_insert_first(&list, &span->release_node);

			node = next;
		}

		prepare_cache(cache, orig);

		// TODO: move free lists from the original cache
		// to new per-span caches.

		// Now store the spans for future release.
		spin_lock(&span_release_lock);
		list_splice_first(&span_release_list, list_head(&list), list_tail(&list));
		spin_unlock(&span_release_lock);
	}

	// Destroy the span along with the cache unless it is still used.
	if (free_orig) {
		destroy_regular(orig);
	}
}

void
slice_scrap_collect(void)
{
	struct list list;
	list_prepare(&list);

	if (spin_try_lock(&span_release_lock)) {
		if (!list_empty(&span_release_list)) {
			list_splice_first(&list,
					  list_head(&span_release_list),
					  list_tail(&span_release_list));
			list_prepare(&span_release_list);
		}
		spin_unlock(&span_release_lock);

		struct node *node = list_head(&list);
		while (node != list_stub(&list)) {
			struct node *const next = node->next;
			struct regular_span *span = containerof(node, struct regular_span, release_node);
			// Check for remotely freed chunks.
			release_remote_one(span);
			coalesce_blocks(&span->space_for_cache);
			// Destroy the span if it is empty.
			if ((span->slice_num + span->block_num) == 0) {
				list_delete(node);
				destroy_regular(span);
			}
			node = next;
		}

		if (!list_empty(&list)) {
			spin_lock(&span_release_lock);
			list_splice_first(&span_release_list,
					  list_head(&list),
					  list_tail(&list));
			spin_unlock(&span_release_lock);
		}
	}
}

void
slice_cache_collect(struct slice_cache *const cache)
{
	coalesce_blocks(cache);

	// Try to free some spans in the list.
	struct node *node = list_head(&cache->staging);
	const struct node *const stub = list_stub(&cache->staging);
	while (node != stub) {
		struct node *const next = node->next;
		struct regular_span *span = containerof(node, struct regular_span, staging_node);

		// Check for remotely freed chunks.
		release_remote_one(span);

		// Destroy the span if it is empty.
		if ((span->slice_num + span->block_num) == 0 && !span->contains_cache) {
			list_delete(node);
			destroy_regular(span);
		}

		node = next;
	}
}

inline void *
slice_cache_alloc(struct slice_cache *const cache, const size_t size)
{
	const uint32_t rank = get_rank(size);
	if (likely(rank < BLOCK_RANKS)) {
		// Handle small and medium sizes.
		void *ptr = alloc_chunk(cache, rank);
		if (likely(ptr != NULL))
			return ptr;
	} else if (likely(rank < CACHE_RANKS)) {
		// Handle large sizes.
		void *ptr = alloc_slice(cache, rank);
		if (likely(ptr != NULL))
			return ptr;
	} else {
		// Handle super-large sizes.
		struct singular_span *span = span_create_singular(cache, size, ALIGNMENT);
		if (likely(span != NULL))
			return span_singular_data(span);
	}

	errno = ENOMEM;
	return NULL;
}

void *
slice_cache_zalloc(struct slice_cache *const cache, const size_t size)
{
	const uint32_t rank = get_rank(size);
	if (likely(rank < BLOCK_RANKS)) {
		// Handle small, medium, and large sizes.
		void *ptr = alloc_chunk(cache, rank);
		if (likely(ptr != NULL)) {
			memset(ptr, 0, memory_sizes[rank]);
			return ptr;
		}
	} else if (likely(rank < CACHE_RANKS)) {
		void *ptr = alloc_slice(cache, rank);
		if (likely(ptr != NULL)) {
			memset(ptr, 0, memory_sizes[rank]);
			return ptr;
		}
	} else {
		// Handle super-large sizes.
		struct singular_span *span = span_create_singular(cache, size, ALIGNMENT);
		if (likely(span != NULL))
			return span_singular_data(span);
	}

	errno = ENOMEM;
	return NULL;
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
			void *ptr = (rank < BLOCK_RANKS
				     ? alloc_chunk(cache, rank)
				     : alloc_slice(cache, rank));
			if (unlikely(ptr == NULL))
				errno = ENOMEM;
			return ptr;
		}
	} else {
		// Handle super-large sizes.
		struct singular_span *span = span_create_singular(cache, size,
								  max(alignment, ALIGNMENT));
		if (unlikely(span == NULL)) {
			errno = ENOMEM;
			return NULL;
		}
		return span_singular_data(span);
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
			void *ptr = (rank < BLOCK_RANKS
				     ? alloc_chunk(cache, rank)
				     : alloc_slice(cache, rank));
			if (unlikely(ptr == NULL))
				errno = ENOMEM;
			else
				memset(ptr, 0, memory_sizes[rank]);
			return ptr;
		}
	} else {
		// Handle super-large sizes.
		struct singular_span *span = span_create_singular(cache, size,
								  max(alignment, ALIGNMENT));
		if (unlikely(span == NULL)) {
			errno = ENOMEM;
			return NULL;
		}
		return span_singular_data(span);
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
		old_size = span_singular_size((struct singular_span *) hdr);
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
		free_chunk(local_cache, (struct regular_span *) hdr, ptr);
	} else if (likely(span_is_regular(hdr))) {
		// Well, this is really a remote free.
		struct mpsc_node *const link = ptr;
		mpsc_qlink_prepare(link);
		mpsc_queue_append(&((struct regular_span *) hdr)->remote_free_list, link);
	} else {
		// Free super-large chunks.
		span_destroy_singular((struct singular_span *) hdr);
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
		return span_singular_size((struct singular_span *) hdr);
	}

	// Handle a chunk in a regular span.
	return get_chunk_size(hdr, ptr);
}

/**********************************************************************
 * Thread-specific memory management - public API.
 **********************************************************************/

// This is used for thread-local cache cleanup.
static pthread_key_t local_cache_key;
static pthread_once_t local_cache_once = PTHREAD_ONCE_INIT;

// Thread-local cache.
static __thread struct slice_cache *local_cache TLS_ATTR = NULL;

static void
destroy_local_cache(void *ptr)
{
	slice_cache_destroy((struct slice_cache *) ptr);
}

static void
destroy_initial_cache(void)
{
	pthread_key_delete(local_cache_key);
	slice_cache_destroy(initial_cache);
}

static void
prepare_local_cache(void)
{
	// Create the key needed for cleanup on thread exit.
	pthread_key_create(&local_cache_key, destroy_local_cache);

	// Register for cleanup on process exit.
	atexit(destroy_initial_cache);
}

static struct slice_cache *
create_local_cache_noerrno(void)
{
	// Create a new local cache.
	struct slice_cache *cache = slice_cache_create();
	if (likely(cache != NULL)) {
		local_cache = cache;

		// This is only for cleanup. We don't use pthread_getspecific().
		pthread_once(&local_cache_once, prepare_local_cache);
		pthread_setspecific(local_cache_key, cache);
	}
	return cache;
}

static struct slice_cache *
create_local_cache(void)
{
	struct slice_cache *cache = create_local_cache_noerrno();
	if (unlikely(cache == NULL))
		errno = ENOMEM;
	return cache;
}

static inline struct slice_cache *
get_local_cache_noerrno(void)
{
	struct slice_cache *cache = local_cache;
	if (unlikely(cache == NULL))
		cache = create_local_cache_noerrno();
	return cache;
}

static inline struct slice_cache *
get_local_cache(void)
{
	struct slice_cache *cache = local_cache;
	if (unlikely(cache == NULL))
		cache = create_local_cache();
	return cache;
}

void
slice_local_collect(void)
{
	if (local_cache != NULL)
		slice_cache_collect(local_cache);
}

void *
slice_alloc(const size_t size)
{
	struct slice_cache *cache = get_local_cache();
	if (unlikely(cache == NULL))
		return NULL;
	return slice_cache_alloc(cache, size);
}

void *
slice_zalloc(const size_t size)
{
	struct slice_cache *cache = get_local_cache();
	if (unlikely(cache == NULL))
		return NULL;
	return slice_cache_zalloc(cache, size);
}

void *
slice_calloc(const size_t num, const size_t size)
{
	struct slice_cache *cache = get_local_cache();
	if (unlikely(cache == NULL))
		return NULL;
	return slice_cache_calloc(cache, num, size);
}

void *
slice_aligned_alloc(const size_t alignment, const size_t size)
{
	struct slice_cache *cache = get_local_cache();
	if (unlikely(cache == NULL))
		return NULL;
	return slice_cache_aligned_alloc(cache, alignment, size);
}

void *
slice_aligned_zalloc(const size_t alignment, const size_t size)
{
	struct slice_cache *cache = get_local_cache();
	if (unlikely(cache == NULL))
		return NULL;
	return slice_cache_aligned_zalloc(cache, alignment, size);
}

void *
slice_aligned_calloc(const size_t alignment, const size_t num, const size_t size)
{
	struct slice_cache *cache = get_local_cache();
	if (unlikely(cache == NULL))
		return NULL;
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
	if (unlikely(cache == NULL))
		return NULL;
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

	struct slice_cache *cache = get_local_cache_noerrno();
	if (unlikely(cache == NULL))
		return ENOMEM;

	// TODO: do not set errno
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
