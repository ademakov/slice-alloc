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

#ifndef SLICE_ALLOC_H
#define SLICE_ALLOC_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

struct slice_cache;

struct slice_cache_node
{
	struct slice_cache_node *next;
	struct slice_cache_node *prev;
};

struct slice_cache_list
{
	struct slice_cache_node node;
};

/*
 * Cache release callback. It is safe to destroy a cache only
 * after the last memory chunk from it is released. Thus this
 * callback is used to notify about this event.
 */
typedef void (*slice_cache_release_t)(struct slice_cache *cache, void *data);

/*
 * A memory allocation cache.
 */
struct slice_cache
{
	/* The active span to allocate memory from. */
	struct slice_alloc_span *active;

	/* Inactive spans to gather freed memory. */
	struct slice_cache_list staging;

	/* Release list node.*/
	struct slice_cache_node release_node;
	/* Release callback. */
	slice_cache_release_t release_callback;
	/* Release callback user data. */
	void *release_callback_data;

	/* Statistics. */
	uint64_t regular_alloc_num;
	uint64_t regular_free_num;
	uint64_t singular_alloc_num;
	uint64_t _Atomic singular_free_num;
};

void
slice_cache_prepare(struct slice_cache *cache);

void
slice_cache_cleanup(struct slice_cache *cache, slice_cache_release_t cb, void *cb_data);

void
slice_cache_collect(struct slice_cache *cache);

void *
slice_cache_alloc(struct slice_cache *cache, size_t size);

void *
slice_cache_zalloc(struct slice_cache *cache, size_t size);

void *
slice_cache_calloc(struct slice_cache *cache, size_t num, size_t size);

void *
slice_cache_aligned_alloc(struct slice_cache *cache, size_t alignment, size_t size);

void *
slice_cache_aligned_zalloc(struct slice_cache *cache, size_t alignment, size_t size);

void *
slice_cache_aligned_calloc(struct slice_cache *cache, size_t alignment, size_t num, size_t size);

void *
slice_cache_realloc(struct slice_cache *cache, void *ptr, size_t size);

void
slice_cache_free(struct slice_cache *cache, void *ptr);

void
slice_cache_free_maybe_remotely(struct slice_cache *local_cache, void *ptr);

size_t
slice_usable_size(const void *ptr);

void
slice_scrap_collect(void);

void
slice_local_collect(void);

void *
slice_alloc(size_t size);

void *
slice_zalloc(size_t size);

void *
slice_calloc(size_t num, size_t size);

void *
slice_aligned_alloc(size_t alignment, size_t size);

void *
slice_aligned_zalloc(size_t alignment, size_t size);

void *
slice_aligned_calloc(size_t alignment, size_t num, size_t size);

void *
slice_realloc(void *ptr, size_t size);

void
slice_free(void *ptr);

#ifdef __cplusplus
} // extern "C"
#endif

#endif /* SLICE_ALLOC_H */
