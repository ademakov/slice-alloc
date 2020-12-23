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
 * A memory allocation cache.
 */
struct slice_cache
{
	/* The active span to allocate memory from. */
	struct slice_alloc_span *active;

	/* Inactive spans to gather freed memory. */
	struct slice_cache_list staging;
};

void
slice_cache_prepare(struct slice_cache *cache);

void
slice_cache_cleanup(struct slice_cache *cache);

void
slice_cache_collect(struct slice_cache *cache);

void *
slice_cache_alloc(struct slice_cache *cache, size_t size);

void *
slice_cache_aligned_alloc(struct slice_cache *const cache, const size_t alignment, const size_t size);

void
slice_cache_free(struct slice_cache *const cache, void *const ptr);

void *
slice_cache_realloc(struct slice_cache *const cache, void *const ptr, const size_t size);

size_t
slice_alloc_size(const void *const ptr);

#endif /* SLICE_ALLOC_H */
