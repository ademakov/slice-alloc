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

#ifndef SLICE_ALLOC_H
#define SLICE_ALLOC_H

#include <stddef.h>

#if defined(__cplusplus) && __cplusplus >= 201703L
# define SLICE_NODISCARD [[nodiscard]]
#elif defined(__GNUC__) || defined(__clang__)
# define SLICE_NODISCARD __attribute__((__warn_unused_result__))
#else
# define SLICE_NODISCARD
#endif

#ifdef __cplusplus
# if __cplusplus >= 201103L
#  define SLICE_NOEXCEPT noexcept
# else
#  define SLICE_NOEXCEPT throw()
# endif
#else
# define SLICE_NOEXCEPT
#endif

#if defined(__GNUC__) || defined(__clang__)
# define SLICE_EXPORT __attribute__((__visibility__("default")))
# define SLICE_NONNULL(params) __attribute__((__nonnull__ params))
#else
# define SLICE_EXPORT
# define SLICE_NONNULL(params)
#endif

#if defined(__GNUC__) || defined(__clang__)
# if __GNUC__ >= 11
#  define SLICE_NEWOBJ(dealloc) __attribute__((__malloc__, __malloc__ dealloc))
# else
#  define SLICE_NEWOBJ(dealloc) __attribute__((__malloc__))
# endif
#else
# define SLICE_NEWOBJ(dealloc)
#endif

#if defined(__GNUC__) || defined(__clang__)
# define SLICE_MALLOC(size) __attribute__((__malloc__, __alloc_size__(size)))
# define SLICE_CALLOC(num, size) __attribute__((__malloc__, __alloc_size__(num, size)))
# define SLICE_REALLOC(size) __attribute__((__alloc_size__(size)))
#else
# define SLICE_MALLOC(size)
# define SLICE_CALLOC(num, size)
# define SLICE_REALLOC(size)
#endif

#if defined(__GNUC__) && (__GNUC__ >= 5 || __GNUC__ == 4 && __GNUC_MINOR__ >= 9)
# define SLICE_ALIGN(align) __attribute__((__alloc_align__(align)))
#else
# define SLICE_ALIGN(align)
#endif

#ifdef __cplusplus
extern "C" {
#endif

struct slice_cache;

SLICE_EXPORT void
slice_cache_destroy(struct slice_cache *cache)
	SLICE_NOEXCEPT SLICE_NONNULL((1));

SLICE_NODISCARD SLICE_EXPORT struct slice_cache *
slice_cache_create(void)
	SLICE_NOEXCEPT SLICE_NEWOBJ((slice_cache_destroy));

SLICE_NODISCARD SLICE_EXPORT void *
slice_cache_alloc(struct slice_cache *cache, size_t size)
	SLICE_NOEXCEPT SLICE_NONNULL((1)) SLICE_MALLOC(2);

SLICE_NODISCARD SLICE_EXPORT void *
slice_cache_zalloc(struct slice_cache *cache, size_t size)
	SLICE_NOEXCEPT SLICE_NONNULL((1)) SLICE_MALLOC(2);

SLICE_NODISCARD SLICE_EXPORT void *
slice_cache_calloc(struct slice_cache *cache, size_t num, size_t size)
	SLICE_NOEXCEPT SLICE_NONNULL((1)) SLICE_CALLOC(2, 3);

SLICE_NODISCARD SLICE_EXPORT void *
slice_cache_realloc(struct slice_cache *cache, void *ptr, size_t size)
	SLICE_NOEXCEPT SLICE_NONNULL((1)) SLICE_REALLOC(3);

SLICE_NODISCARD SLICE_EXPORT void *
slice_cache_aligned_alloc(struct slice_cache *cache, size_t alignment, size_t size)
	SLICE_NOEXCEPT SLICE_NONNULL((1)) SLICE_ALIGN(2) SLICE_MALLOC(3);

SLICE_NODISCARD SLICE_EXPORT void *
slice_cache_aligned_zalloc(struct slice_cache *cache, size_t alignment, size_t size)
	SLICE_NOEXCEPT SLICE_NONNULL((1)) SLICE_ALIGN(2) SLICE_MALLOC(3);

SLICE_NODISCARD SLICE_EXPORT void *
slice_cache_aligned_calloc(struct slice_cache *cache, size_t alignment, size_t num, size_t size)
	SLICE_NOEXCEPT SLICE_NONNULL((1)) SLICE_ALIGN(2) SLICE_CALLOC(3, 4);

SLICE_EXPORT void
slice_cache_free(struct slice_cache *cache, void *ptr)
	SLICE_NOEXCEPT /* SLICE_NONNULL((1)) */;

SLICE_NODISCARD SLICE_EXPORT void *
slice_alloc(size_t size)
	SLICE_NOEXCEPT SLICE_MALLOC(1);

SLICE_NODISCARD SLICE_EXPORT void *
slice_zalloc(size_t size)
	SLICE_NOEXCEPT SLICE_MALLOC(1);

SLICE_NODISCARD SLICE_EXPORT void *
slice_calloc(size_t num, size_t size)
	SLICE_NOEXCEPT SLICE_CALLOC(1, 2);

SLICE_NODISCARD SLICE_EXPORT void *
slice_realloc(void *ptr, size_t size)
	SLICE_NOEXCEPT SLICE_REALLOC(2);

SLICE_NODISCARD SLICE_EXPORT void *
slice_aligned_alloc(size_t alignment, size_t size)
	SLICE_NOEXCEPT SLICE_ALIGN(1) SLICE_MALLOC(2);

SLICE_NODISCARD SLICE_EXPORT void *
slice_aligned_zalloc(size_t alignment, size_t size)
	SLICE_NOEXCEPT SLICE_ALIGN(1) SLICE_MALLOC(2);

SLICE_NODISCARD SLICE_EXPORT void *
slice_aligned_calloc(size_t alignment, size_t num, size_t size)
	SLICE_NOEXCEPT SLICE_ALIGN(1) SLICE_CALLOC(2, 3);

SLICE_EXPORT void
slice_free(void *ptr)
	SLICE_NOEXCEPT;

SLICE_EXPORT size_t
slice_usable_size(const void *ptr)
	SLICE_NOEXCEPT;

SLICE_EXPORT void
slice_cache_collect(struct slice_cache *cache)
	SLICE_NOEXCEPT SLICE_NONNULL((1));

SLICE_EXPORT void
slice_local_collect(void)
	SLICE_NOEXCEPT;

SLICE_EXPORT void
slice_scrap_collect(void)
	SLICE_NOEXCEPT;

#undef SLICE_NODISCARD
#undef SLICE_NOEXCEPT
#undef SLICE_EXPORT
#undef SLICE_NONNULL
#undef SLICE_NEWOBJ
#undef SLICE_MALLOC
#undef SLICE_CALLOC
#undef SLICE_REALLOC
#undef SLICE_ALIGN

#ifdef __cplusplus
} // extern "C"
#endif

#endif /* SLICE_ALLOC_H */
