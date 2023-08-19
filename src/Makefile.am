lib_LTLIBRARIES = libslicealloc.la

include_HEADERS = slice-alloc.h

libslicealloc_la_SOURCES = slice-alloc.c slice-alloc.h
libslicealloc_la_CFLAGS = -fvisibility=hidden

noinst_PROGRAMS = test

test_SOURCES = test.c
test_LDADD = libslicealloc.la
