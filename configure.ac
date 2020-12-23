dnl Process this file with autoconf to produce a configure script.

dnl Initialize autoconf.
AC_PREREQ(2.68)
AC_INIT([slice-alloc], [0.0], [ademakov@gmail.com])
AC_CONFIG_MACRO_DIR([m4])
AC_CONFIG_AUX_DIR([build-aux])
AC_CONFIG_SRCDIR([src/slice-alloc.h])
AC_CONFIG_HEADERS([src/config.h])

dnl Initialize automake.
AM_INIT_AUTOMAKE([-Wall -Werror foreign subdir-objects])

dnl Determine the host system type.
AC_CANONICAL_HOST

dnl Check for API variants.
AC_GNU_SOURCE

dnl Checks for programs.
AC_PROG_CC
AC_PROG_CC_C99
AM_PROG_CC_C_O
AM_PROG_AR
AC_PROG_INSTALL

dnl Initialize libtool.
LT_INIT()

dnl Checks for libraries.
AC_SEARCH_LIBS([pthread_create], [pthread],
        [], [AC_MSG_ERROR(Cannot find pthread library)])

dnl Checks for header files.
AC_CHECK_HEADERS([pthread.h])

dnl Checks for typedefs, structures, and compiler characteristics.

dnl Checks for library functions.

dnl Check command line arguments

dnl Conclude
AC_CONFIG_FILES([
	Makefile
	src/Makefile])
AC_OUTPUT
