
#include "slice-alloc.h"

#include <stdio.h>

int
main(int ac, char **av)
{
	void *ptr = slice_alloc(100);
	printf("%p\n", ptr);
	slice_free(ptr);
	return 0;
}
