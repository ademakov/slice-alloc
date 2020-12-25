
#include "slice-alloc.h"

#include <stdio.h>
#include <pthread.h>

static void
test(void)
{
	void *ptr = slice_alloc(100);
	printf("%p\n", ptr);
	slice_free(ptr);
}

static void *
thread_test(void *arg)
{
	test();
	return arg == NULL ? NULL : slice_alloc(100);
}

int
main(int ac, char **av)
{
	test();

	{
		pthread_t tid;
		pthread_create(&tid, NULL, thread_test, NULL);

		void *ret;
		pthread_join(tid, &ret);
	}

	{
		pthread_t tid;
		pthread_create(&tid, NULL, thread_test, (void *) 1);

		void *ret;
		pthread_join(tid, &ret);
		slice_free(ret);

//		slice_scrap_collect();
	}

	return 0;
}
