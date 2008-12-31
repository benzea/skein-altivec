#include "SHA3api_ref.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/time.h>
#include <sys/resource.h>


/* Subtract the `struct timeval' values X and Y,
   storing the result in RESULT.
   Return 1 if the difference is negative, otherwise 0.  */
int
timeval_subtract (struct timeval *result, struct timeval *x, struct timeval *y)
{
	/* Perform the carry for the later subtraction by updating y. */
	if (x->tv_usec < y->tv_usec) {
		int nsec = (y->tv_usec - x->tv_usec) / 1000000 + 1;
  	y->tv_usec -= 1000000 * nsec;
		y->tv_sec += nsec;
	}
	if (x->tv_usec - y->tv_usec > 1000000) {
		int nsec = (x->tv_usec - y->tv_usec) / 1000000;
		y->tv_usec += 1000000 * nsec;
		y->tv_sec -= nsec;
	}

	/* Compute the time remaining to wait.
	   tv_usec is certainly positive. */
	result->tv_sec = x->tv_sec - y->tv_sec;
	result->tv_usec = x->tv_usec - y->tv_usec;

	/* Return 1 if result is negative. */
	return x->tv_sec < y->tv_sec;
}

#define LEN 1024*1024
int main(int argc, char **argv)
{
	BitSequence hash[512 / 8];
	char *buffer = malloc(LEN);
	unsigned int i;
	size_t len;
	hashState state;
	struct rusage start, end;
	FILE *f;
	
	if (argc < 2) {
		printf("You need to specify a file to hash!\n");
		return 1;
	}
	
	memset(hash, 0, 512/8);
	
	Init(&state, 512);
	f = fopen(argv[1], "r");
	if (f == NULL) {
		printf("Failed to open the file!\n");
		return 1;
	}
	
	getrusage(RUSAGE_SELF, &start);
	while (len = fread(buffer, 1, LEN, f)) {
		Update(&state, buffer, len*8);
	}
	Final(&state, hash);
	getrusage(RUSAGE_SELF, &end);
	
	for (i = 0; i < 512 / 8; i++)
		printf("%02X", hash[i]);
	timeval_subtract(&start.ru_utime, &end.ru_utime, &start.ru_utime);
	printf("\n");
	printf("Needed %i seconds and %i useconds.\n", start.ru_utime.tv_sec, start.ru_utime.tv_usec);
	return 0;
}
