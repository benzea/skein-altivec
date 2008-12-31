#include "SHA3api_ref.h"
#include <stdio.h>
#include <string.h>

#define T(d, r) { .data = d, .result = r, .datalen = 8 * (sizeof(d) - 1), }
#define TN(n, d, r) { .data = d, .result = r, .datalen = n, }

static struct {
	unsigned char *data, *result;
	size_t datalen;
} tests[] = {
#include "short_test_data.h"
#include "long_test_data.h"
};

#define NT (sizeof(tests)/sizeof(tests[0]))

int main(void)
{
	BitSequence hash[512 / 8];
	int i;
	for (i = 0; i < NT; i++) {
		Hash(512, tests[i].data, tests[i].datalen, hash);
		printf("nbits = %d\n", tests[i].datalen);
		if (memcmp(tests[i].result, hash, sizeof(hash)))
		        printf("FAIL %d!\n", i);
	}
	return 0;
}
