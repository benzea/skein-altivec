#include "SHA3api_ref.h"
#include <stdio.h>
#include <string.h>

#define T(d, r) { .data = d, .result = r, .datalen = 8 * (sizeof(d) - 1), }
#define TN(n, d, r) { .data = d, .result = r, .datalen = n, }

static struct {
	unsigned char *data, *result;
	size_t datalen;
} tests512[] = {
#include "short_test_512_data.h"
#include "long_test_512_data.h"
};

static struct {
	unsigned char *data, *result;
	size_t datalen;
} tests256[] = {
#include "short_test_256_data.h"
#include "long_test_256_data.h"
};

#define ITEMS(array) (sizeof(array)/sizeof(array[0]))

int main(void)
{
	BitSequence hash256[256 / 8];
	BitSequence hash512[512 / 8];
	int i;
	for (i = 0; i < ITEMS(tests256); i++) {
		Hash(256, tests256[i].data, tests256[i].datalen, hash256);
		printf("256 nbits = %d\n", tests256[i].datalen);
		if (memcmp(tests256[i].result, hash256, sizeof(hash256)))
		        printf("FAIL %d!\n", i);
	}

	for (i = 0; i < ITEMS(tests512); i++) {
		Hash(512, tests512[i].data, tests512[i].datalen, hash512);
		printf("512 nbits = %d\n", tests512[i].datalen);
		if (memcmp(tests512[i].result, hash512, sizeof(hash512)))
		        printf("FAIL %d!\n", i);
	}

	return 0;
}
