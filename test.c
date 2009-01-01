#include "SHA3api_ref.h"
#include <stdio.h>
#include <string.h>

#define T(d, r) { .data = (unsigned char*) d, .result = (unsigned char*) r, .datalen = 8 * (sizeof(d) - 1), }
#define TN(n, d, r) { .data = (unsigned char*) d, .result = (unsigned char*) r, .datalen = n, }

static struct {
	unsigned char *data, *result;
	size_t datalen;
} tests256[] = {
#include "short_test_256_data.h"
#include "long_test_256_data.h"
};

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
} tests1024[] = {
#include "short_test_1024_data.h"
#include "long_test_1024_data.h"
};

#define ITEMS(array) (sizeof(array)/sizeof(array[0]))

int main(void)
{
	BitSequence hash256[256 / 8];
	BitSequence hash512[512 / 8];
	BitSequence hash1024[1024 / 8];
	int i;
	int result = 0;

	for (i = 0; i < ITEMS(tests256); i++) {
		Hash(256, tests256[i].data, tests256[i].datalen, hash256);
		if (memcmp(tests256[i].result, hash256, sizeof(hash256))) {
			printf("FAIL 256bit: %d!\n", i);
			result = 1;
                }
	}

	for (i = 0; i < ITEMS(tests512); i++) {
		Hash(512, tests512[i].data, tests512[i].datalen, hash512);
		if (memcmp(tests512[i].result, hash512, sizeof(hash512))) {
			printf("FAIL 512bit: %d!\n", i);
			result = 1;
                }
	}

	for (i = 0; i < ITEMS(tests1024); i++) {
		Hash(1024, tests1024[i].data, tests1024[i].datalen, hash1024);
		if (memcmp(tests1024[i].result, hash1024, sizeof(hash1024))) {
			printf("FAIL 1024bit: %d!\n", i);
			result = 1;
                }
	}

	return result;
}
