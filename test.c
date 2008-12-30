#include "SHA3api_ref.h"
#include <stdio.h>
#include <string.h>

#define T(d, r)	{ .data = d, .result = r, .datalen = sizeof(d) - 1, }

struct {
	unsigned char *data, *result;
	size_t datalen;
} tests[] = {
	T("\xff",
	  "\x8F\xCA\x8D\x27\x05\xF9\x9A\x56\x90\x43\x08\xA4\x00\x4C\x64\xEF\xB6\x68\x81\x8B\x58\xB0\x89\x5B\xF7\x29\x6A\x2C\x5A\x54\xF9\x30\x14\x83\xD6\x22\xC4\xA5\xAE\xC8\x55\xAC\x30\x08\x7E\x1E\xB0\xE8\x39\x40\x90\x6E\x7B\x05\x5D\x70\xD4\x46\xC8\xD2\x85\xF2\x7F\x01"),
};

#define NT (sizeof(tests)/sizeof(tests[0]))

int main()
{
	BitSequence hash[512 / 8];
	int i;
	for (i = 0; i < NT; i++) {
		Hash(512, tests[i].data, 8 * tests[i].datalen, hash);
		if (memcmp(tests[i].result, &hash, sizeof(hash)))
		        printf("FAIL %d!\n", i);
	}
	return 0;
}
