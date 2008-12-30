#include "SHA3api_ref.h"
#include <stdio.h>
#include <string.h>

char *data = "blubasdflkjasldkfjlkasjdflkajsdflkjasldkfjd";

int main()
{
	unsigned char hash[512 / 8];
	int i;
	Hash(512, data, strlen(data) * 8, &hash);
	for (i = 0; i < 512 / 8; i++) {
		printf("%02x", hash[i]);
	}
	printf("\n");
	return 0;
}
