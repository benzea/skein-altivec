CFLAGS=-mcpu=G4 -maltivec -O2 -Wall

all: test speed_test

test:  test.o SHA3api_ref.o skein_debug.o skein.o skein_block.o
speed_test:  speed_test.o SHA3api_ref.o skein_debug.o skein.o skein_block.o


clean:
	@rm -f *~ *.o test speed_test

