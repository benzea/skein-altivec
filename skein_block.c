/***********************************************************************
**
** Implementation of the Skein block functions.
**
** Source code author: Doug Whiting, 2008.
** Altivec Optimization: Benjamin Berg, 2008.
**
** This algorithm and source code is released to the public domain.
**
************************************************************************/

/* About the Altivec Optimization (512 bit case)
 * 
 * Altivec has 32 128bit registers, which can be used as 8, 16 or 32 bit
 * integers, or 32/64 bit floating point values. Altivec does not support
 * 64bit operations natively, but we can still do two 64 bit calculations
 * at the same time with some tricks.
 *
 * The important part here is to note that the state has two different kinds of
 * words. There are eight 64bit values, but 4 (the even ones) are always
 * used as the target for the addition, and the other 4 (the odd ones) are the
 * target of the xor (and are shifted).
 * Now this does not lend to the way that altivec works, because an even and
 * odd value would end up in the same register, and we cannot perform the same
 * operation on both words. However, we can change the order:
 * (Brackets show which values are together in a vector.)
 *  Instead of:  (0, 1), (2, 3), (4, 5), (6, 7)
 *  we use:      (0, 2), (4, 6), (1, 3), (5, 7)
 * Now the old algorithm:
 *  0 = 0 + 1;
 *  2 = 2 + 3;
 *  rotate(1, a);
 *  rotate(3, b);
 *  1 = 0 ^ 1
 *  3 = 2 ^ 3
 * can be replaced with:
 *  v0 = v0 + v2;
 *  rotate(v2, a, b);
 *  v0 = v0 ^ v2;
 *
 * If we now look at the different steps, we notice that the calculations always
 * looks the same. The words in the first two vectors are always the
 * destination of the addition, and the words of the last two vectors the
 * destination for the xor and rotate. The difference between each run is that
 * the words in the last two vectors are swapped.
 *
 * So in the first round the vectors are:
 *   (0, 2), (4, 6), (1, 3), (5, 7)
 * second:
 *   (0, 2), (4, 6), (3, 1), (7, 5)
 * third:
 *   (0, 2), (4, 6), (5, 7), (1, 3)
 * fourth:
 *   (0, 2), (4, 6), (7, 5), (3, 1)
 * key injection (which needs to be adjusted because of the different order):
 *   (0, 2), (4, 6), (1, 3), (5, 7)
 * 
 * This shows that after each step, we permute the values in the last two vectors
 * and then run the exact same code again.
 *
 * Speed
 * =====
 *
 * In performance tests on a PowerBook G4 1.6 GHz, the code (optimized for
 * the G4) achieves a hash performance of about 35 MByte/s, or about
 * 45 cycles/byte. This is more than 10 times faster than the simple
 * non-optimized code that GCC creates. However, my guess is that optimized
 * assembler for powerpc, that does not use the altivec unit, will not be much
 * slower than the altivec code.
 *   * 64 bit add in normal powerpc: 2 instructions
 *   * 64 bit rotate in normal powerpc: should be 8 instructions
 *                                      (GCC does *much* worst than this)
 *   * 64 bit xor: 2 instructions
 */


#include <string.h>
#include "skein.h"


#include <altivec.h>

/* 64bit Altivec calculation macros */
#define add64_vectors	vector unsigned char carry_mov = {0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0};
/* 64bit add in 4 instructions, should need 3 cycles by itself, but could be
 * less if the compiler reorders instructions. */
#define vec_add64(a, b) ({ \
	vector unsigned int __result;					\
	vector unsigned int __carry;					\
									\
	__carry = vec_addc(a, b);					\
	__carry = vec_perm(__carry, __carry, carry_mov);		\
	__result = vec_add(a, b);					\
	__result = vec_add(__carry, __result);				\
	__result;})

/* vec_rotl64 also needs perm_load_upper! */
#define rotl64_vectors												\
	vector unsigned char perm_load_a = {0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7};			\
	vector unsigned char perm_load_b = {8, 9, 10, 11, 12, 13, 14, 15, 8, 9, 10, 11, 12, 13, 14, 15};

/* Two 64bit left rotations in a 128bit Vector. These two rotations are
 * independent of each other. The rotation needs to be a constant (as the
 * values are stored in immediates for the instructions).
 *
 * This calculation needs 3-9 instructions (most of the time 9). All
 * instructions are in the VPERM unit except for the splat ones. (May differ
 * on some machines.) So this code should need 7, or less cycles (if interleaved
 * with other calculations and/or some of the instructions are not needed.
 **/
#define vec_rotl64(input, rot_a, rot_b)					\
{									\
	vector unsigned char _tmp1, _tmp2;				\
	vector unsigned int _a, _b;					\
									\
	_a = vec_perm(input, input, perm_load_a);			\
	_b = vec_perm(input, input, perm_load_b);			\
									\
	if ((rot_a) >> 3 != 0) {					\
		_a = vec_sld(_a, _a, (rot_a) >> 3);			\
	}								\
	if ((rot_b) >> 3 != 0) {					\
		_b = vec_sld(_b, _b, (rot_b) >> 3);			\
	}								\
									\
	if ((rot_a) % 8 != 0) {						\
		_tmp1 = vec_splat_u8((rot_a) % 8);			\
		_a = vec_sll(_a, _tmp1);				\
	}								\
									\
	if ((rot_b) % 8 != 0) {						\
		_tmp2 = vec_splat_u8((rot_b) % 8);			\
		_b = vec_sll(_b, _tmp2);				\
	}								\
									\
	input = vec_perm(_a, _b, perm_load_upper);			\
}




/* 64-bit rotate left */
u64b_t RotL_64(u64b_t x, uint_t N)
{
	return (x << (N & 63)) | (x >> ((64 - N) & 63));
}

#define BLK_BITS    (WCNT*64)

/* macro to perform a key injection (same for all block sizes) */
#define InjectKey(r)                                                \
    for (i=0;i < WCNT;i++)                                          \
         X[i] += ks[((r)+i) % (WCNT+1)];                            \
    X[WCNT-3] += ts[((r)+0) % 3];                                   \
    X[WCNT-2] += ts[((r)+1) % 3];                                   \
    X[WCNT-1] += (r);                    /* avoid slide attacks */  \
    Skein_Show_Round(BLK_BITS,&ctx->h,SKEIN_RND_KEY_INJECT,X);




#define InjectKey_256_altivec(r)					\
	KeyInject_add[0] = ks[((r)+0) % (4+1)];				\
	KeyInject_add[2] = ks[((r)+1) % (4+1)] + ts[((r)+0) % 3];	\
	KeyInject_add[1] = ks[((r)+2) % (4+1)] + ts[((r)+1) % 3];	\
	KeyInject_add[3] = ks[((r)+3) % (4+1)] + (r);			\
									\
	tmp_vec0 = vec_ld(0x00, (unsigned int*) KeyInject_add);		\
	tmp_vec1 = vec_ld(0x10, (unsigned int*) KeyInject_add);		\
	X0 = vec_add64(X0, tmp_vec0);					\
	X1 = vec_add64(X1, tmp_vec1);

#define Skein_Get64_256_altivec(addr)				\
	vector unsigned char __load_vec;			\
								\
	tmp_vec0 = vec_ld(0, (unsigned int*) (addr));		\
	w0 = vec_ld(0x10, (unsigned int*) (addr));		\
	w1 = vec_ld(0x1f, (unsigned int*) (addr));		\
								\
	__load_vec = vec_lvsl(0, (addr));			\
	__load_vec = vec_add(__load_vec, perm_load_swap_endian); \
								\
	w1 = vec_perm(w0, w1, __load_vec);			\
	w0 = vec_perm(tmp_vec0, w0, __load_vec);		\
								\
	/* ALTIVEC ORDER */					\
	tmp_vec0 = w0;						\
	w0 = vec_perm(w0, w1, perm_load_upper);			\
	w1 = vec_perm(tmp_vec0, w1, perm_load_lower);


void Skein_256_Process_Block(Skein_256_Ctxt_t * ctx, const u08b_t * blkPtr,
			     size_t blkCnt, size_t byteCntAdd)
{	/* do it in C with altivec! */
	size_t i, r;
	u64b_t ks[5];
	u64b_t ts[3] __attribute__((aligned(16)));
	u64b_t KeyInject_add[4] __attribute__((aligned(16)));

	/* The Xi is only used for storing the data. */
	u64b_t Xi[4] __attribute__((aligned(16)));

	vector unsigned int X0, X1;
	vector unsigned int w0, w1;

	/* special vectors for the altivec calculations */
	rotl64_vectors
	add64_vectors
	vector unsigned char perm_load_upper = {0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17};
	vector unsigned char perm_load_lower = {0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F};
	vector unsigned char perm_swap_u64 = {8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7};
	/* This vector can be added to a vector produced with vec_lvsl (load vector for shift left), so that
	 * unaligned little endian data, can be aligned *and* byteswapped at the same time. */
	vector char perm_load_swap_endian = {7, 5, 3, 1, -1, -3, -5, -7, 7, 5, 3, 1, -1, -3, -5, -7,};

	vector unsigned int tmp_vec0, tmp_vec1;
	unsigned int dst_control_word = 0x20020020; /* Preload two blocks of 32 bytes each. */

	Skein_assert(blkCnt != 0);	/* never call with blkCnt == 0! */

	Xi[0] = ctx->X[0];
	Xi[1] = ctx->X[1];
	Xi[2] = ctx->X[2];
	Xi[3] = ctx->X[3];

	X0 = vec_ld(0x00, (unsigned int*) Xi);
	X1 = vec_ld(0x10, (unsigned int*) Xi);

	/* ALTIVEC ORDER */
	tmp_vec0 = X0;
	X0 = vec_perm(X0, X1, perm_load_upper);
	X1 = vec_perm(tmp_vec0, X1, perm_load_lower);


	Skein_assert(blkCnt != 0);	/* never call with blkCnt == 0! */
	do {
		u64b_t tmp;

		vec_dst(blkPtr, dst_control_word, 0);

		/* this implementation only supports 2**64 input bytes (no carry out here) */
		ctx->h.T[0] += byteCntAdd;	/* update processed length */

		/* Store ks in normal order. */
		tmp_vec0 = vec_perm(X0, X1, perm_load_upper);
		tmp_vec1 = vec_perm(X0, X1, perm_load_lower);

		vec_st(tmp_vec0, 0x00, (unsigned int*) ks);
		vec_st(tmp_vec1, 0x10, (unsigned int*) ks);

		ks[4] = SKEIN_KS_PARITY;
		ks[4] ^= ks[0];
		ks[4] ^= ks[1];	
		ks[4] ^= ks[2];
		ks[4] ^= ks[3];

		ts[0] = ctx->h.T[0];
		ts[1] = ctx->h.T[1];
		ts[2] = ts[0] ^ ts[1];
		Skein_Get64_256_altivec(blkPtr); /* load input block into w registers */
/*	vec_st(w0, 0x00, (unsigned int*) Xi);
	vec_st(w1, 0x10, (unsigned int*) Xi);
		printf("input: %0.8x%0.8x, %0.8x%0.8x, %0.8x%0.8x, %0.8x%0.8x\n", (unsigned int)(Xi[0] >> 32), (unsigned int)Xi[0], (unsigned int)(Xi[1] >> 32), (unsigned int)Xi[1], (unsigned int)(Xi[2] >> 32), (unsigned int)Xi[2], (unsigned int)(Xi[3] >> 32), (unsigned int)Xi[3]);

	vec_st(X0, 0x00, (unsigned int*) Xi);
	vec_st(X1, 0x10, (unsigned int*) Xi);
		printf("ts: %0.8x%0.8x, %0.8x%0.8x\n", (unsigned int)(ts[0] >> 32), (unsigned int)ts[0], (unsigned int)(ts[1] >> 32), (unsigned int)ts[1]);
		printf("%0.8x%0.8x, %0.8x%0.8x, %0.8x%0.8x, %0.8x%0.8x\n", (unsigned int)(Xi[0] >> 32), (unsigned int)Xi[0], (unsigned int)(Xi[1] >> 32), (unsigned int)Xi[1], (unsigned int)(Xi[2] >> 32), (unsigned int)Xi[2], (unsigned int)(Xi[3] >> 32), (unsigned int)Xi[3]);
*/

		tmp_vec1 = vec_ld(0, (unsigned int*)ts);
		tmp_vec1 = vec_sld(tmp_vec1, tmp_vec1, 8);
		tmp_vec0 = vec_sld(X0, X1, 8);
		tmp_vec0 = vec_add64(tmp_vec0, tmp_vec1);

		X0 = vec_perm(X0, tmp_vec0, perm_load_upper);
		X1 = vec_perm(tmp_vec0, X1, perm_load_lower);

/*	vec_st(X0, 0x00, (unsigned int*) Xi);
	vec_st(X1, 0x10, (unsigned int*) Xi);
		printf("%0.8x%0.8x, %0.8x%0.8x, %0.8x%0.8x, %0.8x%0.8x\n", (unsigned int)(Xi[0] >> 32), (unsigned int)Xi[0], (unsigned int)(Xi[1] >> 32), (unsigned int)Xi[1], (unsigned int)(Xi[2] >> 32), (unsigned int)Xi[2], (unsigned int)(Xi[3] >> 32), (unsigned int)Xi[3]);
*/
		X0 = vec_add64(X0, w0);
		X1 = vec_add64(X1, w1);

		for (r = 1; r <= SKEIN_256_ROUNDS_TOTAL / 8; r++) {	/* unroll 8 rounds */
			X0 = vec_add64(X0, X1);
			vec_rotl64(X1, R_256_0_0, R_256_0_1);
			X1 = vec_xor(X1, X0);

			X1 = vec_perm(X1, X1, perm_swap_u64);

			X0 = vec_add64(X0, X1);
			vec_rotl64(X1, R_256_1_0, R_256_1_1);
			X1 = vec_xor(X1, X0);

			X1 = vec_perm(X1, X1, perm_swap_u64);

			X0 = vec_add64(X0, X1);
			vec_rotl64(X1, R_256_2_0, R_256_2_1);
			X1 = vec_xor(X1, X0);

			X1 = vec_perm(X1, X1, perm_swap_u64);

			X0 = vec_add64(X0, X1);
			vec_rotl64(X1, R_256_3_0, R_256_3_1);
			X1 = vec_xor(X1, X0);

			X1 = vec_perm(X1, X1, perm_swap_u64);

			InjectKey_256_altivec(2 * r - 1);

			/* 0,1; 2,3*/
			X0 = vec_add64(X0, X1);
			vec_rotl64(X1, R_256_4_0, R_256_4_1);
			X1 = vec_xor(X1, X0);

			X1 = vec_perm(X1, X1, perm_swap_u64);

			X0 = vec_add64(X0, X1);
			vec_rotl64(X1, R_256_5_0, R_256_5_1);
			X1 = vec_xor(X1, X0);

			X1 = vec_perm(X1, X1, perm_swap_u64);

			X0 = vec_add64(X0, X1);
			vec_rotl64(X1, R_256_6_0, R_256_6_1);
			X1 = vec_xor(X1, X0);

			X1 = vec_perm(X1, X1, perm_swap_u64);

			X0 = vec_add64(X0, X1);
			vec_rotl64(X1, R_256_7_0, R_256_7_1);
			X1 = vec_xor(X1, X0);

			X1 = vec_perm(X1, X1, perm_swap_u64);

			InjectKey_256_altivec(2 * r);
		}
		/* do the final "feedforward" xor, update context chaining vars */
		X0 = vec_xor(X0, w0);
		X1 = vec_xor(X1, w1);

		Skein_Clear_First_Flag(ctx->h);	/* clear the start bit */
		blkPtr += SKEIN_256_BLOCK_BYTES;
	} while (--blkCnt);

	/* UNDO ALTIVEC ORDER */
	tmp_vec0 = X0;
	X0 = vec_perm(X0, X1, perm_load_upper);
	X1 = vec_perm(tmp_vec0, X1, perm_load_lower);

	vec_st(X0, 0x00, (unsigned int*) Xi);
	vec_st(X1, 0x10, (unsigned int*) Xi);

	vec_dss(0);

	ctx->X[0] = Xi[0];
	ctx->X[1] = Xi[1];
	ctx->X[2] = Xi[2];
	ctx->X[3] = Xi[3];
}

#undef InjectKey_256_altivec
#undef Skein_Get64_256_altivec

#if defined(SKEIN_CODE_SIZE) || defined(SKEIN_PERF)
size_t Skein_256_Process_Block_CodeSize(void)
{
	return ((u08b_t *) Skein_256_Process_Block_CodeSize) -
	    ((u08b_t *) Skein_256_Process_Block);
}

uint_t Skein_256_Unroll_Cnt(void)
{
	return 1;
}
#endif

#define InjectKey_512_altivec(r)					\
	KeyInject_add[0] = ks[((r)+0) % (8+1)];				\
	KeyInject_add[4] = ks[((r)+1) % (8+1)];				\
	KeyInject_add[1] = ks[((r)+2) % (8+1)];				\
	KeyInject_add[5] = ks[((r)+3) % (8+1)];				\
	KeyInject_add[2] = ks[((r)+4) % (8+1)];				\
	KeyInject_add[6] = ks[((r)+5) % (8+1)] + ts[((r)+0) % 3];	\
	KeyInject_add[3] = ks[((r)+6) % (8+1)] + ts[((r)+1) % 3];	\
	KeyInject_add[7] = ks[((r)+7) % (8+1)] + (r);			\
									\
	tmp_vec0 = vec_ld(0x00, (unsigned int*) KeyInject_add);		\
	tmp_vec1 = vec_ld(0x10, (unsigned int*) KeyInject_add);		\
	tmp_vec2 = vec_ld(0x20, (unsigned int*) KeyInject_add);		\
	tmp_vec3 = vec_ld(0x30, (unsigned int*) KeyInject_add);		\
	X0 = vec_add64(X0, tmp_vec0);					\
	X1 = vec_add64(X1, tmp_vec1);					\
	X2 = vec_add64(X2, tmp_vec2);					\
	X3 = vec_add64(X3, tmp_vec3);					\

#define Skein_Get64_512_altivec(addr)				\
	vector unsigned char __load_vec;			\
								\
	tmp_vec0 = vec_ld(0, (unsigned int*) (addr));		\
	w0 = vec_ld(0x10, (unsigned int*) (addr));		\
	w1 = vec_ld(0x20, (unsigned int*) (addr));		\
	w2 = vec_ld(0x30, (unsigned int*) (addr));		\
	w3 = vec_ld(0x3f, (unsigned int*) (addr));		\
								\
	__load_vec = vec_lvsl(0, (addr));			\
	__load_vec = vec_add(__load_vec, perm_load_swap_endian); \
								\
	w3 = vec_perm(w2, w3, __load_vec);			\
	w2 = vec_perm(w1, w2, __load_vec);			\
	w1 = vec_perm(w0, w1, __load_vec);			\
	w0 = vec_perm(tmp_vec0, w0, __load_vec);		\
								\
	/* ALTIVEC ORDER */					\
	tmp_vec0 = w0;						\
	w0 = vec_perm(w0, w1, perm_load_upper);			\
	tmp_vec1 = w1;						\
	w1 = vec_perm(w2, w3, perm_load_upper);			\
	tmp_vec2 = w2;						\
	w2 = vec_perm(tmp_vec0, tmp_vec1, perm_load_lower);	\
	w3 = vec_perm(tmp_vec2, w3, perm_load_lower);


void Skein_512_Process_Block(Skein_512_Ctxt_t * ctx, const u08b_t * blkPtr,
			     size_t blkCnt, size_t byteCntAdd)
{	/* do it in C with altivec! */
	size_t i, r;
	u64b_t ks[9];
	u64b_t ts[3] __attribute__((aligned(16)));
	u64b_t KeyInject_add[8] __attribute__((aligned(16)));

	/* The Xi is only used for storing the data. */
	u64b_t Xi[8] __attribute__((aligned(16)));

	vector unsigned int X0, X1, X2, X3;
	vector unsigned int w0, w1, w2, w3;

	/* special vectors for the altivec calculations */
	rotl64_vectors
	add64_vectors
	vector unsigned char perm_load_upper = {0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17};
	vector unsigned char perm_load_lower = {0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F};
	vector unsigned char perm_swap_u64 = {8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7};
	/* This vector can be added to a vector produced with vec_lvsl (load vector for shift left), so that
	 * unaligned little endian data, can be aligned *and* byteswapped at the same time. */
	vector char perm_load_swap_endian = {7, 5, 3, 1, -1, -3, -5, -7, 7, 5, 3, 1, -1, -3, -5, -7,};

	vector unsigned int tmp_vec0, tmp_vec1, tmp_vec2, tmp_vec3;
	unsigned int dst_control_word = 0x40020040; /* Preload two blocks of 64 bytes each. */

	Skein_assert(blkCnt != 0);	/* never call with blkCnt == 0! */

	Xi[0] = ctx->X[0];
	Xi[1] = ctx->X[1];
	Xi[2] = ctx->X[2];
	Xi[3] = ctx->X[3];
	Xi[4] = ctx->X[4];
	Xi[5] = ctx->X[5];
	Xi[6] = ctx->X[6];
	Xi[7] = ctx->X[7];

	X0 = vec_ld(0x00, (unsigned int*) Xi);
	X1 = vec_ld(0x10, (unsigned int*) Xi);
	X2 = vec_ld(0x20, (unsigned int*) Xi);
	X3 = vec_ld(0x30, (unsigned int*) Xi);

	/* ALTIVEC ORDER */
	tmp_vec0 = X0;
	X0 = vec_perm(X0, X1, perm_load_upper);
	tmp_vec1 = X1;
	X1 = vec_perm(X2, X3, perm_load_upper);
	tmp_vec2 = X2;
	X2 = vec_perm(tmp_vec0, tmp_vec1, perm_load_lower);
	X3 = vec_perm(tmp_vec2, X3, perm_load_lower);

	do {
		u64b_t tmp;

		vec_dst(blkPtr, dst_control_word, 0);

		/* this implementation only supports 2**64 input bytes (no carry out here) */
		ctx->h.T[0] += byteCntAdd;	/* update processed length */

		/* Store ks in normal order. */
		tmp_vec0 = vec_perm(X0, X2, perm_load_upper);
		tmp_vec1 = vec_perm(X0, X2, perm_load_lower);
		tmp_vec2 = vec_perm(X1, X3, perm_load_upper);
		tmp_vec3 = vec_perm(X1, X3, perm_load_lower);

		ks[8] = SKEIN_KS_PARITY;
		vec_st(tmp_vec0, 0x00, (unsigned int*) ks);
		ks[8] ^= ks[0];
		ks[8] ^= ks[1];	
		vec_st(tmp_vec1, 0x10, (unsigned int*) ks);
		ks[8] ^= ks[2];
		ks[8] ^= ks[3];
		vec_st(tmp_vec2, 0x20, (unsigned int*) ks);
		ks[8] ^= ks[4];
		ks[8] ^= ks[5];
		vec_st(tmp_vec3, 0x30, (unsigned int*) ks);
		ks[8] ^= ks[6];
		ks[8] ^= ks[7];

		ts[0] = ctx->h.T[0];
		ts[1] = ctx->h.T[1];
		ts[2] = ts[0] ^ ts[1];
		Skein_Get64_512_altivec(blkPtr); /* load input block into w[] registers */

		tmp_vec2 = vec_ld(0, (unsigned int*)ts);
		tmp_vec0 = vec_sld(X1, X3, 8);
		tmp_vec1 = vec_sld(tmp_vec2, tmp_vec2, 8);
		tmp_vec0 = vec_add64(tmp_vec0, tmp_vec1);
		
		X1 = vec_perm(X1, tmp_vec0, perm_load_upper);
		X3 = vec_perm(tmp_vec0, X3, perm_load_lower);

		X0 = vec_add64(X0, w0);
		X1 = vec_add64(X1, w1);
		X2 = vec_add64(X2, w2);
		X3 = vec_add64(X3, w3);

		for (r = 1; r <= SKEIN_512_ROUNDS_TOTAL / 8; r++) { /* unroll 8 rounds */
			X0 = vec_add64(X0, X2);
			X1 = vec_add64(X1, X3);
			vec_rotl64(X2, R_512_0_0, R_512_0_1);
			vec_rotl64(X3, R_512_0_2, R_512_0_3);
			X2 = vec_xor(X2, X0);
			X3 = vec_xor(X3, X1);

			X2 = vec_perm(X2, X2, perm_swap_u64);
			X3 = vec_perm(X3, X3, perm_swap_u64);

			X0 = vec_add64(X0, X2);
			X1 = vec_add64(X1, X3);
			vec_rotl64(X2, R_512_1_3, R_512_1_0);
			vec_rotl64(X3, R_512_1_1, R_512_1_2);
			X2 = vec_xor(X2, X0);
			X3 = vec_xor(X3, X1);

			tmp_vec0 = X2;
			X2 = vec_perm(X3, X3, perm_swap_u64);
			X3 = vec_perm(tmp_vec0, tmp_vec0, perm_swap_u64);

			X0 = vec_add64(X0, X2);
			X1 = vec_add64(X1, X3);
			vec_rotl64(X2, R_512_2_2, R_512_2_3);
			vec_rotl64(X3, R_512_2_0, R_512_2_1);
			X2 = vec_xor(X2, X0);
			X3 = vec_xor(X3, X1);

			X2 = vec_perm(X2, X2, perm_swap_u64);
			X3 = vec_perm(X3, X3, perm_swap_u64);

			X0 = vec_add64(X0, X2);
			X1 = vec_add64(X1, X3);
			vec_rotl64(X2, R_512_3_1, R_512_3_2);
			vec_rotl64(X3, R_512_3_3, R_512_3_0);
			X2 = vec_xor(X2, X0);
			X3 = vec_xor(X3, X1);

			tmp_vec0 = X2;
			X2 = vec_perm(X3, X3, perm_swap_u64);
			X3 = vec_perm(tmp_vec0, tmp_vec0, perm_swap_u64);

			InjectKey_512_altivec(2 * r - 1);

			X0 = vec_add64(X0, X2);
			X1 = vec_add64(X1, X3);
			vec_rotl64(X2, R_512_4_0, R_512_4_1);
			vec_rotl64(X3, R_512_4_2, R_512_4_3);
			X2 = vec_xor(X2, X0);
			X3 = vec_xor(X3, X1);

			X2 = vec_perm(X2, X2, perm_swap_u64);
			X3 = vec_perm(X3, X3, perm_swap_u64);

			X0 = vec_add64(X0, X2);
			X1 = vec_add64(X1, X3);
			vec_rotl64(X2, R_512_5_3, R_512_5_0);
			vec_rotl64(X3, R_512_5_1, R_512_5_2);
			X2 = vec_xor(X2, X0);
			X3 = vec_xor(X3, X1);

			tmp_vec0 = X2;
			X2 = vec_perm(X3, X3, perm_swap_u64);
			X3 = vec_perm(tmp_vec0, tmp_vec0, perm_swap_u64);

			X0 = vec_add64(X0, X2);
			X1 = vec_add64(X1, X3);
			vec_rotl64(X2, R_512_6_2, R_512_6_3);
			vec_rotl64(X3, R_512_6_0, R_512_6_1);
			X2 = vec_xor(X2, X0);
			X3 = vec_xor(X3, X1);

			X2 = vec_perm(X2, X2, perm_swap_u64);
			X3 = vec_perm(X3, X3, perm_swap_u64);

			X0 = vec_add64(X0, X2);
			X1 = vec_add64(X1, X3);
			vec_rotl64(X2, R_512_7_1, R_512_7_2);
			vec_rotl64(X3, R_512_7_3, R_512_7_0);
			X2 = vec_xor(X2, X0);
			X3 = vec_xor(X3, X1);

			tmp_vec0 = X2;
			X2 = vec_perm(X3, X3, perm_swap_u64);
			X3 = vec_perm(tmp_vec0, tmp_vec0, perm_swap_u64);

			InjectKey_512_altivec(2 * r);
		}

		/* do the final "feedforward" xor, update context chaining vars */
		X0 = vec_xor(X0, w0);
		X1 = vec_xor(X1, w1);
		X2 = vec_xor(X2, w2);
		X3 = vec_xor(X3, w3);

		Skein_Clear_First_Flag(ctx->h);	/* clear the start bit */
		blkPtr += SKEIN_512_BLOCK_BYTES;
	} while (--blkCnt);

	/* UNDO ALTIVEC ORDER */
	tmp_vec0 = X0;
	X0 = vec_perm(X0, X2, perm_load_upper);
	tmp_vec1 = X1;
	X1 = vec_perm(tmp_vec0, X2, perm_load_lower);
	X2 = vec_perm(tmp_vec1, X3, perm_load_upper);
	X3 = vec_perm(tmp_vec1, X3, perm_load_lower);

	vec_st(X0, 0x00, (unsigned int*) Xi);
	vec_st(X1, 0x10, (unsigned int*) Xi);
	vec_st(X2, 0x20, (unsigned int*) Xi);
	vec_st(X3, 0x30, (unsigned int*) Xi);

	vec_dss(0);

	ctx->X[0] = Xi[0];
	ctx->X[1] = Xi[1];
	ctx->X[2] = Xi[2];
	ctx->X[3] = Xi[3];
	ctx->X[4] = Xi[4];
	ctx->X[5] = Xi[5];
	ctx->X[6] = Xi[6];
	ctx->X[7] = Xi[7];
}

#undef InjectKey_512_altivec
#undef Skein_Get64_512_Altivec

#if defined(SKEIN_CODE_SIZE) || defined(SKEIN_PERF)
size_t Skein_512_Process_Block_CodeSize(void)
{
	return ((u08b_t *) Skein_512_Process_Block_CodeSize) -
	    ((u08b_t *) Skein_512_Process_Block);
}

uint_t Skein_512_Unroll_Cnt(void)
{
	return 1;
}
#endif

void Skein1024_Process_Block(Skein1024_Ctxt_t * ctx, const u08b_t * blkPtr,
			     size_t blkCnt, size_t byteCntAdd)
{				/* do it in C */
	enum {
		WCNT = SKEIN1024_STATE_WORDS
	};

	size_t i, r;
	u64b_t ts[3];		/* key schedule: tweak */
	u64b_t ks[WCNT + 1];	/* key schedule: chaining vars */
	u64b_t X[WCNT];		/* local copy of vars */
	u64b_t w[WCNT];		/* local copy of input block */

	Skein_assert(blkCnt != 0);	/* never call with blkCnt == 0! */
	do {
		/* this implementation only supports 2**64 input bytes (no carry out here) */
		ctx->h.T[0] += byteCntAdd;	/* update processed length */

		/* precompute the key schedule for this block */
		ks[WCNT] = SKEIN_KS_PARITY;
		for (i = 0; i < WCNT; i++) {
			ks[i] = ctx->X[i];
			ks[WCNT] ^= ctx->X[i];	/* compute overall parity */
		}
		ts[0] = ctx->h.T[0];
		ts[1] = ctx->h.T[1];
		ts[2] = ts[0] ^ ts[1];

		Skein_Get64_LSB_First(w, blkPtr, WCNT);	/* get input block in little-endian format */
		Skein_Show_Block(BLK_BITS, &ctx->h, ctx->X, blkPtr, w, ks, ts);
		for (i = 0; i < WCNT; i++) {	/* do the first full key injection */
			X[i] = w[i] + ks[i];
		}
		X[WCNT - 3] += ts[0];
		X[WCNT - 2] += ts[1];

		Skein_Show_Round(BLK_BITS, &ctx->h, SKEIN_RND_KEY_INITIAL, X);	/* show starting state values */
		for (r = 1; r <= SKEIN1024_ROUNDS_TOTAL / 8; r++) {	/* unroll 8 rounds */
			X[0] += X[1];
			X[1] = RotL_64(X[1], R1024_0_0);
			X[1] ^= X[0];
			X[2] += X[3];
			X[3] = RotL_64(X[3], R1024_0_1);
			X[3] ^= X[2];
			X[4] += X[5];
			X[5] = RotL_64(X[5], R1024_0_2);
			X[5] ^= X[4];
			X[6] += X[7];
			X[7] = RotL_64(X[7], R1024_0_3);
			X[7] ^= X[6];
			X[8] += X[9];
			X[9] = RotL_64(X[9], R1024_0_4);
			X[9] ^= X[8];
			X[10] += X[11];
			X[11] = RotL_64(X[11], R1024_0_5);
			X[11] ^= X[10];
			X[12] += X[13];
			X[13] = RotL_64(X[13], R1024_0_6);
			X[13] ^= X[12];
			X[14] += X[15];
			X[15] = RotL_64(X[15], R1024_0_7);
			X[15] ^= X[14];
			Skein_Show_Round(BLK_BITS, &ctx->h, 8 * r - 7, X);

			X[0] += X[9];
			X[9] = RotL_64(X[9], R1024_1_0);
			X[9] ^= X[0];
			X[2] += X[13];
			X[13] = RotL_64(X[13], R1024_1_1);
			X[13] ^= X[2];
			X[6] += X[11];
			X[11] = RotL_64(X[11], R1024_1_2);
			X[11] ^= X[6];
			X[4] += X[15];
			X[15] = RotL_64(X[15], R1024_1_3);
			X[15] ^= X[4];
			X[10] += X[7];
			X[7] = RotL_64(X[7], R1024_1_4);
			X[7] ^= X[10];
			X[12] += X[3];
			X[3] = RotL_64(X[3], R1024_1_5);
			X[3] ^= X[12];
			X[14] += X[5];
			X[5] = RotL_64(X[5], R1024_1_6);
			X[5] ^= X[14];
			X[8] += X[1];
			X[1] = RotL_64(X[1], R1024_1_7);
			X[1] ^= X[8];
			Skein_Show_Round(BLK_BITS, &ctx->h, 8 * r - 6, X);

			X[0] += X[7];
			X[7] = RotL_64(X[7], R1024_2_0);
			X[7] ^= X[0];
			X[2] += X[5];
			X[5] = RotL_64(X[5], R1024_2_1);
			X[5] ^= X[2];
			X[4] += X[3];
			X[3] = RotL_64(X[3], R1024_2_2);
			X[3] ^= X[4];
			X[6] += X[1];
			X[1] = RotL_64(X[1], R1024_2_3);
			X[1] ^= X[6];
			X[12] += X[15];
			X[15] = RotL_64(X[15], R1024_2_4);
			X[15] ^= X[12];
			X[14] += X[13];
			X[13] = RotL_64(X[13], R1024_2_5);
			X[13] ^= X[14];
			X[8] += X[11];
			X[11] = RotL_64(X[11], R1024_2_6);
			X[11] ^= X[8];
			X[10] += X[9];
			X[9] = RotL_64(X[9], R1024_2_7);
			X[9] ^= X[10];
			Skein_Show_Round(BLK_BITS, &ctx->h, 8 * r - 5, X);

			X[0] += X[15];
			X[15] = RotL_64(X[15], R1024_3_0);
			X[15] ^= X[0];
			X[2] += X[11];
			X[11] = RotL_64(X[11], R1024_3_1);
			X[11] ^= X[2];
			X[6] += X[13];
			X[13] = RotL_64(X[13], R1024_3_2);
			X[13] ^= X[6];
			X[4] += X[9];
			X[9] = RotL_64(X[9], R1024_3_3);
			X[9] ^= X[4];
			X[14] += X[1];
			X[1] = RotL_64(X[1], R1024_3_4);
			X[1] ^= X[14];
			X[8] += X[5];
			X[5] = RotL_64(X[5], R1024_3_5);
			X[5] ^= X[8];
			X[10] += X[3];
			X[3] = RotL_64(X[3], R1024_3_6);
			X[3] ^= X[10];
			X[12] += X[7];
			X[7] = RotL_64(X[7], R1024_3_7);
			X[7] ^= X[12];
			Skein_Show_Round(BLK_BITS, &ctx->h, 8 * r - 4, X);
			InjectKey(2 * r - 1);

			X[0] += X[1];
			X[1] = RotL_64(X[1], R1024_4_0);
			X[1] ^= X[0];
			X[2] += X[3];
			X[3] = RotL_64(X[3], R1024_4_1);
			X[3] ^= X[2];
			X[4] += X[5];
			X[5] = RotL_64(X[5], R1024_4_2);
			X[5] ^= X[4];
			X[6] += X[7];
			X[7] = RotL_64(X[7], R1024_4_3);
			X[7] ^= X[6];
			X[8] += X[9];
			X[9] = RotL_64(X[9], R1024_4_4);
			X[9] ^= X[8];
			X[10] += X[11];
			X[11] = RotL_64(X[11], R1024_4_5);
			X[11] ^= X[10];
			X[12] += X[13];
			X[13] = RotL_64(X[13], R1024_4_6);
			X[13] ^= X[12];
			X[14] += X[15];
			X[15] = RotL_64(X[15], R1024_4_7);
			X[15] ^= X[14];
			Skein_Show_Round(BLK_BITS, &ctx->h, 8 * r - 3, X);

			X[0] += X[9];
			X[9] = RotL_64(X[9], R1024_5_0);
			X[9] ^= X[0];
			X[2] += X[13];
			X[13] = RotL_64(X[13], R1024_5_1);
			X[13] ^= X[2];
			X[6] += X[11];
			X[11] = RotL_64(X[11], R1024_5_2);
			X[11] ^= X[6];
			X[4] += X[15];
			X[15] = RotL_64(X[15], R1024_5_3);
			X[15] ^= X[4];
			X[10] += X[7];
			X[7] = RotL_64(X[7], R1024_5_4);
			X[7] ^= X[10];
			X[12] += X[3];
			X[3] = RotL_64(X[3], R1024_5_5);
			X[3] ^= X[12];
			X[14] += X[5];
			X[5] = RotL_64(X[5], R1024_5_6);
			X[5] ^= X[14];
			X[8] += X[1];
			X[1] = RotL_64(X[1], R1024_5_7);
			X[1] ^= X[8];
			Skein_Show_Round(BLK_BITS, &ctx->h, 8 * r - 2, X);

			X[0] += X[7];
			X[7] = RotL_64(X[7], R1024_6_0);
			X[7] ^= X[0];
			X[2] += X[5];
			X[5] = RotL_64(X[5], R1024_6_1);
			X[5] ^= X[2];
			X[4] += X[3];
			X[3] = RotL_64(X[3], R1024_6_2);
			X[3] ^= X[4];
			X[6] += X[1];
			X[1] = RotL_64(X[1], R1024_6_3);
			X[1] ^= X[6];
			X[12] += X[15];
			X[15] = RotL_64(X[15], R1024_6_4);
			X[15] ^= X[12];
			X[14] += X[13];
			X[13] = RotL_64(X[13], R1024_6_5);
			X[13] ^= X[14];
			X[8] += X[11];
			X[11] = RotL_64(X[11], R1024_6_6);
			X[11] ^= X[8];
			X[10] += X[9];
			X[9] = RotL_64(X[9], R1024_6_7);
			X[9] ^= X[10];
			Skein_Show_Round(BLK_BITS, &ctx->h, 8 * r - 1, X);

			X[0] += X[15];
			X[15] = RotL_64(X[15], R1024_7_0);
			X[15] ^= X[0];
			X[2] += X[11];
			X[11] = RotL_64(X[11], R1024_7_1);
			X[11] ^= X[2];
			X[6] += X[13];
			X[13] = RotL_64(X[13], R1024_7_2);
			X[13] ^= X[6];
			X[4] += X[9];
			X[9] = RotL_64(X[9], R1024_7_3);
			X[9] ^= X[4];
			X[14] += X[1];
			X[1] = RotL_64(X[1], R1024_7_4);
			X[1] ^= X[14];
			X[8] += X[5];
			X[5] = RotL_64(X[5], R1024_7_5);
			X[5] ^= X[8];
			X[10] += X[3];
			X[3] = RotL_64(X[3], R1024_7_6);
			X[3] ^= X[10];
			X[12] += X[7];
			X[7] = RotL_64(X[7], R1024_7_7);
			X[7] ^= X[12];
			Skein_Show_Round(BLK_BITS, &ctx->h, 8 * r, X);
			InjectKey(2 * r);
		}
		/* do the final "feedforward" xor, update context chaining vars */
		for (i = 0; i < WCNT; i++)
			ctx->X[i] = X[i] ^ w[i];
		Skein_Show_Round(BLK_BITS, &ctx->h, SKEIN_RND_FEED_FWD, ctx->X);

		Skein_Clear_First_Flag(ctx->h);	/* clear the start bit */
		blkPtr += SKEIN1024_BLOCK_BYTES;
	}
	while (--blkCnt);
}

#if defined(SKEIN_CODE_SIZE) || defined(SKEIN_PERF)
size_t Skein1024_Process_Block_CodeSize(void)
{
	return ((u08b_t *) Skein1024_Process_Block_CodeSize) -
	    ((u08b_t *) Skein1024_Process_Block);
}

uint_t Skein1024_Unroll_Cnt(void)
{
	return 1;
}
#endif
