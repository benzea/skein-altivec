/***********************************************************************
**
** Implementation of the Skein block functions.
**
** Source code author: Doug Whiting, 2008.
** Altivec Optimization: Benjamin Berg, 2008, 2009.
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
 *
 *
 * The 256 and 1024 bit implementations are both slightly slower.
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
	tmp_vec0 = vec_ld(0, (unsigned int*) (addr));		\
	w0 = vec_ld(0x10, (unsigned int*) (addr));		\
	w1 = vec_ld(0x1f, (unsigned int*) (addr));		\
								\
	w1 = vec_perm(w0, w1, load_vec);			\
	w0 = vec_perm(tmp_vec0, w0, load_vec);		\
								\
	/* ALTIVEC ORDER */					\
	tmp_vec0 = w0;						\
	w0 = vec_perm(w0, w1, perm_load_upper);			\
	w1 = vec_perm(tmp_vec0, w1, perm_load_lower);


void Skein_256_Process_Block(Skein_256_Ctxt_t * ctx, const u08b_t * blkPtr,
			     size_t blkCnt, size_t byteCntAdd)
{	/* do it in C with altivec! */
	size_t r;
	u64b_t ks[6] __attribute__((aligned(16)));
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
	/* The byte offset of the input data will be added to this (using vec_lvsl).
	 * It is then possible to load the input data, and swap its endianness at
	 * the same time. */
	vector char load_vec = {7, 5, 3, 1, -1, -3, -5, -7, 7, 5, 3, 1, -1, -3, -5, -7,};

	vector unsigned int tmp_vec0, tmp_vec1;
	unsigned int dst_control_word = 0x03020020; /* Preload two blocks of 32 bytes each. */

	tmp_vec0 = (vector unsigned int) vec_lvsl(0, blkPtr);
	load_vec = vec_add((vector char) tmp_vec0, load_vec);

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
		vec_dst(blkPtr, dst_control_word, 0);

		/* this implementation only supports 2**64 input bytes (no carry out here) */
		ctx->h.T[0] += byteCntAdd;	/* update processed length */

		/* Store ks in normal order. */
		tmp_vec0 = vec_perm(X0, X1, perm_load_upper);
		tmp_vec1 = vec_perm(X0, X1, perm_load_lower);

		vec_st(tmp_vec0, 0x00, (unsigned int*) ks);
		vec_st(tmp_vec1, 0x10, (unsigned int*) ks);

		tmp_vec0 = vec_xor(tmp_vec0, tmp_vec1);
		vec_st(tmp_vec0, 0x20, (unsigned int*) ks);

		ks[4] ^= ks[5];
		ks[4] ^= SKEIN_KS_PARITY;

		ts[0] = ctx->h.T[0];
		ts[1] = ctx->h.T[1];
		ts[2] = ts[0] ^ ts[1];
		Skein_Get64_256_altivec(blkPtr); /* load input block into w registers */

		tmp_vec1 = vec_ld(0, (unsigned int*)ts);
		tmp_vec1 = vec_sld(tmp_vec1, tmp_vec1, 8);
		tmp_vec0 = vec_sld(X0, X1, 8);
		tmp_vec0 = vec_add64(tmp_vec0, tmp_vec1);

		X0 = vec_perm(X0, tmp_vec0, perm_load_upper);
		X1 = vec_perm(tmp_vec0, X1, perm_load_lower);

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
		/* do the final "feedforward" xor */
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
	tmp_vec0 = vec_ld(0, (unsigned int*) (addr));		\
	w0 = vec_ld(0x10, (unsigned int*) (addr));		\
	w1 = vec_ld(0x20, (unsigned int*) (addr));		\
	w2 = vec_ld(0x30, (unsigned int*) (addr));		\
	w3 = vec_ld(0x3f, (unsigned int*) (addr));		\
								\
	w3 = vec_perm(w2, w3, load_vec);			\
	w2 = vec_perm(w1, w2, load_vec);			\
	w1 = vec_perm(w0, w1, load_vec);			\
	w0 = vec_perm(tmp_vec0, w0, load_vec);		\
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
	size_t r;
	u64b_t ks[10] __attribute__((aligned(16)));
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
	/* The byte offset of the input data will be added to this (using vec_lvsl).
	 * It is then possible to load the input data, and swap its endianness at
	 * the same time. */
	vector char load_vec = {7, 5, 3, 1, -1, -3, -5, -7, 7, 5, 3, 1, -1, -3, -5, -7,};

	vector unsigned int tmp_vec0, tmp_vec1, tmp_vec2, tmp_vec3;
	unsigned int dst_control_word = 0x05020040; /* Preload two blocks of 64 bytes each. */

	tmp_vec0 = (vector unsigned int) vec_lvsl(0, blkPtr);
	load_vec = vec_add((vector char) tmp_vec0, load_vec);

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
		vec_dst(blkPtr, dst_control_word, 0);

		/* this implementation only supports 2**64 input bytes (no carry out here) */
		ctx->h.T[0] += byteCntAdd;	/* update processed length */

		/* Store ks in normal order. */
		tmp_vec0 = vec_perm(X0, X2, perm_load_upper);
		tmp_vec1 = vec_perm(X0, X2, perm_load_lower);
		tmp_vec2 = vec_perm(X1, X3, perm_load_upper);
		tmp_vec3 = vec_perm(X1, X3, perm_load_lower);

		vec_st(tmp_vec0, 0x00, (unsigned int*) ks);
		vec_st(tmp_vec1, 0x10, (unsigned int*) ks);
		vec_st(tmp_vec2, 0x20, (unsigned int*) ks);
		vec_st(tmp_vec3, 0x30, (unsigned int*) ks);

		tmp_vec0 = vec_xor(tmp_vec0, tmp_vec1);
		tmp_vec0 = vec_xor(tmp_vec0, tmp_vec2);
		tmp_vec0 = vec_xor(tmp_vec0, tmp_vec3);
		vec_st(tmp_vec0, 0x40, (unsigned int*) ks);

		ks[8] ^= ks[9];
		ks[8] ^= SKEIN_KS_PARITY;

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

		/* do the final "feedforward" xor */
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

#define InjectKey_1024_altivec(r)					\
	KeyInject_add[ 0] = ks[((r)+ 0) % (16+1)];			\
	KeyInject_add[ 8] = ks[((r)+ 1) % (16+1)];			\
	KeyInject_add[ 1] = ks[((r)+ 2) % (16+1)];			\
	KeyInject_add[ 9] = ks[((r)+ 3) % (16+1)];			\
	KeyInject_add[ 2] = ks[((r)+ 4) % (16+1)];			\
	KeyInject_add[10] = ks[((r)+ 5) % (16+1)];			\
	KeyInject_add[ 3] = ks[((r)+ 6) % (16+1)];			\
	KeyInject_add[11] = ks[((r)+ 7) % (16+1)];			\
	KeyInject_add[ 4] = ks[((r)+ 8) % (16+1)];			\
	KeyInject_add[12] = ks[((r)+ 9) % (16+1)];			\
	KeyInject_add[ 5] = ks[((r)+10) % (16+1)];			\
	KeyInject_add[13] = ks[((r)+11) % (16+1)];			\
	KeyInject_add[ 6] = ks[((r)+12) % (16+1)];			\
	KeyInject_add[14] = ks[((r)+13) % (16+1)] + ts[((r)+0) % 3];	\
	KeyInject_add[ 7] = ks[((r)+14) % (16+1)] + ts[((r)+1) % 3];	\
	KeyInject_add[15] = ks[((r)+15) % (16+1)] + (r);		\
									\
	tmp_vec0 = vec_ld(0x00, (unsigned int*) KeyInject_add);		\
	tmp_vec1 = vec_ld(0x10, (unsigned int*) KeyInject_add);		\
	tmp_vec2 = vec_ld(0x20, (unsigned int*) KeyInject_add);		\
	tmp_vec3 = vec_ld(0x30, (unsigned int*) KeyInject_add);		\
	tmp_vec4 = vec_ld(0x40, (unsigned int*) KeyInject_add);		\
	tmp_vec5 = vec_ld(0x50, (unsigned int*) KeyInject_add);		\
	tmp_vec6 = vec_ld(0x60, (unsigned int*) KeyInject_add);		\
	tmp_vec7 = vec_ld(0x70, (unsigned int*) KeyInject_add);		\
	X0 = vec_add64(X0, tmp_vec0);					\
	X1 = vec_add64(X1, tmp_vec1);					\
	X2 = vec_add64(X2, tmp_vec2);					\
	X3 = vec_add64(X3, tmp_vec3);					\
	X4 = vec_add64(X4, tmp_vec4);					\
	X5 = vec_add64(X5, tmp_vec5);					\
	X6 = vec_add64(X6, tmp_vec6);					\
	X7 = vec_add64(X7, tmp_vec7);

#define Skein_Get64_1024_altivec(addr)				\
	tmp_vec0 = vec_ld(0, (unsigned int*) (addr));		\
	w0 = vec_ld(0x10, (unsigned int*) (addr));		\
	w1 = vec_ld(0x20, (unsigned int*) (addr));		\
	w2 = vec_ld(0x30, (unsigned int*) (addr));		\
	w3 = vec_ld(0x40, (unsigned int*) (addr));		\
	w4 = vec_ld(0x50, (unsigned int*) (addr));		\
	w5 = vec_ld(0x60, (unsigned int*) (addr));		\
	w6 = vec_ld(0x70, (unsigned int*) (addr));		\
	w7 = vec_ld(0x7f, (unsigned int*) (addr));		\
								\
	w7 = vec_perm(w6, w7, load_vec);			\
	w6 = vec_perm(w5, w6, load_vec);			\
	w5 = vec_perm(w4, w5, load_vec);			\
	w4 = vec_perm(w3, w4, load_vec);			\
	w3 = vec_perm(w2, w3, load_vec);			\
	w2 = vec_perm(w1, w2, load_vec);			\
	w1 = vec_perm(w0, w1, load_vec);			\
	w0 = vec_perm(tmp_vec0, w0, load_vec);			\
								\
	/* ALTIVEC ORDER */					\
	tmp_vec0 = w0;						\
	w0 = vec_perm(w0, w1, perm_load_upper);			\
	tmp_vec1 = w1;						\
	w1 = vec_perm(w2, w3, perm_load_upper);			\
	tmp_vec2 = w2;						\
	w2 = vec_perm(w4, w5, perm_load_upper);			\
	tmp_vec3 = w3;						\
	w3 = vec_perm(w6, w7, perm_load_upper);			\
								\
	tmp_vec4 = w4;						\
	w4 = vec_perm(tmp_vec0, tmp_vec1, perm_load_lower);	\
	tmp_vec5 = w5;						\
	w5 = vec_perm(tmp_vec2, tmp_vec3, perm_load_lower);	\
	tmp_vec6 = w6;						\
	w6 = vec_perm(tmp_vec4, tmp_vec5, perm_load_lower);	\
	w7 = vec_perm(tmp_vec6, w7, perm_load_lower);

void Skein1024_Process_Block(Skein1024_Ctxt_t * ctx, const u08b_t * blkPtr,
			     size_t blkCnt, size_t byteCntAdd)
{	/* do it in C with altivec! */
	size_t r;
	u64b_t ks[18] __attribute__((aligned(16)));
	u64b_t ts[3] __attribute__((aligned(16)));
	u64b_t KeyInject_add[16] __attribute__((aligned(16)));

	/* The Xi is only used for storing the data. */
	u64b_t Xi[16] __attribute__((aligned(16)));

	vector unsigned int X0, X1, X2, X3, X4, X5, X6, X7;
	vector unsigned int w0, w1, w2, w3, w4, w5, w6, w7;

	/* special vectors for the altivec calculations */
	rotl64_vectors
	add64_vectors
	vector unsigned char perm_load_upper = {0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17};
	vector unsigned char perm_load_lower = {0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE, 0xF, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F};
	/* lower_upper can be done with vec_sld */
	vector unsigned char perm_load_upper_lower = {0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F};
	/* The byte offset of the input data will be added to this (using vec_lvsl).
	 * It is then possible to load the input data, and swap its endianness at
	 * the same time. */
	vector char load_vec = {7, 5, 3, 1, -1, -3, -5, -7, 7, 5, 3, 1, -1, -3, -5, -7,};

	vector unsigned int tmp_vec0, tmp_vec1, tmp_vec2, tmp_vec3;
	vector unsigned int tmp_vec4, tmp_vec5, tmp_vec6, tmp_vec7;
	unsigned int dst_control_word = 0x09020080; /* Preload two blocks of 64 bytes each. */

	tmp_vec0 = (vector unsigned int) vec_lvsl(0, blkPtr);
	load_vec = vec_add((vector char) tmp_vec0, load_vec);

	Skein_assert(blkCnt != 0);	/* never call with blkCnt == 0! */

	memcpy(Xi, ctx->X, 8*16);
	
	X0 = vec_ld(0x00, (unsigned int*) Xi);
	X1 = vec_ld(0x10, (unsigned int*) Xi);
	X2 = vec_ld(0x20, (unsigned int*) Xi);
	X3 = vec_ld(0x30, (unsigned int*) Xi);
	X4 = vec_ld(0x40, (unsigned int*) Xi);
	X5 = vec_ld(0x50, (unsigned int*) Xi);
	X6 = vec_ld(0x60, (unsigned int*) Xi);
	X7 = vec_ld(0x70, (unsigned int*) Xi);

	/* ALTIVEC ORDER */
	tmp_vec0 = X0;
	X0 = vec_perm(X0, X1, perm_load_upper);
	tmp_vec1 = X1;
	X1 = vec_perm(X2, X3, perm_load_upper);
	tmp_vec2 = X2;
	X2 = vec_perm(X4, X5, perm_load_upper);
	tmp_vec3 = X3;
	X3 = vec_perm(X6, X7, perm_load_upper);

	tmp_vec4 = X4;
	X4 = vec_perm(tmp_vec0, tmp_vec1, perm_load_lower);
	tmp_vec5 = X5;
	X5 = vec_perm(tmp_vec2, tmp_vec3, perm_load_lower);
	tmp_vec6 = X6;
	X6 = vec_perm(tmp_vec4, tmp_vec5, perm_load_lower);
	X7 = vec_perm(tmp_vec6, X7, perm_load_lower);

	Skein_assert(blkCnt != 0);	/* never call with blkCnt == 0! */
	do {
		vec_dst(blkPtr, dst_control_word, 0);

		/* this implementation only supports 2**64 input bytes (no carry out here) */
		ctx->h.T[0] += byteCntAdd;	/* update processed length */

		/* Store ks in normal order. */
		tmp_vec0 = vec_perm(X0, X4, perm_load_upper);
		tmp_vec1 = vec_perm(X0, X4, perm_load_lower);
		tmp_vec2 = vec_perm(X1, X5, perm_load_upper);
		tmp_vec3 = vec_perm(X1, X5, perm_load_lower);
		tmp_vec4 = vec_perm(X2, X6, perm_load_upper);
		tmp_vec5 = vec_perm(X2, X6, perm_load_lower);
		tmp_vec6 = vec_perm(X3, X7, perm_load_upper);
		tmp_vec7 = vec_perm(X3, X7, perm_load_lower);

		vec_st(tmp_vec0, 0x00, (unsigned int*) ks);
		vec_st(tmp_vec1, 0x10, (unsigned int*) ks);
		vec_st(tmp_vec2, 0x20, (unsigned int*) ks);
		vec_st(tmp_vec3, 0x30, (unsigned int*) ks);
		vec_st(tmp_vec4, 0x40, (unsigned int*) ks);
		vec_st(tmp_vec5, 0x50, (unsigned int*) ks);
		vec_st(tmp_vec6, 0x60, (unsigned int*) ks);
		vec_st(tmp_vec7, 0x70, (unsigned int*) ks);

		tmp_vec0 = vec_xor(tmp_vec0, tmp_vec1);
		tmp_vec0 = vec_xor(tmp_vec0, tmp_vec2);
		tmp_vec0 = vec_xor(tmp_vec0, tmp_vec3);
		tmp_vec0 = vec_xor(tmp_vec0, tmp_vec4);
		tmp_vec0 = vec_xor(tmp_vec0, tmp_vec5);
		tmp_vec0 = vec_xor(tmp_vec0, tmp_vec6);
		tmp_vec0 = vec_xor(tmp_vec0, tmp_vec7);
		vec_st(tmp_vec0, 0x80, (unsigned int*) ks);

		ks[16] ^= ks[17];
		ks[16] ^= SKEIN_KS_PARITY;

		ts[0] = ctx->h.T[0];
		ts[1] = ctx->h.T[1];
		ts[2] = ts[0] ^ ts[1];
		Skein_Get64_1024_altivec(blkPtr); /* load input block into w[] registers */

		X0 = vec_add64(X0, w0);
		X1 = vec_add64(X1, w1);
		X2 = vec_add64(X2, w2);
		X3 = vec_add64(X3, w3);
		X4 = vec_add64(X4, w4);
		X5 = vec_add64(X5, w5);
		X6 = vec_add64(X6, w6);
		X7 = vec_add64(X7, w7);

		tmp_vec1 = vec_ld(0, (unsigned int*)ts);
		tmp_vec1 = vec_sld(tmp_vec1, tmp_vec1, 8);
		tmp_vec0 = vec_sld(X3, X7, 8);
		tmp_vec0 = vec_add64(tmp_vec0, tmp_vec1);
		
		X3 = vec_perm(X3, tmp_vec0, perm_load_upper);
		X7 = vec_perm(tmp_vec0, X7, perm_load_lower);

		for (r = 1; r <= SKEIN1024_ROUNDS_TOTAL / 8; r++) {	/* unroll 8 rounds */
			X0 = vec_add64(X0, X4);
			X1 = vec_add64(X1, X5);
			X2 = vec_add64(X2, X6);
			X3 = vec_add64(X3, X7);
			vec_rotl64(X4, R1024_0_0, R1024_0_1);
			vec_rotl64(X5, R1024_0_2, R1024_0_3);
			vec_rotl64(X6, R1024_0_4, R1024_0_5);
			vec_rotl64(X7, R1024_0_6, R1024_0_7);
			X4 = vec_xor(X4, X0);
			X5 = vec_xor(X5, X1);
			X6 = vec_xor(X6, X2);
			X7 = vec_xor(X7, X3);

			tmp_vec4 = X4;
			X4 = vec_perm(X6, X7, perm_load_upper);
			tmp_vec5 = X5;
			X5 = vec_perm(X7, X6, perm_load_lower);
			X6 = vec_perm(tmp_vec4, tmp_vec5, perm_load_upper_lower);
			X7 = vec_sld(tmp_vec4, tmp_vec5, 8);

			X0 = vec_add64(X0, X4);
			X1 = vec_add64(X1, X5);
			X2 = vec_add64(X2, X6);
			X3 = vec_add64(X3, X7);
			vec_rotl64(X4, R1024_1_0, R1024_1_1);
			vec_rotl64(X5, R1024_1_3, R1024_1_2);
			vec_rotl64(X6, R1024_1_7, R1024_1_4);
			vec_rotl64(X7, R1024_1_5, R1024_1_6);
			X4 = vec_xor(X4, X0);
			X5 = vec_xor(X5, X1);
			X6 = vec_xor(X6, X2);
			X7 = vec_xor(X7, X3);

			tmp_vec4 = X4;
			X4 = vec_perm(X6, X7, perm_load_lower);
			tmp_vec5 = X5;
			X5 = vec_perm(X7, X6, perm_load_upper);
			X6 = vec_sld(tmp_vec5, tmp_vec4, 8);
			X7 = vec_perm(tmp_vec5, tmp_vec4, perm_load_upper_lower);

			X0 = vec_add64(X0, X4);
			X1 = vec_add64(X1, X5);
			X2 = vec_add64(X2, X6);
			X3 = vec_add64(X3, X7);
			vec_rotl64(X4, R1024_2_0, R1024_2_1);
			vec_rotl64(X5, R1024_2_2, R1024_2_3);
			vec_rotl64(X6, R1024_2_6, R1024_2_7);
			vec_rotl64(X7, R1024_2_4, R1024_2_5);
			X4 = vec_xor(X4, X0);
			X5 = vec_xor(X5, X1);
			X6 = vec_xor(X6, X2);
			X7 = vec_xor(X7, X3);

			tmp_vec4 = X4;
			X4 = vec_perm(X7, X6, perm_load_upper);
			tmp_vec5 = X5;
			X5 = vec_perm(X6, X7, perm_load_lower);
			X6 = vec_sld(tmp_vec4, tmp_vec5, 8);
			X7 = vec_perm(tmp_vec4, tmp_vec5, perm_load_upper_lower);
			
			X0 = vec_add64(X0, X4);
			X1 = vec_add64(X1, X5);
			X2 = vec_add64(X2, X6);
			X3 = vec_add64(X3, X7);
			vec_rotl64(X4, R1024_3_0, R1024_3_1);
			vec_rotl64(X5, R1024_3_3, R1024_3_2);
			vec_rotl64(X6, R1024_3_5, R1024_3_6);
			vec_rotl64(X7, R1024_3_7, R1024_3_4);
			X4 = vec_xor(X4, X0);
			X5 = vec_xor(X5, X1);
			X6 = vec_xor(X6, X2);
			X7 = vec_xor(X7, X3);

			tmp_vec4 = X4;
			X4 = vec_perm(X7, X6, perm_load_lower);
			tmp_vec5 = X5;
			X5 = vec_perm(X6, X7, perm_load_upper);
			X6 = vec_perm(tmp_vec5, tmp_vec4, perm_load_upper_lower);
			X7 = vec_sld(tmp_vec5, tmp_vec4, 8);

			InjectKey_1024_altivec(2 * r - 1);


			X0 = vec_add64(X0, X4);
			X1 = vec_add64(X1, X5);
			X2 = vec_add64(X2, X6);
			X3 = vec_add64(X3, X7);
			vec_rotl64(X4, R1024_4_0, R1024_4_1);
			vec_rotl64(X5, R1024_4_2, R1024_4_3);
			vec_rotl64(X6, R1024_4_4, R1024_4_5);
			vec_rotl64(X7, R1024_4_6, R1024_4_7);
			X4 = vec_xor(X4, X0);
			X5 = vec_xor(X5, X1);
			X6 = vec_xor(X6, X2);
			X7 = vec_xor(X7, X3);

			tmp_vec4 = X4;
			X4 = vec_perm(X6, X7, perm_load_upper);
			tmp_vec5 = X5;
			X5 = vec_perm(X7, X6, perm_load_lower);
			X6 = vec_perm(tmp_vec4, tmp_vec5, perm_load_upper_lower);
			X7 = vec_sld(tmp_vec4, tmp_vec5, 8);

			X0 = vec_add64(X0, X4);
			X1 = vec_add64(X1, X5);
			X2 = vec_add64(X2, X6);
			X3 = vec_add64(X3, X7);
			vec_rotl64(X4, R1024_5_0, R1024_5_1);
			vec_rotl64(X5, R1024_5_3, R1024_5_2);
			vec_rotl64(X6, R1024_5_7, R1024_5_4);
			vec_rotl64(X7, R1024_5_5, R1024_5_6);
			X4 = vec_xor(X4, X0);
			X5 = vec_xor(X5, X1);
			X6 = vec_xor(X6, X2);
			X7 = vec_xor(X7, X3);

			tmp_vec4 = X4;
			X4 = vec_perm(X6, X7, perm_load_lower);
			tmp_vec5 = X5;
			X5 = vec_perm(X7, X6, perm_load_upper);
			X6 = vec_sld(tmp_vec5, tmp_vec4, 8);
			X7 = vec_perm(tmp_vec5, tmp_vec4, perm_load_upper_lower);

			X0 = vec_add64(X0, X4);
			X1 = vec_add64(X1, X5);
			X2 = vec_add64(X2, X6);
			X3 = vec_add64(X3, X7);
			vec_rotl64(X4, R1024_6_0, R1024_6_1);
			vec_rotl64(X5, R1024_6_2, R1024_6_3);
			vec_rotl64(X6, R1024_6_6, R1024_6_7);
			vec_rotl64(X7, R1024_6_4, R1024_6_5);
			X4 = vec_xor(X4, X0);
			X5 = vec_xor(X5, X1);
			X6 = vec_xor(X6, X2);
			X7 = vec_xor(X7, X3);

			tmp_vec4 = X4;
			X4 = vec_perm(X7, X6, perm_load_upper);
			tmp_vec5 = X5;
			X5 = vec_perm(X6, X7, perm_load_lower);
			X6 = vec_sld(tmp_vec4, tmp_vec5, 8);
			X7 = vec_perm(tmp_vec4, tmp_vec5, perm_load_upper_lower);
			
			X0 = vec_add64(X0, X4);
			X1 = vec_add64(X1, X5);
			X2 = vec_add64(X2, X6);
			X3 = vec_add64(X3, X7);
			vec_rotl64(X4, R1024_7_0, R1024_7_1);
			vec_rotl64(X5, R1024_7_3, R1024_7_2);
			vec_rotl64(X6, R1024_7_5, R1024_7_6);
			vec_rotl64(X7, R1024_7_7, R1024_7_4);
			X4 = vec_xor(X4, X0);
			X5 = vec_xor(X5, X1);
			X6 = vec_xor(X6, X2);
			X7 = vec_xor(X7, X3);

			tmp_vec4 = X4;
			X4 = vec_perm(X7, X6, perm_load_lower);
			tmp_vec5 = X5;
			X5 = vec_perm(X6, X7, perm_load_upper);
			X6 = vec_perm(tmp_vec5, tmp_vec4, perm_load_upper_lower);
			X7 = vec_sld(tmp_vec5, tmp_vec4, 8);

			InjectKey_1024_altivec(2 * r);
		}
		/* do the final "feedforward" xor */
		X0 = vec_xor(X0, w0);
		X1 = vec_xor(X1, w1);
		X2 = vec_xor(X2, w2);
		X3 = vec_xor(X3, w3);
		X4 = vec_xor(X4, w4);
		X5 = vec_xor(X5, w5);
		X6 = vec_xor(X6, w6);
		X7 = vec_xor(X7, w7);

		Skein_Clear_First_Flag(ctx->h);	/* clear the start bit */
		blkPtr += SKEIN1024_BLOCK_BYTES;
	}
	while (--blkCnt);

	vec_dss(0);

	/* UNDO ALTIVEC ORDER */
	tmp_vec0 = vec_perm(X0, X4, perm_load_upper);
	tmp_vec1 = vec_perm(X0, X4, perm_load_lower);
	tmp_vec2 = vec_perm(X1, X5, perm_load_upper);
	tmp_vec3 = vec_perm(X1, X5, perm_load_lower);
	tmp_vec4 = vec_perm(X2, X6, perm_load_upper);
	tmp_vec5 = vec_perm(X2, X6, perm_load_lower);
	tmp_vec6 = vec_perm(X3, X7, perm_load_upper);
	tmp_vec7 = vec_perm(X3, X7, perm_load_lower);

	vec_st(tmp_vec0, 0x00, (unsigned int*) Xi);
	vec_st(tmp_vec1, 0x10, (unsigned int*) Xi);
	vec_st(tmp_vec2, 0x20, (unsigned int*) Xi);
	vec_st(tmp_vec3, 0x30, (unsigned int*) Xi);
	vec_st(tmp_vec4, 0x40, (unsigned int*) Xi);
	vec_st(tmp_vec5, 0x50, (unsigned int*) Xi);
	vec_st(tmp_vec6, 0x60, (unsigned int*) Xi);
	vec_st(tmp_vec7, 0x70, (unsigned int*) Xi);

	memcpy(ctx->X, Xi, 8*16);
}

#undef InjectKey_1024_altivec
#undef Skein_Get64_1024_Altivec

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
