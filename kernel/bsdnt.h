#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <limits.h>
#include <stdio.h>

#define MUL_CLASSICAL_CUTOFF       33L
#define MUL_KARA_CUTOFF            400L
#define MUL_TOOM32_CUTOFF          LONG_MAX
#define MUL_TOOM33_CUTOFF          LONG_MAX
#define MULMID_CLASSICAL_CUTOFF    80L
#define MULLOW_CLASSICAL_CUTOFF    120L
#define DIVAPPROX_CLASSICAL_CUTOFF 45L
#define DIVREM_CLASSICAL_CUTOFF    80L

#define BSDNT_MIN(x, y) \
   ((x) <= (y) ? (x) : (y))

#define WORD(x) (x##UL)

#define WORD_BITS 64

#define high_zero_bits __builtin_clzl

typedef uint64_t      word_t;
typedef int64_t       sword_t;
typedef int64_t       len_t;
typedef int64_t       bits_t;
typedef __uint128_t   dword_t;
typedef word_t        preinv2_t;
typedef word_t        preinv1_t;
typedef word_t*       nn_t;
typedef const word_t *nn_src_t;

#define TMP_INIT \
   typedef struct __tmp_struct { \
      void * block; \
      struct __tmp_struct * next; \
   } __tmp_t; \
   __tmp_t * __tmp_root; \
   __tmp_t * __t

#define TMP_START \
   __tmp_root = NULL

#define TMP_END \
   while (__tmp_root) { \
      free(__tmp_root->block); \
      __tmp_root = __tmp_root->next; \
   }

#define TMP_ALLOC_BYTES(size) \
   ((size) > 8192 ? \
      (__t = (__tmp_t *) alloca(sizeof(__tmp_t)), \
       __t->next = __tmp_root, \
       __tmp_root = __t, \
       __t->block = malloc(size)) : \
      alloca(size))

#define TMP_ALLOC(size) \
   TMP_ALLOC_BYTES(sizeof(word_t)*(size))

static inline void nn_zero(nn_t a, len_t m) {
   for (long i = 0; i < m; i++) a[i] = 0;
}

static inline void nn_copy(nn_t a, nn_src_t b, len_t m) {
   for (long i = 0; i < m; i++) a[i] = b[i];
}

static inline len_t nn_normalise(nn_t a, len_t m) {
   while ((m != 0) && (a[m - 1] == 0)) m--;
   return m;
}

void nn_mul(nn_t p, nn_src_t a, len_t m, nn_src_t b, len_t n);

void nn_mul_m(nn_t p, nn_src_t a, nn_src_t b, len_t m);

#define nn_add_m(a, b, c, m) \
   nn_add_mc(a, b, c, m, (word_t) 0)


#define nn_mul1(a, b, m, c) \
   nn_mul1_c(a, b, m, c, (word_t) 0)

#define nn_addmul1(a, b, m, c) \
   nn_addmul1_c(a, b, m, c, (word_t) 0)

#define nn_sub_m(a, b, c, m) \
   nn_sub_mc(a, b, c, m, (word_t) 0)

#define nn_submul1(a, b, m, c) \
   nn_submul1_c(a, b, m, c, (word_t) 0)

#define divapprox21_preinv1(q, u_hi, u_lo, d, dinv) \
   do { \
      dword_t __q1 = (dword_t) u_hi * (dword_t) (dinv) \
                  + (((dword_t) u_hi) << WORD_BITS) + (dword_t) u_lo; \
      const dword_t __q0 = (dword_t) u_lo * (dword_t) (dinv); \
      __q1 += (dword_t) ((__q0) >> WORD_BITS); \
      (q) = (__q1 >> WORD_BITS); \
   } while (0)

#define divapprox21_preinv2(q, a_hi, a_lo, dinv) \
   do { \
      const dword_t __a = ((dword_t) (a_hi) << WORD_BITS) + (dword_t) (a_lo); \
      dword_t __q2 = (dword_t) (a_hi) * (dword_t) (dinv); \
      dword_t __q3 = (dword_t) (a_lo) * (dword_t) (dinv); \
      __q2 += (__q3 >> WORD_BITS) + __a; \
      (q) = (word_t) (__q2 >> WORD_BITS); \
   } while (0)

word_t nn_add_mc(nn_t a, nn_src_t b, nn_src_t c, len_t m, word_t ci);

word_t nn_add1(nn_t a, nn_src_t b, len_t m, word_t c);

word_t nn_sub1(nn_t a, nn_src_t b, len_t m, word_t c);

word_t nn_sub_mc(nn_t a, nn_src_t b, nn_src_t c, len_t m, word_t bi);


static inline word_t nn_add_c(nn_t a, nn_src_t b, len_t bm, 
                              nn_src_t c, len_t cm, word_t ci) {
   ci = nn_add_mc(a, b, c, cm, ci);
   return nn_add1(a + cm, b + cm, bm - cm, ci);
}

#define nn_add(a, b, bm, c, cm) \
   nn_add_c(a, b, bm, c, cm, (word_t) 0)

#define nn_divrem1_simple(q, a, m, d) \
   nn_divrem1_simple_c(q, a, m, d, (word_t) 0)

static inline word_t nn_sub_c(nn_t a, nn_src_t b, len_t bm, 
                            nn_src_t c, len_t cm, word_t ci) {
   ci = nn_sub_mc(a, b, c, cm, ci);
   return nn_sub1(a + cm, b + cm, bm - cm, ci);
}

#define nn_sub(a, b, bm, c, cm) \
   nn_sub_c(a, b, bm, c, cm, (word_t) 0)

void nn_divrem_divconquer_preinv_c
    (nn_t q, nn_t a, len_t m, nn_src_t d, len_t n, preinv2_t dinv, word_t ci);

word_t nn_divapprox_divconquer_preinv_c
    (nn_t q, nn_t a, len_t m, nn_src_t d, len_t n, preinv2_t dinv, word_t ci);

#define nn_shl(a, b, m, bits) \
   nn_shl_c(a, b, m, bits, (word_t) 0)

#define nn_shr(a, b, m, bits) \
   nn_shr_c(a, b, m, bits, (word_t) 0)

#define nn_neg(a, b, m) \
    nn_neg_c(a, b, m, 0)

void nn_divrem(nn_t q, nn_t a, len_t m, nn_src_t d, len_t n);

int nn_cmp_m(nn_src_t a, nn_src_t b, len_t m);

void nn_mul_m(nn_t p, nn_src_t a, nn_src_t b, len_t m);

word_t nn_mul1_c(nn_t a, nn_src_t b, len_t m, word_t c, word_t ci);

word_t nn_divrem1_simple_c(nn_t q, nn_src_t a, len_t m, word_t d, word_t ci);

void nn_mul_classical(nn_t r, nn_src_t a, len_t m1, nn_src_t b, len_t m2);
