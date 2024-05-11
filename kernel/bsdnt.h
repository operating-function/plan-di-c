#include <stdint.h>
#include <math.h>
#include <limits.h>

#define WORD_BITS      64
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

void   nn_mul              (nn_t p, nn_src_t a, len_t m, nn_src_t b, len_t n);
void   nn_mul_m            (nn_t p, nn_src_t a, nn_src_t b, len_t m);
word_t nn_add_mc           (nn_t a, nn_src_t b, nn_src_t c, len_t m, word_t ci);
word_t nn_add1             (nn_t a, nn_src_t b, len_t m, word_t c);
word_t nn_sub1             (nn_t a, nn_src_t b, len_t m, word_t c);
word_t nn_sub_mc           (nn_t a, nn_src_t b, nn_src_t c, len_t m, word_t bi);
void   nn_divrem           (nn_t q, nn_t a, len_t m, nn_src_t d, len_t n);
int    nn_cmp_m            (nn_src_t a, nn_src_t b, len_t m);
void   nn_mul_m            (nn_t p, nn_src_t a, nn_src_t b, len_t m);
word_t nn_mul1_c           (nn_t a, nn_src_t b, len_t m, word_t c, word_t ci);
word_t nn_divrem1_simple_c (nn_t q, nn_src_t a, len_t m, word_t d, word_t ci);
void   nn_mul_classical    (nn_t r, nn_src_t a, len_t m1, nn_src_t b, len_t m2);

#define nn_add_m(a, b, c, m)       nn_add_mc(a, b, c, m, (word_t) 0)
#define nn_mul1(a, b, m, c)        nn_mul1_c(a, b, m, c, (word_t) 0)
#define nn_addmul1(a, b, m, c)     nn_addmul1_c(a, b, m, c, (word_t) 0)
#define nn_sub_m(a, b, c, m)       nn_sub_mc(a, b, c, m, (word_t) 0)
#define nn_submul1(a, b, m, c)     nn_submul1_c(a, b, m, c, (word_t) 0)
#define nn_shl(a, b, m, bits)      nn_shl_c(a, b, m, bits, (word_t) 0)
#define nn_shr(a, b, m, bits)      nn_shr_c(a, b, m, bits, (word_t) 0)
#define nn_neg(a, b, m)            nn_neg_c(a, b, m, 0)
#define nn_add(a, b, bm, c, cm)    nn_add_c(a, b, bm, c, cm, (word_t) 0)
#define nn_divrem1_simple(q,a,m,d) nn_divrem1_simple_c(q, a, m, d, (word_t) 0)
#define nn_sub(a, b, bm, c, cm)    nn_sub_c(a, b, bm, c, cm, (word_t) 0)

static inline word_t nn_add_c(nn_t a, nn_src_t b, len_t bm, 
                              nn_src_t c, len_t cm, word_t ci) {
   ci = nn_add_mc(a, b, c, cm, ci);
   return nn_add1(a + cm, b + cm, bm - cm, ci);
}

static inline word_t nn_sub_c(nn_t a, nn_src_t b, len_t bm, 
                            nn_src_t c, len_t cm, word_t ci) {
   ci = nn_sub_mc(a, b, c, cm, ci);
   return nn_sub1(a + cm, b + cm, bm - cm, ci);
}

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
