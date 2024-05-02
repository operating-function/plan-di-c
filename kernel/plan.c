// - TODO GC at a certain size, not just after each assertion.
// - TODO Place the two heaps in adjacent memory.
// - TODO Separate "pinspace" gc generation (not collected / moved).
// - TODO pinspace backed by file.
// - TODO resume from pinspace snapshots + log
// - TODO WASM

#include <math.h>
#include <stdint.h>
#define __STDC_WANT_LIB_EXT2__  1
#include <stdio.h>
#include <stdbool.h>
#include <ctype.h>
#include <stdarg.h>
#include <string.h>
#include <sys/param.h>
#include <sys/stat.h>
#include <inttypes.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdnoreturn.h>
#include <sys/mman.h>
#include <stdint.h>
#include <assert.h>

// BSDNT ///////////////////////////////////////////////////////////////////////

#define MUL_CLASSICAL_CUTOFF 33L
#define MUL_KARA_CUTOFF 400L
#define MUL_TOOM32_CUTOFF LONG_MAX
#define MUL_TOOM33_CUTOFF LONG_MAX
#define MULMID_CLASSICAL_CUTOFF 80L
#define MULLOW_CLASSICAL_CUTOFF 120L
#define DIVAPPROX_CLASSICAL_CUTOFF 45L
#define DIVREM_CLASSICAL_CUTOFF 80L

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

/*
   Set a = b + c where b and c are both m words in length. Return 
   any carry out. 
*/
#define nn_add_m(a, b, c, m) \
   nn_add_mc(a, b, c, m, (word_t) 0)

word_t nn_add_mc(nn_t a, nn_src_t b, nn_src_t c, len_t m, word_t ci)
{
   dword_t t;

   for (long i = 0; i < m; i++)
   {
      t = (dword_t) b[i] + (dword_t) c[i] + (dword_t) ci;
      a[i] = (word_t) t;
      ci = (t >> WORD_BITS);
   }

   return ci;
}

int nn_cmp_m(nn_src_t a, nn_src_t b, len_t m)
{
   while (m--)
   {
      if (a[m] != b[m])
      {
         if (a[m] > b[m])
            return 1;
         else
            return -1;
      }
   }

   return 0;
}

word_t nn_add1(nn_t a, nn_src_t b, len_t m, word_t c)
{
   dword_t t;
   long i;

   for (i = 0; i < m && c != 0; i++)
   {
      t = (dword_t) b[i] + (dword_t) c;
      a[i] = (word_t) t;
      c = (t >> WORD_BITS);
   }

   if (a != b)
      for ( ; i < m; i++)
         a[i] = b[i];

   return c;
}

word_t nn_sub1(nn_t a, nn_src_t b, len_t m, word_t c)
{
   dword_t t;
   long i;

   for (i = 0; i < m && c != 0; i++)
   {
      t = (dword_t) b[i] - (dword_t) c;
      a[i] = (word_t) t;
      c = -(t >> WORD_BITS);
   }

   if (a != b)
      for ( ; i < m; i++)
         a[i] = b[i];

   return c;
}

word_t nn_mul1_c(nn_t a, nn_src_t b, len_t m, word_t c, word_t ci)
{
   dword_t t;
   long i;

   for (i = 0; i < m; i++)
   {
      t = (dword_t) b[i] * (dword_t) c + (dword_t) ci;
      a[i] = (word_t) t;
      ci = (t >> WORD_BITS);
   }

   return ci;
}

#define nn_mul1(a, b, m, c) \
   nn_mul1_c(a, b, m, c, (word_t) 0)

word_t nn_addmul1_c(nn_t a, nn_src_t b, len_t m, word_t c, word_t ci)
{
   dword_t t;
   long i;

   for (i = 0; i < m; i++)
   {
      t = (dword_t) a[i] + (dword_t) b[i] * (dword_t) c + (dword_t) ci;
      a[i] = (word_t) t;
      ci = (t >> WORD_BITS);
   }

   return ci;
}

#define nn_addmul1(a, b, m, c) \
   nn_addmul1_c(a, b, m, c, (word_t) 0)

void nn_mul_classical(nn_t r, nn_src_t a, len_t m1, nn_src_t b, len_t m2) {
   len_t i;

   r[m1] = nn_mul1(r, a, m1, b[0]);

   for (i = 1; i < m2; i++)
      r[m1 + i] = nn_addmul1(r + i, a, m1, b[i]);
}


word_t nn_sub_mc(nn_t a, nn_src_t b, nn_src_t c, len_t m, word_t bi) {
   dword_t t;
   long i;

   for (i = 0; i < m; i++)
   {
      t = (dword_t) b[i] - (dword_t) c[i] - (dword_t) bi;
      a[i] = (word_t) t;
      bi = -(t >> WORD_BITS);
   }

   return bi;
}

#define nn_sub_m(a, b, c, m) \
   nn_sub_mc(a, b, c, m, (word_t) 0)

word_t nn_submul1_c(nn_t a, nn_src_t b, len_t m, word_t c, word_t ci)
{
   dword_t t;
   long i;

   for (i = 0; i < m; i++)
   {
      t = (dword_t) a[i] - (dword_t) b[i] * (dword_t) c - (dword_t) ci;
      a[i] = (word_t) t;
      ci = -(t >> WORD_BITS);
   }

   return ci;
}

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

void nn_divrem_classical_preinv_c(nn_t q, nn_t a, len_t m, nn_src_t d,
                                  len_t n, preinv2_t dinv, word_t ci)
{
   long j;

   a += m;

   for (j = m - n; j >= 0; j--)
   {
      a--;

      divapprox21_preinv2(q[j], ci, a[0], dinv);

	  /* a -= d*q1 */
      ci -= nn_submul1(a - n + 1, d, n, q[j]);

      /* correct if remainder is too large */
      if (ci || nn_cmp_m(a - n + 1, d, n) >= 0)
      {
         q[j]++;
         ci -= nn_sub_m(a - n + 1, a - n + 1, d, n);
      }

      /* fetch next word now that it has been updated */
      ci = a[0];
   }
}

static inline word_t nn_add_c(nn_t a, nn_src_t b, len_t bm, 
                              nn_src_t c, len_t cm, word_t ci) {
   ci = nn_add_mc(a, b, c, cm, ci);
   return nn_add1(a + cm, b + cm, bm - cm, ci);
}

/*
   Set a = b + c + ci where b is bm words, c is cm words in length,
   and bm >= cm. We return the carry out. 
*/
#define nn_add(a, b, bm, c, cm) \
   nn_add_c(a, b, bm, c, cm, (word_t) 0)

word_t _nn_divapprox_helper(nn_t q, nn_t a, nn_src_t d, len_t s)
{
   word_t ci;
   len_t i;
   
   nn_sub_m(a + 1, a + 1, d, s + 1);
   ci = a[2] + nn_add1(a + 1, a + 1, 1, d[s]);

   for (i = s - 1; i >= 0; i--)
   {
      q[i] = ~WORD(0);
      ci += nn_add1(a, a, 2, d[i]);
   }

   return ci;
}

word_t nn_divapprox_classical_preinv_c(nn_t q, nn_t a, len_t m, nn_src_t d,
                                  len_t n, preinv2_t dinv, word_t ci)
{
   word_t cy = 0;
   len_t s = m - n + 1;

   a += m;

   /* Reduce until n - 2 >= s */
   for (s = m - n; s > n - 2; s--)
   {
      a--;
      divapprox21_preinv2(q[s], ci, a[0], dinv);

	  /* a -= d*q1 */
      ci -= nn_submul1(a - n + 1, d, n, q[s]);

      /* correct if remainder is too large */
      if (ci || nn_cmp_m(a - n + 1, d, n) >= 0)
      {
         q[s]++;
         ci -= nn_sub_m(a - n + 1, a - n + 1, d, n);
      }

      /* fetch next word now that it has been updated */
      cy = ci;
      ci = a[0];
   }

   s++;
   d = d + n - s - 1; /* make d length s + 1 */

   for ( ; s > 0; s--)
   {
      a--;
      /* rare case where truncation ruins normalisation */
      if (ci > d[s] || (ci == d[s] && nn_cmp_m(a - s + 1, d, s) >= 0))
         return _nn_divapprox_helper(q, a - s, d, s);

      divapprox21_preinv2(q[s - 1], ci, a[0], dinv);

      /* a -= d*q1 */
      ci -= nn_submul1(a - s, d, s + 1, q[s - 1]);

	   /* correct if remainder is too large */
      if (ci || nn_cmp_m(a - s, d, s + 1) >= 0)
      {
         q[s - 1]++;
         ci -= nn_sub_m(a - s, a - s, d, s + 1);
      }

      /* fetch next word now that it has been updated */
      cy = ci;
      ci = a[0];

      d++;
   }

   return cy;
}

#define nn_divrem1_simple(q, a, m, d) \
   nn_divrem1_simple_c(q, a, m, d, (word_t) 0)

static inline word_t nn_sub_c(nn_t a, nn_src_t b, len_t bm, 
                            nn_src_t c, len_t cm, word_t ci) {
   ci = nn_sub_mc(a, b, c, cm, ci);
   return nn_sub1(a + cm, b + cm, bm - cm, ci);
}

/*
   Set a = b - c - ci where b is bm words, c is cm words in length,
   and bm >= cm. We return any borrow out. 
*/
#define nn_sub(a, b, bm, c, cm) \
   nn_sub_c(a, b, bm, c, cm, (word_t) 0)

void nn_divrem_divconquer_preinv_c(nn_t q, nn_t a, len_t m, nn_src_t d, len_t n, preinv2_t dinv, word_t ci);


static inline
void nn_divrem_preinv_c(nn_t q, nn_t a, len_t m, nn_src_t d, 
                               len_t n, preinv2_t dinv, word_t ci) {
   if (n <= DIVREM_CLASSICAL_CUTOFF || m == n)
      nn_divrem_classical_preinv_c(q, a, m, d, n, dinv, ci);
   else
      nn_divrem_divconquer_preinv_c(q, a, m, d, n, dinv, ci);
}

void talker(const char * str) {
   fprintf(stderr, "Error: %s\n", str);
}

static inline preinv1_t precompute_inverse1(word_t d) {
   d++;

   if (d == 0)
      return 0;

   return (word_t) ((((dword_t) -d) << WORD_BITS) / (dword_t) d);
}

preinv2_t precompute_inverse2(word_t d1, word_t d2)
{
   word_t q, r[2], p[2], ci;
   dword_t t;

   if (d2 + 1 == 0 && d1 + 1 == 0)
      return 0;

   if (d1 + 1 == 0)
      q = ~d1, r[1] = ~d2;
   else
   {
      t = ((((dword_t) ~d1) << WORD_BITS) + (dword_t) ~d2);
      q = (word_t) (t / (dword_t) (d1 + 1));
      r[1] = (word_t) (t % (dword_t) (d1 + 1));
   }

   if (d2 + 1 == 0)
      return q;
   
   r[0] = 0;

   t = (dword_t) q * (dword_t) (~d2);
   p[0] = (word_t) t;
   p[1] = (word_t) (t >> WORD_BITS);
   ci = nn_add_m(r, r, p, 2);
 
   p[0] = d2 + 1, p[1] = d1 + (d2 + 1 == 0);
   while (ci || nn_cmp_m(r, p, 2) >= 0)
   {
      q++;
      ci -= nn_sub_m(r, r, p, 2);
   }
   
   return q;
}

word_t nn_shl_c(nn_t a, nn_src_t b, len_t m, bits_t bits, word_t ci)
{
   dword_t t;
   long i;

   for (i = 0; i < m; i++)
   {
      t = (((dword_t) b[i]) << bits);
      a[i] = (word_t) t + ci;
      ci = (t >> WORD_BITS);
   }

   return ci;
}

#define nn_shl(a, b, m, bits) \
   nn_shl_c(a, b, m, bits, (word_t) 0)

word_t nn_shr_c(nn_t a, nn_src_t b, len_t m, bits_t bits, word_t ci)
{
   dword_t t;
   long i;

   bits = WORD_BITS - bits;

   for (i = m - 1; i >= 0L; i--)
   {
      t = (((dword_t) b[i]) << bits);
      a[i] = (t >> WORD_BITS) + ci;
      ci = (word_t) t;
   }

   return ci;
}

#define nn_shr(a, b, m, bits) \
   nn_shr_c(a, b, m, bits, (word_t) 0)

word_t nn_neg_c(nn_t a, nn_src_t b, len_t m, word_t ci)
{
   dword_t t;
   long i;
   
   ci = 1 - ci;

   for (i = 0; i < m && ci != 0; i++)
   {
      t = (dword_t) ~b[i] + (dword_t) ci;
      a[i] = (word_t) t;
      ci = (t >> WORD_BITS);
   }

   for ( ; i < m; i++)
      a[i] = ~b[i];

   return (word_t) 1 - ci;
}

#define nn_neg(a, b, m) \
    nn_neg_c(a, b, m, 0)

void nn_mul_toom33(nn_t p, nn_src_t a, len_t m, nn_src_t b, len_t n)
{
   len_t m3 = (m + 2)/3;
   len_t h1 = m - 2*m3;
   len_t h2 = n - 2*m3;
   len_t nn;
   word_t ci;
   bits_t norm;
   nn_t t;
   TMP_INIT;

   TMP_START;
   t = (nn_t) TMP_ALLOC(6*m3 + 6);

#define r1 p
#define r2 t
#define r3 (t + 2*m3 + 2)
#define r4 (t + 4*m3 + 4)  
#define r5 (p + 4*m3) 
#define s1 (p + m3 + 1)

   r1[m3]  = nn_add_m(r1, a, a + m3, m3); /* Evaluate at 1 */
   r1[m3] += nn_add(r1, r1, m3, a + 2*m3, h1);
   s1[m3]  = nn_add_m(s1, b, b + m3, m3);
   s1[m3] += nn_add(s1, s1, m3, b + 2*m3, h2);
   nn_mul_m(r2, r1, s1, m3 + 1);

   ci = nn_shl(r1, a + 2*m3, h1, 1); /* Evaluate at 2 */
   r1[m3]  = nn_add(r1, a + m3, m3, r1, h1);
   r1[m3] += nn_add1(r1 + h1, r1 + h1, m3 - h1, ci);
   nn_shl(r1, r1, m3 + 1, 1);
   r1[m3] += nn_add_m(r1, r1, a, m3);
   ci = nn_shl(s1, b + 2*m3, h2, 1);
   s1[m3]  = nn_add(s1, b + m3, m3, s1, h2);
   s1[m3] += nn_add1(s1 + h2, s1 + h2, m3 - h2, ci);
   nn_shl(s1, s1, m3 + 1, 1);
   s1[m3] += nn_add_m(s1, s1, b, m3);
   nn_mul_m(r3, r1, s1, m3 + 1);

   ci = nn_shl(r1, a + 2*m3, h1, 2); /* Evaluate at 4 */
   r1[m3]  = nn_add(r1, a + m3, m3, r1, h1);
   r1[m3] += nn_add1(r1 + h1, r1 + h1, m3 - h1, ci);
   nn_shl(r1, r1, m3 + 1, 2);
   r1[m3] += nn_add_m(r1, r1, a, m3);
   ci = nn_shl(s1, b + 2*m3, h2, 2);
   s1[m3]  = nn_add(s1, b + m3, m3, s1, h2);
   s1[m3] += nn_add1(s1 + h2, s1 + h2, m3 - h2, ci);
   nn_shl(s1, s1, m3 + 1, 2);
   s1[m3] += nn_add_m(s1, s1, b, m3);
   nn_mul_m(r4, r1, s1, m3 + 1);

   nn_mul_m(r1, a, b, m3); /* Evaluate at 0 */
   nn_mul(r5, a + 2*m3, h1, b + 2*m3, h2); /* Evaluate at oo */

   nn_zero(p + 2*m3, 2*m3);

   r3[2*m3 + 1] = -nn_sub(r3, r3, 2*m3 + 1, r1, 2*m3); /* Interpolate */
   r4[2*m3 + 1] = -nn_sub(r4, r4, 2*m3 + 1, r1, 2*m3);
   r2[2*m3 + 1] = -nn_sub(r2, r2, 2*m3 + 1, r1, 2*m3);
   nn_submul1(r3, r2, 2*m3 + 1, 2);
   nn_submul1(r4, r2, 2*m3 + 1, 4);
   ci = nn_submul1(r4, r5, h1 + h2, 112);
   nn_sub1(r4 + h1 + h2, r4 + h1 + h2, 2*m3 - h1 - h2 + 1, ci); 
   nn_submul1(r4, r3, 2*m3 + 1, 10);
   nn_neg(r4, r4, 2*m3 + 1);
   nn_shr(r4, r4, 2*m3 + 1, 3);
   nn_submul1(r3, r4, 2*m3 + 1, 2);
   ci = nn_submul1(r3, r5, h1 + h2, 14);
   nn_sub1(r3 + h1 + h2, r3 + h1 + h2, 2*m3 - h1 - h2 + 1, ci);

   norm = high_zero_bits(WORD(3));
   // word_t ninv = precompute_inverse1(WORD(3) << norm);
   r3[2*m3 + 1] = nn_shl(r3, r3, 2*m3 + 1, norm);

   nn_shr(r3, r3, 2*m3 + 1, 1);
   nn_sub_m(r2, r2, r3, 2*m3 + 1);
   nn_sub_m(r2, r2, r4, 2*m3 + 1);
   nn_sub(r2, r2, 2*m3 + 1, r5, h1 + h2);

   nn = nn_normalise(r3, 2*m3 + 1); /* Normalise */
   
   nn_add(p + m3, p + m3, 3*m3 + h1 + h2, r2, 2*m3 + 1); /* Recombine */
   nn_add(p + 2*m3, p + 2*m3, 2*m3 + h1 + h2, r4, 2*m3 + 1); 
   nn_add(p + 3*m3, p + 3*m3, m3 + h1 + h2, r3, nn); 

   TMP_END;

#undef r1
#undef r2
#undef r3
#undef r4
#undef r5
#undef s1
}

void nn_mul_kara(nn_t p, nn_src_t a, len_t m, nn_src_t b, len_t n)
{
   len_t m2 = (m + 1)/2;
   len_t h1 = m - m2;
   len_t h2 = n - m2;
   
   nn_t t;
   TMP_INIT;

   p[m2]       = nn_add(p, a, m2, a + m2, h1);
   p[2*m2 + 1] = nn_add(p + m2 + 1, b, m2, b + m2, h2);
   
   TMP_START;
   t = (nn_t) TMP_ALLOC(2*m2 + 2);
   
   nn_mul_m(t, p + m2 + 1, p, m2 + 1); 
   
   nn_mul_m(p, a, b, m2);
   nn_mul(p + 2*m2, a + m2, h1, b + m2, h2);
   
   nn_sub(t, t, 2*m2 + 1, p, 2*m2);
   nn_sub(t, t, 2*m2 + 1, p + 2*m2, h1 + h2);
   
   /* add a_hi*b_lo + a_lo*b_hi, cannot exceed m + 1 words */
   nn_add(p + m2, p + m2, m + h2, t, m + 1);
   
   TMP_END;
}

void nn_mul_m(nn_t p, nn_src_t a, nn_src_t b, len_t m)
{
   if (m <= MUL_CLASSICAL_CUTOFF)
      nn_mul_classical(p, a, m, b, m);
   else if (m <= MUL_KARA_CUTOFF)
      nn_mul_kara(p, a, m, b, m);
   else if (m <= MUL_TOOM33_CUTOFF)
      nn_mul_toom33(p, a, m, b, m);
   else
      talker("Out of options in nn_mul_m\n");
}

void nn_mul_toom32(nn_t p, nn_src_t a, len_t m, nn_src_t b, len_t n) {
   len_t m3 = (m + 2)/3;
   len_t h1 = m - 2*m3;
   len_t h2 = n - m3;
   len_t nn;
   nn_t t;
   word_t ci;
   TMP_INIT;

   TMP_START;
   t = (nn_t) TMP_ALLOC(4*m3 + 4);

#define r1 p
#define r2 t
#define r3 (t + 2*m3 + 2)
#define r4 (p + 3*m3)   
#define s1 (p + m3 + 1)

   r1[m3]  = nn_add(r1, a, m3, a + 2*m3, h1); /* Evaluate at 1 */
   r1[m3] += nn_add_m(r1, r1, a + m3, m3);
   s1[m3]  = nn_add(s1, b, m3, b + m3, h2);
   nn_mul_m(r2, r1, s1, m3 + 1);

   ci = nn_shl(r1, a + 2*m3, h1, 1); /* Evaluate at 2 */
   r1[m3]  = nn_add(r1, a + m3, m3, r1, h1);
   r1[m3] += nn_add1(r1 + h1, r1 + h1, m3 - h1, ci);
   nn_shl(r1, r1, m3 + 1, 1);
   r1[m3] += nn_add_m(r1, r1, a, m3);
   ci = nn_shl(s1, b + m3, h2, 1);
   s1[m3]  = nn_add(s1, b, m3, s1, h2);
   s1[m3] += nn_add1(s1 + h2, s1 + h2, m3 - h2, ci);
   nn_mul_m(r3, r1, s1, m3 + 1);

   nn_mul_m(r1, a, b, m3); /* Evaluate at 0 */
   if (h1 >= h2) nn_mul(r4, a + 2*m3, h1, b + m3, h2); /* Evaluate at oo */
   else nn_mul(r4, b + m3, h2, a + 2*m3, h1);
   nn_zero(p + 2*m3, m3);

   nn_sub_m(r2, r2, r1, 2*m3 + 1); /* Interpolate */
   nn_sub_m(r3, r3, r1, 2*m3 + 1);
   nn_submul1(r3, r2, 2*m3 + 1, 2); 
   ci = nn_submul1(r3, r4, h1 + h2, 6);
   nn_sub1(r3 + h1 + h2, r3 + h1 + h2, 2*m3 - h1 - h2 + 1, ci);

   nn_sub(r2, r2, 2*m3 + 1, r4, h1 + h2);
   nn_sub_m(r2, r2, r3, 2*m3 + 1);
   
   nn = nn_normalise(r3, 2*m3 + 1); /* Normalise */
   
   nn_add(p + m3, p + m3, 2*m3 + h1 + h2, r2, 2*m3 + 1); /* Recombine */
   nn_add(p + 2*m3, p + 2*m3, m3 + h1 + h2, r3, nn); 

   TMP_END;

#undef r1
#undef r2
#undef r3
#undef r4
#undef s1
}

void nn_mul(nn_t p, nn_src_t a, len_t m, nn_src_t b, len_t n)
{
   len_t r;
   nn_t t;
   TMP_INIT;
   
   if (n <= MUL_CLASSICAL_CUTOFF)
   {
      nn_mul_classical(p, a, m, b, n);
      return;
   } 
   
   if (n <= MUL_KARA_CUTOFF)
   {
      if (n > (m + 1)/2)
      {
         nn_mul_kara(p, a, m, b, n);
         return;
      }
   } else /* too big for Karatsuba */
   {
      const len_t m3 = (m + 2)/3;
      
      if (n > m3)
      {
         if (n <= 2*m3)
         {
            if (n <= MUL_TOOM32_CUTOFF)
            {
               nn_mul_toom32(p, a, m, b, n);
               return;
            } else
               talker("Out of options in nn_mul\n");
         } else /* n > 2*m3 */
         {
            if (n <= MUL_TOOM33_CUTOFF)
            {
               nn_mul_toom33(p, a, m, b, n);
               return;
            } else
               talker("Out of options in nn_mul\n");
         }
      }
   }

   r = m;

   while (r > n) r -= n;

   nn_mul(p, b, n, a, r);
  
   TMP_START;
   t = (nn_t) TMP_ALLOC(n + 1);
   while (m > r)
   {
      nn_copy(t, p + r, n); /* temporarily save top n + 1 limbs */
      nn_mul_m(p + r, a + r, b, n);
      nn_add(p + r, p + r, 2*n, t, n);
      r += n;
   }
   TMP_END;
}

void nn_mullow_classical(nn_t ov, nn_t r, nn_src_t a, len_t m1, 
                                              nn_src_t b, len_t m2)
{
   len_t i;
   dword_t t;
  
   t = (dword_t) nn_mul1(r, a, m1, b[0]); 
   
   for (i = 1; i < m2; i++)
      t += (dword_t) nn_addmul1(r + i, a, m1 - i, b[i]);

   ov[0] = (word_t) t;
   ov[1] = (word_t) (t >> WORD_BITS);
}

void nn_mullow_kara(nn_t ov, nn_t p, nn_src_t a, len_t m, nn_src_t b, len_t n)
{
   len_t nl = n/2, nh = n - nl;
   len_t mh = nl, ml = m - mh;
   nn_t p1, p2;
   word_t ci;

   TMP_INIT;

   if (n <= MULLOW_CLASSICAL_CUTOFF)
   {
      nn_mullow_classical(ov, p, a, m, b, n);
      return;
   }

   nn_mul(p, a, ml, b, nl);
   
   TMP_START;

   p1 = (nn_t) TMP_ALLOC(mh);
   p2 = (nn_t) TMP_ALLOC(ml + 2);

   nn_mullow_kara(ov, p1, a + ml, mh, b, mh);
   nn_mullow_kara(p2 + ml, p2, a, ml, b + nl, nh);

   ci = nn_add_m(p + ml, p + ml, p1, mh);
   nn_add1(ov, ov, 2, ci);

   ci = nn_add_m(p + nl, p + nl, p2, ml);
   nn_add_mc(ov, ov, p2 + ml, 2, ci);
   
   TMP_END;
}

void nn_mulmid_classical(nn_t ov, nn_t p,
                            nn_src_t a, len_t m, nn_src_t b, len_t n)
{
  dword_t t; /* overflow */

  a += n - 1;
  m -= n - 1;

  t = nn_mul1(p, a, m, b[0]);

  for (n--; n > 0; n--)
  {
      a--; b++;
      t += nn_addmul1(p, a, m, b[0]);
  }

  ov[0] = (word_t) t;
  ov[1] = (t >> WORD_BITS);
}

#define _NN_MULMID_RFIX_M(_op_) \
   len_t i; \
   dword_t s, t = 0; \
   word_t ci = 0; \
   a += n - 2; \
   nn_zero(p, n); \
   for (i = 0; i < n - 1; i++, a--) \
   { \
      s = (dword_t) b1[i] _op_ (dword_t) b2[i] _op_ (dword_t) ci; \
      r[i] = (word_t) s; \
      if ((ci = _op_ (s >> WORD_BITS))) \
         t += (dword_t) a[n] - (dword_t) nn_sub1(p, p, n, a[0]); \
   } \
   s = (dword_t) b1[i] _op_ (dword_t) b2[i] _op_ (dword_t) ci; \
   r[i] = (word_t) s; \
   if ((ci = _op_ (s >> WORD_BITS))) \
      t += (dword_t) a[n] + (dword_t) nn_add_m(p + 1, p + 1, a + 1, n - 1); \
   ov[0] = (word_t) t; \
   ov[1] = (t >> WORD_BITS); \
   return ci;

word_t _nn_mulmid_add_rfix_m(nn_t r, nn_t ov, nn_t p,
                       nn_src_t a, nn_src_t b1, nn_src_t b2, len_t n) {
   _NN_MULMID_RFIX_M(+);
}

word_t _nn_mulmid_sub_rfix_m(nn_t r, nn_t ov, nn_t p,
                       nn_src_t a, nn_src_t b1, nn_src_t b2, len_t n) {
   _NN_MULMID_RFIX_M(-);
}

word_t _nn_mulmid_add_lfix_m(nn_t r, nn_t ov, nn_t p,
                    nn_src_t a1, nn_src_t a2, nn_src_t b, len_t n)
{
   len_t i;
   dword_t s, t = 0;
   word_t ci = 0;

   b += n - 1;

   nn_zero(p, n);

   for (i = 0; i < n; i++, b--)
   {
      if (ci) t -= (dword_t) nn_sub1(p, p, n, b[0]);
      s = (dword_t) a1[i] + (dword_t) a2[i] + (dword_t) ci;
      r[i] = (word_t) s;
      ci = (s >> WORD_BITS);  
   }

   for ( ; i < 2*n - 1; i++, b--)
   {
       if (ci) t += (dword_t) b[n];
       s = (dword_t) a1[i] + (dword_t) a2[i] + (dword_t) ci;
       r[i] = (word_t) s;
       ci = (s >> WORD_BITS);
   }

   if (ci) t += (dword_t) b[n];

   ov[0] = (word_t) t;
   ov[1] = (t >> WORD_BITS);

   return ci;
}


void nn_mulmid_kara(nn_t ov, nn_t p, nn_src_t a, len_t m, nn_src_t b, len_t n)
{
  len_t i, n2 = n/2, odd = (n & 1), extra = m - 4*n2 + 1 - odd;
  nn_t s, p0, p1, p2, f, ex = NULL;
  int neg = 0;
  nn_t ptr;
  dword_t t;
  word_t ci, tmp[2], tmp2[2];

  TMP_INIT;

  if (n <= MULMID_CLASSICAL_CUTOFF)
  {
     nn_mulmid_classical(ov, p, a, m, b, n);
     return;
  }

  if (nn_cmp_m(b, b + n2, n2) < 0)
     neg = 1;

  TMP_START;

  s = (nn_t) TMP_ALLOC(2*n2 - 1);
  p0 = (nn_t) TMP_ALLOC(n2 + 2);
  p1 = (nn_t) TMP_ALLOC(n2 + 2);
  p2 = (nn_t) TMP_ALLOC(n2 + 2);
  f = (nn_t) TMP_ALLOC(n2 + 2);

  if (extra) ptr = tmp2, ex = (nn_t) TMP_ALLOC(extra);
  else ptr = ov;

  if (odd) a++;

  /* p0 = (a0 + a1)*b1 */
  _nn_mulmid_add_lfix_m(s, f + n2, f, a, a + n2, b + n2, n2);
  nn_mulmid_kara(p0 + n2, p0, s, 2*n2 - 1, b + n2, n2);
  nn_add_m(p0, p0, f, n2 + 2);

  /* p1 = a1*(b0 - b1) */
  if (neg) _nn_mulmid_sub_rfix_m(s, f + n2, f, a + n2, b + n2, b, n2);
  else _nn_mulmid_sub_rfix_m(s, f + n2, f, a + n2, b, b + n2, n2);
  nn_mulmid_kara(p1 + n2, p1, a + n2, 2*n2 - 1, s, n2);
  nn_sub_m(p1, p1, f, n2 + 2);

  /* p2 = (a1 + a2)*b0 */
  _nn_mulmid_add_lfix_m(s, f + n2, f, a + n2, a + 2*n2, b, n2);
  nn_mulmid_kara(p2 + n2, p2, s, 2*n2 - 1, b, n2);
  nn_add_m(p2, p2, f, n2 + 2);

  /* r0 = p0 + p1, r1 = p2 - p1 */
  if (neg) 
  {
     nn_sub_m(p, p0, p1, n2 + 2);
     tmp[0] = p[n2], tmp[1] = p[n2 + 1];
     ci = nn_add_m(p + n2, p2, p1, n2);
     nn_add_mc(ptr, p2 + n2, p1 + n2, 2, ci);
  } else 
  {
     nn_add_m(p, p0, p1, n2 + 2);
     tmp[0] = p[n2], tmp[1] = p[n2 + 1];
     ci = nn_sub_m(p + n2, p2, p1, n2);
     nn_sub_mc(ptr, p2 + n2, p1 + n2, 2, ci);
  }
  
  ci = nn_add(p + n2, p + n2, n2, tmp, 2);  
  nn_add1(ptr, ptr, 2, ci);

  if (extra)
  {
     a += 4*n2 - 1;

     t = (dword_t) nn_mul1(ex, a, extra, b[0]);
     for (i = 1, a--; i < 2*n2; i++, a--)
        t += (dword_t) nn_addmul1(ex, a, extra, b[i]);

     if (extra == 1)
        t += (dword_t) nn_add1(p + 2*n2, ex, 1, ptr[0]) + (dword_t) ptr[1];
     else
        t += (dword_t) nn_add(p + 2*n2, ex, extra, ptr, 2);
     
     if (odd)
     {
        a -= 2*n2;
        t += nn_addmul1(p, a, 2*n2 + extra, b[i]);
     }

     ov[0] = (word_t) t;
     ov[1] = (word_t) (t >> WORD_BITS);
  }

  TMP_END;
}

static inline
word_t nn_divapprox_preinv_c(
    nn_t q, nn_t a, len_t m, 
    nn_src_t d, len_t n, preinv2_t dinv, word_t ci
);

word_t nn_divapprox_divconquer_preinv_c(nn_t q, nn_t a, len_t m, nn_src_t d,
                                            len_t n, preinv2_t dinv, word_t ci)
{
   len_t s = m - n + 1;
   len_t sh, sl;
   nn_t t;
   len_t i;

   TMP_INIT;

   /* special case, s <= 3 */
   if (s <= 3 || n <= 5) return nn_divapprox_classical_preinv_c(q, a, m, d, n, dinv, ci);

   /* Reduce until n - 2 >= s */
   while (n - 2 < s)
   {
      sh = BSDNT_MIN(n, s - n + 2);
      nn_divrem_divconquer_preinv_c(q + s - sh, a + m - n - sh + 1,
                                                   n + sh - 1, d, n, dinv, ci);
      s -= sh; m -= sh;
      ci = a[m];
   }

   /* split into two parts */
   sh = s/2; sl = s - sh;

   /* Rare case where truncation ruins normalisation */
   if (ci > d[n - 1] || (ci == d[n - 1]
     && nn_cmp_m(a + m - s + 1, d + n - s, s - 1) >= 0))
      return _nn_divapprox_helper(q, a + m - s - 1, d + n - s - 1, s);

   ci = nn_divapprox_preinv_c(q + sl, a + sl, n + sh - 1, d, n, dinv, ci);

   TMP_START;
   t = (nn_t) TMP_ALLOC(sl + 2);

   nn_mulmid_kara(t + sl, t, d + n - s - 1, s - 1, q + sl, sh);
   ci -= nn_sub_m(a + m - s - 1, a + m - s - 1, t, sl + 2);

   TMP_END;

   if ((sword_t) ci < 0)
   {

      nn_sub1(q + sl, q + sl, sh, 1); /* ensure quotient is not too big */

      /*
         correct remainder, noting that "digits" of quotient aren't base B
         but in base varying with truncation, thus correction needs fixup
      */
      ci += nn_add_m(a + m - s - 1, a + m - s - 1, d + n - sl - 2, sl + 2);

      for (i = 0; i < sh - 1 && q[sl + i] == ~WORD(0); i++)
         ci += nn_add1(a + m - s - 1, a + m - s - 1, sl + 2, d[n - sl - 3 - i]);
   }

   if (ci != 0 || nn_cmp_m(a + sl, d, n) >= 0) /* special case: unable to canonicalise */
      return _nn_divapprox_helper(q, a + m - s - 1, d + n - sl - 1, sl);

   ci = nn_divapprox_preinv_c(q, a, n + sl - 1, d, n, dinv, a[m - sh]);

   return ci;
}

/*
   As per nn_divapprox_classical_preinv_c.
*/
static inline
word_t nn_divapprox_preinv_c(nn_t q, nn_t a, len_t m, 
                          nn_src_t d, len_t n, preinv2_t dinv, word_t ci)
{
   if (m - n + 1 <= DIVAPPROX_CLASSICAL_CUTOFF || n == 1)
      return nn_divapprox_classical_preinv_c(q, a, m, d, n, dinv, ci);
   else
      return nn_divapprox_divconquer_preinv_c(q, a, m, d, n, dinv, ci);
}

void nn_divrem_divconquer_preinv_c(nn_t q, nn_t a, len_t m, nn_src_t d,
                                            len_t n, preinv2_t dinv, word_t ci)
{
   len_t sh, s = m - n + 1;
   nn_t t;

   TMP_INIT;

   /* Base case */
   if (n <= 3 || s <= 1)
   {
      nn_divrem_classical_preinv_c(q, a, m, d, n, dinv, ci);
      return;
   }

   /* Reduce until n - 2 >= s */
   while (n - 2 < s)
   {
      sh = BSDNT_MIN(n, s - n + 2);
      nn_divrem_preinv_c(q + s - sh, a + m - n - sh + 1,
                                                   n + sh - 1, d, n, dinv, ci);
      s -= sh; m -= sh;
      ci = a[m];
   }

   ci = nn_divapprox_preinv_c(q, a, m, d, n, dinv, ci);

   TMP_START;
   t = (nn_t) TMP_ALLOC(n);

   if (s > 0)
   {
      nn_mullow_kara(t + n - 2, t, d, n - 2, q, s);
      ci -= nn_sub_m(a, a, t, n);
   }

   TMP_END;

   while ((sword_t) ci < 0)
   {
      nn_sub1(q, q, s, 1); /* ensure quotient is not too big */

      ci += nn_add_m(a, a, d, n);
   }
}

/*
   Given a double word u, a normalised divisor d and a precomputed
   inverse dinv of d, computes the quotient and remainder of u by d.
*/
#define divrem21_preinv1(q, r, u_hi, u_lo, d, dinv) \
   do { \
      const dword_t __u = (((dword_t) u_hi) << WORD_BITS) + (dword_t) u_lo; \
      dword_t __r, __q1 = (dword_t) u_hi * (dword_t) (dinv) + __u; \
      const dword_t __q0 = (dword_t) u_lo * (dword_t) (dinv); \
      __q1 += (dword_t) ((__q0) >> WORD_BITS); \
      (q) = (__q1 >> WORD_BITS); \
      __r = __u - (dword_t) (d) * (dword_t) (q); \
      while ((word_t) (__r >> WORD_BITS) || ((word_t) __r >= (d))) \
      { \
         __r -= (dword_t) (d); \
         (q)++; \
      } \
      (r) = (word_t) __r; \
   } while (0)

word_t nn_divrem1_preinv_c(nn_t q, nn_src_t a, len_t m, 
                            word_t d, preinv1_t dinv, word_t ci)
{
   long i;
   
   for (i = m - 1; i >= 0; --i)
      divrem21_preinv1(q[i], ci, ci, a[i], d, dinv);

   return ci;
}

void nn_divrem(nn_t q, nn_t a, len_t m, nn_src_t d, len_t n) {
   word_t norm, ci = 0;
   nn_t t;

   TMP_INIT;

   TMP_START;

   if ((norm = high_zero_bits(d[n - 1])))
   {
      t = (nn_t) TMP_ALLOC(n);
      ci = nn_shl(a, a, m, norm);
      nn_shl(t, d, n, norm);
   } else
      t = (nn_t) d;

   if (n == 1)
   {
      preinv1_t inv = precompute_inverse1(t[0]);
      a[0] = nn_divrem1_preinv_c(q, a, m, t[0], inv, ci);
   } else
   {
      preinv2_t inv = precompute_inverse2(t[n - 1], t[n - 2]);
      nn_divrem_divconquer_preinv_c(q, a, m, t, n, inv, ci);
   }

   if (norm)
      nn_shr(a, a, n, norm);

   TMP_END;
}

word_t nn_divrem1_simple_c(nn_t q, nn_src_t a, len_t m, word_t d, word_t ci)
{
   dword_t t;
   long i;

   for (i = m - 1; i >= 0; i--)
   {
      t = (((dword_t) ci) << WORD_BITS) + (dword_t) a[i];
      q[i] = t / (dword_t) d;
      ci = (word_t) (t % (dword_t) d);
   }

   return ci;
}

char * nn_get_str(nn_src_t a, len_t m)
{
   /* 9.63... is log_10(2^32) */
   size_t i = 0, j;
   size_t digits = (long) ceil(m * 9.632959861247398 * (WORD_BITS/32)) + (m == 0);
   char * str = (char *) malloc(digits + 1);
   word_t ci, d = 10UL << (WORD_BITS - 4);
   nn_t q1, q2, t;
   TMP_INIT;

   if (m == 0)
      str[0] = '0';
   else 
   {
      TMP_START;
      q1 = (nn_t) TMP_ALLOC(m);
      q2 = (nn_t) TMP_ALLOC(m);
      nn_copy(q1, a, m);

      /* compute digits in reverse order */
      for (i = digits; m > 0; i--) 
      {
         ci = nn_shl(q1, q1, m, WORD_BITS - 4);
         str[i - 1] = 48 + (char) (nn_divrem1_simple_c(q2, q1, m, d, ci) >> (WORD_BITS - 4));
         t = q1; q1 = q2; q2 = t;
         m = nn_normalise(q1, m);
      }

      TMP_END;

      /* didn't get the right number of digits, shift */
      if (i) 
      {
         for (j = i; j < digits; j++)
            str[j - i] = str[j];
      }
   }

   str[digits - i] = '\0';

   return str;
}


////////////////////////////////////////////////////////////////////////////////
//  Crash

noreturn void crash(char *s) {
  printf("Error: %s\n", s);
  exit(1);
}


// Heap ////////////////////////////////////////////////////////////////////////

#define HEAP_MAP_SZ (1ULL << 40) // 1 TB
#define BLOCK_SZ    65536

// tospace and fromspace are swapped on every GC.

static char *tospace     = (char*) (1ULL << 24);
static char *hp          = (char*) (1ULL << 24);
static char *fromspace   = (char*) (1ULL << 41);
static char *tospace_end = (char*) ((1ULL << 24) + BLOCK_SZ);

static void gc();

// argument is in bytes, but must be a multiple of 8.
static inline void *alloc(size_t bytes) {
 again:
  char *res = hp;
  hp += bytes;
  if (hp > tospace_end) { gc(); goto again; }
  return res;
}


////////////////////////////////////////////////////////////////////////////////
//  Typedefs

typedef uint64_t u64;

// Note that underlying enum number for NAT, PIN, LAW, APP are in
// sort-order.
typedef enum Type {
  NAT,
  PIN,
  LAW,
  APP,
  IND,
  MOV,
} Type;

typedef enum NatType {
  SMALL,
  BIG
} NatType;

typedef struct BigNat { len_t size; } BigNat;

struct Value;

typedef struct Value Value;

typedef enum JetTag {
  J_ADD,
  J_SUB,
  J_MUL,
  J_DIV,
  J_MOD,
  J_DEC,
  J_CMP,
  J_NONE,
} JetTag;

typedef struct Pin {
  Value *item;
  JetTag jet;
} Pin;

typedef struct LawWeight {
    u64 n_lets;
    u64 n_calls;
} LawWeight;

typedef struct Law {
  Value *n; // Always a nat
  Value *a; // Always a nat
  Value *b;
  LawWeight w;
} Law;

typedef struct App {
  Value *f;
  Value *g;
} App;

struct Value {
  Type type;
  union {
    Pin p;    // PIN
    Law l;    // LAW
    App a;    // APP
    BigNat n; // NAT
    Value *i; // IND
  };
};

////////////////////////////////////////////////////////////////////////////////
//  Prototypes

int call_depth = 0;

char dot_lab[1024];

#define TRACE_JET_MATCHES  0
#define TRACE_CALLS        0
#define TRACE_LAWS         0
#define STACK_BOUNDS_CHECK 0
#define CHECK_TAGS         0
#define CHECK_DIRECT       0

void write_dot(char *);

Value *normalize (Value*);
JetTag jet_match(Value*);

static void push_word(u64);
static Value *DIRECT(u64);

static void swap(void);
static void mk_app(void);
static void clone(void);
static Value *pop(void);
static Value *get(u64);
static Value *get_deref(u64);
static Value *pop_deref(void);
static void slide(u64);
static void update(u64);
static void push(u64);
static void push_val(Value*);
static Value **get_ptr(u64);

void BigPlusDirect(u64, u64);
void force();
bool eval();
void eval_update(int);
static void force_in_place();

void write_dot_extra(char*, char*, Value*);

void frag_load(Value**, u64, int*, u64*, u64**);
bool read_exp(FILE *f);

////////////////////////////////////////////////////////////////////////////////
//  Globals

#define STACK_SIZE 65536
Value *stack[STACK_SIZE];
u64 sp = 0;

////////////////////////////////////////////////////////////////////////////////
//  Nat pointer tagging (ptr-nat)

// if the high bit is set, then the remaining 63 bits should be interpreted as
// a nat. this is simpler than having to modify all pointers to mask/unmask
// their high bit.

// 2^63 - high bit
# define PTR_NAT_MASK          9223372036854775808ull
# define DIRECT_ZERO  ((Value*)9223372036854775808ull)
# define DIRECT_ONE   ((Value*)9223372036854775809ull)
# define DIRECT_TWO   ((Value*)9223372036854775810ull)

static inline bool is_direct(Value *x) {
  return (((u64) x) & PTR_NAT_MASK);
}

static inline u64 get_direct(Value *x) {
  return (u64) (((u64) x) & ~PTR_NAT_MASK);
}

////////////////////////////////////////////////////////////////////////////////
//  Accessors

static Value *deref(Value *x);

static inline void ck_pin(char *fn_nm, Value *x) {
  char s[14];
  sprintf(s, "%s not a PIN!", fn_nm);
  if (x->type != PIN) crash(s);
}

// we allow PIN LAWs
static inline void ck_law(char *fn_nm, Value *x) {
  char s[28];
  sprintf(s, "%s not a LAW or PIN-LAW!", fn_nm);
  if (x->type == LAW) return;
  if (x->type == PIN) {
    return ck_law(fn_nm, x->i);
  }
  crash(s);
}

static inline void ck_app(char *fn_nm, Value *x) {
  char s[15];
  sprintf(s, "%s not an APP!", fn_nm);
  if (x->type != APP) crash(s);
}

static inline void ck_nat(char *fn_nm, Value *x) {
  char s[14];
  sprintf(s, "%s not a NAT!", fn_nm);
  if (x->type != NAT) crash(s);
}

static inline void ck_ind(char *fn_nm, Value *x) {
  char s[14];
  sprintf(s, "%s not a IND!", fn_nm);
  if (x->type != IND) crash(s);
}

static inline Type TY(Value *x) {
  if (is_direct(x)) return NAT;
  return x->type;
}

static inline bool IS_NAT(Value *x) {
  return (TY(x) == NAT);
}

static inline Value *IT(Value *x) {
  x = deref(x);
  #if CHECK_TAGS
  ck_pin("IT", x);
  #endif
  return x->p.item;
};

static inline Value *NM(Value *x) {
  x = deref(x);
  #if CHECK_TAGS
  ck_law("NM", x);
  #endif
  if (x->type == PIN) return NM(x->i);
  return x->l.n;
}

static inline Value *AR(Value *x) {
  x = deref(x);
  #if CHECK_TAGS
  ck_law("AR", x);
  #endif
  if (x->type == PIN) return AR(x->i);
  return x->l.a;
}

static inline Value *BD(Value *x) {
  x = deref(x);
  #if CHECK_TAGS
  ck_law("BD", x);
  #endif
  if (x->type == PIN) return BD(x->i);
  return x->l.b;
}

static inline Law FUNC(Value *x) {
  x = deref(x);
  if (x->type == PIN) return FUNC(x->i);
  return x->l;
}

static inline Value *HD(Value *x) {
  x = deref(x);
  #if CHECK_TAGS
  ck_app("HD", x);
  #endif
  return x->a.f;
};

static inline Value *TL(Value *x) {
  x = deref(x);
  #if CHECK_TAGS
  ck_app("TL", x);
  #endif
  return x->a.g;
};

static inline Value *IN(Value *x) {
  #if CHECK_TAGS
  ck_ind("IN", x);
  #endif
  return x->i;
};

static inline len_t WID(Value *v) {
  return v->n.size;
}

static inline word_t *BUF(Value *v) {
  return (void*) (&(v->n.size) + 1);
}


////////////////////////////////////////////////////////////////////////////////
//  Printing

void check_nat(Value *v) {
  if (v == NULL) crash("check_nat: NULL");

  if (is_direct(v)) return;

  if (v->type != NAT) crash("check_nat: not nat");

  word_t sz = v->n.size;

  if (sz == 0) crash("check_nat: bignat zero");

  if (sz == 1) {
    if (BUF(v)[0] < PTR_NAT_MASK) {
      crash("check_nat: direct atom encoded as bignat");
    }
    return;
  }

  if (BUF(v)[sz - 1] == 0) {
    crash("check_nat: bad size (high word is zero)");
  }
}

void check_value(Value *v) {
  if (v == NULL) crash("check_value: NULL");

  if (is_direct(v)) return;

  if ((char*)v < tospace) {
    fprintf(stderr, "check_value: %p is before the heap", v);
    crash("check_value");
  }

  if ((char*)v >= tospace_end) {
    fprintf(stderr, "check_value: %p is past the heap", v);
    crash("check_value");
  }

  switch (TY(v)) {
    case PIN:
      check_value(IT(v));
      break;
    case LAW:
      check_nat(NM(v));
      check_nat(AR(v));
      check_value(BD(v));
      break;
    case APP:
      check_value(HD(v));
      check_value(TL(v));
      break;
    case NAT:
      check_nat(v);
      break;
    case IND:
      check_value(IN(v));
      break;
    default:
      crash("BAD VALUE TAG");
  }
}

////////////////////////////////////////////////////////////////////////////////
//  Construction

// just allocates the space. caller must fill buf.
Value *start_bignat_alloc(size_t num_words) {
  // tag size words..
  Value *res = (Value *)alloc(8 * (2 + num_words));
  res->type   = NAT;
  res->n.size = num_words;
  return res;
}

static inline void abort_bignat_alloc(Value *v) {
  hp -= ((2 + v->n.size) * 8);
}

// shrinks a "candidate" bignat and DECREASES THE SIZE OF THE HEAP so
// that the next thing will be allocated in the right place.
Value *end_bignat_alloc(Value *v) {
  size_t old_sz = v->n.size;
  size_t sz     = old_sz;
  word_t *buf   = BUF(v);

  while (sz && buf[sz - 1] == 0) sz--;

  if (sz == 0) {
    abort_bignat_alloc(v);
    return DIRECT_ZERO;
  }

  if (sz == 1 && 0 == (buf[0] >> 63)) {
    abort_bignat_alloc(v);
    return DIRECT(buf[0]);
  }

  if (sz == old_sz) return v;

  v->n.size = sz;            // shrink size
  hp -= (8 * (old_sz - sz)); // shrink heap
  return v;
}

static inline Value *DIRECT(u64 x) {
  #if CHECK_DIRECT
  if (x & PTR_NAT_MASK) crash("DIRECT: too big");
  #endif

  return (Value *) (x | PTR_NAT_MASK);
}

static inline void push_word(u64 x) {
  if (!(x & PTR_NAT_MASK)) {
    push_val((Value *) (x | PTR_NAT_MASK));
    return;
  }

  Value *res = (Value *)alloc(3 * 8);
  res->type   = NAT;
  res->n.size = 1;
  BUF(res)[0] = x;
  push_val(res);
}

static inline Value *a_Pin(Value *item) {
  push_val(item);
  Value *res = (Value *)alloc(sizeof(Value));
  item = pop();
  res->type = PIN;
  JetTag jet = jet_match(item);
  res->p = (Pin){ .item = item, .jet = jet };
  return res;
}

static inline Value *a_Law(Law l) {
  push_val(l.n);
  push_val(l.a);
  push_val(l.b);
  Value *res = (Value *)alloc(sizeof(Value));
  l.b = pop();
  l.a = pop();
  l.n = pop();
  *res = (Value){ .type = LAW, .l = l };
  return res;
}

////////////////////////////////////////////////////////////////////////////////
//  Nat Operators

int less=0, equals=1, greater=2;

static inline int cmp_direct(u64 a, u64 b) {
  if (a == b) return equals;
  if (a < b) return less;
  return greater;
}

static inline int big_cmp(Value *a, Value *b) {
  if (WID(a) != WID(b)) {
    return (WID(a) < WID(b)) ? less : greater;
  }

  int nnres = nn_cmp_m(BUF(a), BUF(b), WID(a));

  if (nnres < 0) return less;
  if (nnres == 0) return equals;
  return greater;
}

int cmp_recur(Value *a, Value *b) {
 tail_recur:
  a=deref(a), b=deref(b);

  if (is_direct(a))
    return (!is_direct(b))
             ? less
             : cmp_direct(get_direct(a), get_direct(b));

  if (is_direct(b)) return greater;

  if (a->type < b->type) return less;
  if (a->type > b->type) return greater;

  switch (a->type) {
  case NAT:
    return big_cmp(a, b);

  case PIN:
    a=IT(a); b=IT(b); goto tail_recur;

  case LAW:
    {
      int ord;
      if (b->type != LAW) return less;
      ord = cmp_recur(NM(a), NM(b));
      if (ord != 1) return ord;
      ord = cmp_recur(AR(a), AR(b));
      if (ord != 1) return ord;
      a=BD(a); b=BD(b); goto tail_recur;
    }

  case APP:
    {
      int ord = cmp_recur(HD(a), HD(b));
      if (ord != 1) return ord;
      a=TL(a); b=TL(b); goto tail_recur;
    }
  default:
    crash("cmp: impossible");
  }
}

// fast path for direct atoms, fallback to full cmp routine.
static inline int cmp_normalized(Value *a, Value *b) {
  if (is_direct(a) && is_direct(b))
    return cmp_direct(get_direct(a), get_direct(b));

  return cmp_recur(a,b);
}

static inline bool LT(Value *a, Value *b) {
  return cmp_normalized(a,b) == 0;
}

static inline bool GT(Value *a, Value *b) {
  return cmp_normalized(a,b) == 2;
}

static inline bool LTE(Value *a, Value *b) {
  return cmp_normalized(a,b) != 2;
}

static inline bool GTE(Value *a, Value *b) {
  return cmp_normalized(a,b) != 0;
}

static inline bool EQ(Value *a, Value *b) {
  return cmp_normalized(a,b) == 1;
}

static inline bool NEQ(Value *a, Value *b) {
  return cmp_normalized(a,b) != 1;
}

static inline bool EQZ(Value *x) {
   return (x == DIRECT_ZERO);
}

static inline bool EQ1(Value *x) {
  return (x == DIRECT_ONE);
}

static inline bool EQ2(Value *x) {
  return (x == DIRECT_TWO);
}

// TODO change to `Value *` arg style of Mul/DivMod/etc
//
// invariant: a.size >= b.size
// stack before: ..rest b a
// stack after:  ..rest (a+b)
void BigPlusBig(u64 aSize, u64 bSize) {
  long new_size = MAX(aSize, bSize) + 1;
  Value *res = start_bignat_alloc(new_size);
  word_t *buf = BUF(res);
  Value *a = pop_deref();
  Value *b = pop_deref();
  word_t c = nn_add_c(buf, BUF(a), a->n.size, BUF(b), b->n.size, 0);
  buf[new_size - 1] = c;
  push_val(end_bignat_alloc(res));
}

void BigPlusDirect(u64 small, u64 bigSz) {
  u64 newSz       = bigSz + 1;
  Value *res      = start_bignat_alloc(newSz); // gc
  Value *big      = pop();
  word_t carry    = nn_add1(BUF(res), BUF(big), bigSz, small);
  BUF(res)[bigSz] = carry;
  push_val(end_bignat_alloc(res));
}

// arguments must both have already been evaluated and coerced into nats.
void Add() {
  Value *a = pop();
  Value *b = pop();

  u64 aSmall = get_direct(a);
  u64 bSmall = get_direct(b);

  if (is_direct(a)) {
    if (is_direct(b)) {
      // no need to handle overflow, since u63 + u63 always fits in a u64.
      push_word(aSmall + bSmall);
      return;
    }

    push_val(b);
    BigPlusDirect(aSmall, b->n.size);
    return;
  }

  if (is_direct(b)) {
    push_val(a);
    BigPlusDirect(bSmall, a->n.size);
    return;
  }

  push_val(b);
  push_val(a);
  BigPlusBig(a->n.size, b->n.size);
}

void BigMinusDirect(Value *big, u64 direct) {
  u64 bigSz = big->n.size;
  push_val(big);                           // save
  Value *res  = start_bignat_alloc(bigSz); // gc
  big         = pop();                     // reload
  word_t *buf = BUF(res);
  word_t c = nn_sub1(buf, BUF(big), bigSz, direct);
  // a positive borrow (nonzero `c`) should only be possible if we
  // underflowed a single u64. our invariant is to convert to SMALL when we
  // reach 1 u64, so we should never encounter this case.
  assert (c == 0);
  push_val(end_bignat_alloc(res));
}

void Dec() {

  Value *v = pop_deref();

  if (is_direct(v)) {
    u64 n = get_direct(v);
    push_val( (n == 0) ? DIRECT_ZERO : DIRECT(n - 1) );
    // the result is always direct because (x/u63 - 1) is always a u63
    // unless x==0.
  } else {
    BigMinusDirect(v, 1);
  }
}

void Sub() {
  Value *a = pop();
  Value *b = pop();

  u64 aSmall = get_direct(a);
  u64 bSmall = get_direct(b);

  if (is_direct(a)) {
    if (is_direct(b)) {
      if (bSmall >= aSmall) {
        push_val(DIRECT_ZERO);
        return;
      }
      push_word(aSmall - bSmall);
      return;
    }
    push_val(DIRECT_ZERO);
    return;
  }

  if (is_direct(b)) {
    BigMinusDirect(a, bSmall);
    return;
  }

  u64 aSz = a->n.size;
  u64 bSz = a->n.size;

  if (aSz < bSz) {
    push_val(DIRECT_ZERO);
    return;
  }

  // Big - Big

  push_val(b);
  push_val(a);
  Value *res  = start_bignat_alloc(aSz); // gc
  a = pop();
  b = pop();

  word_t *buf = BUF(res);

  word_t borrow = nn_sub_c(buf, BUF(a), a->n.size, BUF(b), b->n.size, 0);
  if (borrow) {
    abort_bignat_alloc(res);
    push_val(DIRECT_ZERO);
  } else {
    push_val(end_bignat_alloc(res));
  }
}

void DirectTimesDirect(u64 a, u64 b) {
  if (a==0 || b==0) {
    push_val(DIRECT_ZERO);
    return;
  }

  u64 res = a * b;

  // if no overflow
  if ((res / a) == b) { // TODO does this always work?
    push_word(res);
    return;
  }

  Value *ret  = start_bignat_alloc(2); // gc
  word_t *buf = BUF(ret);
  buf[1] = nn_mul1(buf, &a, 1, b);
  push_val(end_bignat_alloc(ret));
}

// call alloc to reserve words
// fill in data
// truncate
// decrease hp.

void BigTimesDirect(u64 small, Value *big) {
  u64 newSz = big->n.size + 1;
  push_val(big);                          // save pointer to stack
  Value *res = start_bignat_alloc(newSz); // gc
  big = pop();                            // reload pointer
  word_t *buf = BUF(res);
  nn_zero(buf, newSz);
  word_t carry = nn_mul1(buf, BUF(big), big->n.size, small);
  buf[big->n.size] = carry;
  push_val(end_bignat_alloc(res));
}

void BigTimesBig(Value *a, Value *b) {
  long new_size = a->n.size + b->n.size;
  push_val(a);                               // save pointer
  push_val(b);                               // save pointer
  Value *res = start_bignat_alloc(new_size); // gc
  b = pop();                                 // reload pointer
  a = pop();                                 // reload pointer
  word_t *buf = BUF(res);
  nn_zero(buf, new_size);
  nn_mul_classical(buf, BUF(a), a->n.size, BUF(b), b->n.size);
  push_val(end_bignat_alloc(res));
}

void Mul() {
  Value *a = pop();
  Value *b = pop();

  u64 aSmall = get_direct(a);
  u64 bSmall = get_direct(b);

  if (is_direct(a)) {
    if (is_direct(b)) DirectTimesDirect(aSmall, bSmall);
    else BigTimesDirect(aSmall, b);
    return;
  }

  if (is_direct(b)) BigTimesDirect(bSmall, a);
  else BigTimesBig(a, b);
}

void DivModDirectDirect(u64 a, u64 b) {
  if (b == 0) {
    // we could crash here instead
    push_val(DIRECT_ZERO); // mod
    push_val(DIRECT_ZERO); // div
    return;
  }

  push_word(a % b); // mod
  push_word(a / b); // div
}

void DivModBigDirect(Value *a, u64 b) {
  if (b == 0) {
    // we could crash here instead
    push_val(DIRECT_ZERO); // mod
    push_val(DIRECT_ZERO); // div
    return;
  }
  long sz = a->n.size;

  push_val(a);                         // save a
  Value *res = start_bignat_alloc(sz); // gc
  a = pop();                           // restore a

  word_t *buf = BUF(res);
  nn_zero(buf, sz);
  word_t mod = nn_divrem1_simple(buf, BUF(a), sz, b);
  push_val(end_bignat_alloc(res)); // div
  push_word(mod);                  // mod
  swap();
  // need the swap() becuause push_word(mod) can invalidate
}

void DivModBigBig(Value *a, Value *b) {
  long aSz = WID(a);
  long bSz = WID(b);

  if (aSz < bSz) {
    push_val(a);           // mod
    push_val(DIRECT_ZERO); // div
    return;
  }

  // Copy a's words into a working buffer (which will be mutated by
  // `nn_divrem`).  TODO HACK: can stack overflow.
  word_t tmp[aSz];
  nn_copy(tmp, BUF(a), aSz);

  long sz = aSz - bSz + 1;

  push_val(b);                            // save
  Value *divres = start_bignat_alloc(sz); // gc
  b = pop();                              // restore

  word_t *buf = BUF(divres);
  nn_zero(buf, sz);

  nn_divrem(buf, tmp, aSz, BUF(b), bSz);

  push_val(end_bignat_alloc(divres));

  Value *modres = start_bignat_alloc(bSz);
  nn_copy(BUF(modres), tmp, bSz);
  push_val(end_bignat_alloc(modres));

  swap();
}

// stack before: ..rest b a
// stack after:  ..rest (a%b) (a/b)
void DivMod() {
  Value *a = pop();
  Value *b = pop();

  u64 aSmall = get_direct(a);
  u64 bSmall = get_direct(b);

  if (is_direct(a)) {
    if (is_direct(b)) DivModDirectDirect(aSmall, bSmall);
    else {
      push_val(a);           // mod
      push_val(DIRECT_ZERO); // div
    }
    return;
  }

  if (is_direct(b)) DivModBigDirect(a, bSmall);
  else DivModBigBig(a, b);
}

// stack before: ..rest b a
// stack after:  ..rest (a/b)
void Div() {
  DivMod();
  slide(1);
}

// stack before: ..rest b a
// stack after:  ..rest (a%b)
void Mod() {
  DivMod();
  pop();
}

////////////////////////////////////////////////////////////////////////////////
//  Jets

typedef struct Jet {
  Value *name; // if this is ever not direct, a more complex solution
               // will be required.
  u64 arity;
  JetTag tag;
} Jet;

static inline void to_nat(int i) {
  eval_update(i);
  Value **p = get_ptr(i);
  if (!IS_NAT(*p)) { *p = DIRECT_ZERO; }
}

static inline void force_in_place(int i) {
  push(i);
  force();
  Value **p = get_ptr(i);
  *p = deref(*p);
}

// causes a stack slot to be updated (and dereferenced) in place,
// otherwise leaving the stack shape the same as it was before.
void eval_update(int i) {
  Value **p = get_ptr(i);
 again:
  if (is_direct(*p)) return;
  switch ((**p).type) {
  case IND:
    *p = deref(*p); // update the stack slot to not be indirect.
    goto again;
  case APP:
    push(i);
    bool did_eval = eval();
    if (did_eval) {
      update(i+1);
      *p = deref(*p); // never leave an indirection on the stack.
    } else {
      pop();
    }
    return;
  default:
    return;
  }
}

#define ADD   (Value*)9223372036861355073ULL
#define SUB   (Value*)9223372036861228371ULL
#define MUL   (Value*)9223372036861883725ULL
#define DIV   (Value*)9223372036862536004ULL
#define MOD   (Value*)9223372036861357901ULL
#define DEC   (Value*)9223372036861289796ULL
#define CMP   (Value*)9223372036862143811ULL

#define NUM_JETS 7
Jet jet_table[NUM_JETS] =
  { (Jet) { .name = ADD,   .arity = 2, .tag = J_ADD   }
  , (Jet) { .name = SUB,   .arity = 2, .tag = J_SUB   }
  , (Jet) { .name = MUL,   .arity = 2, .tag = J_MUL   }
  , (Jet) { .name = DIV,   .arity = 2, .tag = J_DIV   }
  , (Jet) { .name = MOD,   .arity = 2, .tag = J_MOD   }
  , (Jet) { .name = DEC,   .arity = 1, .tag = J_DEC   }
  , (Jet) { .name = CMP,   .arity = 2, .tag = J_CMP   }
  };

////////////////////////////////////////////////////////////////////////////////
//  Seeds

void frag_load_cell(Value **tab, u64 tabSz, int *use, u64 *acc, u64 **mor) {
  frag_load(tab, tabSz, use, acc, mor); // .. f
  frag_load(tab, tabSz, use, acc, mor); // .. f x
  mk_app();                             // .. (f x)
}

u64 u64_bits (u64 w) {
  if (!w) { return 0; }
  return 64 - __builtin_clzll(w);
}

void frag_load(Value **tab, u64 tabSz, int *use, u64 *acc, u64 **mor) {
  u64 isCell = ((*acc >> *use) & 1ULL);

  // move forward by one bit.
  (*use)++;
  if (*use == 64) {
    *use = 0;
    *acc = **mor;
    *mor = (*mor)+1;
  }

  if (isCell) {
    frag_load_cell(tab, tabSz, use, acc, mor);
    return;
  }

  // `tmp` is the remaining bits from acc (high bits) combined
  // with the low bits of the next word.  We mask out the `refSz`
  // low bits from this to get the index into the backrefs table.

  u64 maxref = tabSz-1;
  u64 refSz = u64_bits(maxref);
  int remain = 64 - *use;
  u64 tmp = (remain==64) ? *acc : ((*acc >> *use) | (**mor << remain));// combine
  u64 ref = tmp & ((1ULL << refSz) - 1ULL);                            // mask

  // move forward by refSz bits.
  *use += refSz;
  if (*use >= 64) {
    *use -= 64;
    *acc = **mor;
    *mor = (*mor)+1;
  }

  push_val(tab[ref]);
}

void stack_grow(u64 count) {
  for (u64 i = 0; i < count; i++) {
    push_val(NULL);
  }
}

void seed_load(u64 *inpbuf) {
  u64 n_holes = inpbuf[0];
  u64 n_bigs  = inpbuf[1];
  u64 n_words = inpbuf[2];
  u64 n_bytes = inpbuf[3];
  u64 n_frags = inpbuf[4];

  if (n_holes > 1) {
    fprintf(stderr, "file is just one seed, expected seedpod\n");
    exit(5);
  }

  u64 n_entries = n_bigs + n_words + n_bytes + n_frags + n_holes;

  if (n_entries == 0) crash("empty seed");

  // clever: store working table on stack to make everything GC safe.

  stack_grow(n_entries);
  Value **tab = get_ptr(n_entries-1); // 0

  Value **next_ref = tab;

  if (n_holes) {
    *next_ref++ = a_Pin(DIRECT_ZERO);
  }

  // How big are the bignats?
  u64 bigwidths[n_bigs];
  for (int i=0; i<n_bigs; i++) {
    bigwidths[i] = inpbuf[5+i];
  }

  int used = 5 + n_bigs; // number of words used

  for (int i=0; i<n_bigs; i++) {
    u64 wid       = bigwidths[i];
    Value *bigres = start_bignat_alloc(wid);
    memcpy(BUF(bigres), inpbuf+used, wid*sizeof(u64));
    *next_ref++ = end_bignat_alloc(bigres);
    used += wid;
  }

  for (int i=0; i<n_words; i++) {
    push_word(inpbuf[used++]);
    *next_ref++ = pop();
  }

  {
    uint8_t *byte_buf = (void*) (inpbuf + used);
    for (int i=0; i<n_bytes; i++) {
      push_word(byte_buf[i]);
      *next_ref++ = pop();
    }
    used += (n_bytes / 8);
  }

  int use = 8 * (n_bytes%8);
  u64 acc = inpbuf[used];
  u64 *more = &inpbuf[used+1];

  for (int i=0; i<n_frags; i++) {
    u64 tabSz = (next_ref - tab);
    frag_load_cell(tab, tabSz, &use, &acc, &more);
    *next_ref++ = pop();
  }

  // The top-most entry is the result
  slide(n_entries - 1);
}

u64 *load_seed_file (const char *filename, u64 *sizeOut) {
  FILE *f = fopen (filename, "rb");

  if (!f) {
    fprintf(stderr, "\n%s\n", filename);
    crash("seed file does not exist");
  }

  fseek(f, 0, SEEK_END);
  u64 szBytes = ftell(f);

  u64 szWords = (szBytes / 8) + (szBytes%8 ? 1 : 0);

  fseek(f, 0, SEEK_SET);
  u64 *buf = calloc(szWords+1, 8); // We add an extra word here
                                   // so that we can over-read
                                   // by one word, this simplifies
                                   // decoding.
  if (!buf) crash("load_seed_file: allocation failed");
  if (fread (buf, 1, szBytes, f) != szBytes) crash("load_seed_file: can't read");
  fclose(f);

  *sizeOut = szWords;
  return buf;
}

////////////////////////////////////////////////////////////////////////////////
//  Interpreter stack fns

static inline Value *deref(Value *x) {
  while (TY(x) == IND) {
    x = IN(x);
  }
  return x;
}

static inline Value *pop() {
  #if STACK_BOUNDS_CHECK
  if (sp == 0) crash("pop: empty stack");
  #endif

  sp--;
  return stack[sp];
}

static inline Value *pop_deref() {
  return deref(pop());
}

static inline Value **get_ptr(u64 idx) {
  if (idx >= sp) crash("get: indexed off stack");
  return &stack[(sp-1)-idx];
}

static inline Value *get(u64 idx) {
  return *get_ptr(idx);
}

static inline Value *get_deref(u64 idx) {
  return deref(get(idx));
}

////////////////////////////////////////////////////////////////////////////////
//  GC

static inline size_t alloc_size(Value *x) {
  if (x->type == NAT) return (8 * (2 + WID(x)));
  return sizeof(Value);
}

Value *gc_copy(Value *x) {
  if (x == NULL || is_direct(x))
    return x;

  // if this points into the tospace, we don't need to copy.
  if ((char*)x >= tospace && (char*)x < (tospace + HEAP_MAP_SZ))
    return x;

  if (x->type == MOV) return x->i;

  size_t sz = alloc_size(x);

  // copy + bump heap size
  Value *res = (Value*) hp;
  memcpy(hp, x, sz);
  hp += sz;

  // tell further references where to find the new pointer.
  x->type = MOV;
  x->i = res;

  return res;
}

// Input is always a heap object, so never direct and never null.
static inline void gc_copy_refs(Value *x) {
  switch (x->type) {
  case PIN:
    x->p.item = gc_copy(x->p.item);
    break;
  case LAW:
    x->l.n = gc_copy(x->l.n);
    x->l.a = gc_copy(x->l.a);
    x->l.b = gc_copy(x->l.b);
    break;
  case APP:
    x->a.f = gc_copy(x->a.f);
    x->a.g = gc_copy(x->a.g);
    break;
  case NAT:
    break;
  case IND:
    x->i = gc_copy(x->i);
    break;
  default:
    fprintf(stderr, "gc_copy_refs: bad value: ptr=%p, tag=%d\n", x, x->type);
    crash("gc_copy_refs: impossible");
  }
}

// Cheney's algorithm
static void gc() {
  // swap the two heaps (with the new heap being empty).
  char *tmp = fromspace;
  fromspace = tospace;
  tospace = tmp;
  hp = tospace;

  // copy roots to new heap.
  for (u64 i = 0; i < sp; i++) {
    *get_ptr(i) = gc_copy(get(i));
  }

  // copy all references from the new heap to the old heap
  for (char *iter = tospace; iter < hp; iter += alloc_size((Value*)iter)) {
    gc_copy_refs((Value*) iter);
  }

  long used     = hp - tospace;
  long new_size = BLOCK_SZ * (1 + (used/BLOCK_SZ));
       new_size = new_size + (new_size / 2);
  tospace_end   = tospace + new_size;
}

////////////////////////////////////////////////////////////////////////////////
//  DOT printing

int dot_count = 0;
char *dot_dir_path = "./dot";

char *p_ptr(Value *x) {
  char *buf = malloc(48);
  if (x == NULL) {
    sprintf(buf, "N_null");
  } else if (is_direct(x)) {
    sprintf(buf, "ptr_nat_%lu", get_direct(x));
  } else {
    sprintf(buf, "N_%p", x);
  }
  return buf;
}


////////////////////////////////////////////////////////////////////////////////
//  Interpreter

static void update(u64 idx) {
  Value *head = get_deref(0);
  Value *v    = get_deref(idx);
  if (head != v) {
    // no update needed if equal, and IND on self would form a cycle.
    v->type = IND;
    v->i    = head;
  }
  pop();
}

static inline void push_val(Value *x) { stack[sp] = x; sp++; }
static inline void push(u64 idx)      { push_val(get_deref(idx)); }
static inline void clone()            { push_val(get_deref(0)); }

// before: ..rest f x
// after:  ..rest (f x)
static inline void mk_app() {
  Value *res = (Value *)alloc(sizeof(Value));
  res->type = APP;
  res->a.g = pop();
  res->a.f = pop();
  push_val(res);
}

// before: ..rest x f
// after:  ..rest (f x)
static inline void mk_app_rev() {
  Value *res = (Value *)alloc(sizeof(Value));
  res->type = APP;
  res->a.f = pop();
  res->a.g = pop();
  push_val(res);
}

// before: ..rest x y
// after:  ..rest y x
static inline void swap() {
  Value *n1 = pop();
  Value *n2 = pop();
  push_val(n1);
  push_val(n2);
}

void slide(u64 count) {
  Value *top = get_deref(0);
  sp -= count;
  stack[sp-1] = top;
}

void mk_pin() {
  Value *top = pop_deref();
  Value *p = a_Pin(normalize(top));
  push_val(p);
}

void weigh_law(bool on_spine, LawWeight *out, Value *x) {
 again:
  if (TY(x) != APP) return;                       // neither a let nor a call
  Value *car = HD(x);

  if (TY(car) != APP) return;                     // neither a let nor a call
  Value *caar = HD(car);

  if (on_spine && EQ1(caar)) {                    // ((1 x) b)
    out->n_lets++;                                // this is a let
    weigh_law(0, out, TL(car));                   // weigh the let expr
    x = TL(x);                                    // weigh the let body
    goto again;
  }

  if (EQZ(caar)) {                                // ((0 f) x)
    out->n_calls++;                               // this is a call
    on_spine = false;                             // no more lets
    weigh_law(0, out, TL(car));                   // weigh the call function
    x = TL(x);                                    // weigh the call argument
    goto again;
  }

  return;                                         // neither a let nor a call
}

Value *normalize (Value *v) {
 again:
  if (is_direct(v)) return v;
  switch (v->type) {
  case IND: v = IN(v); goto again;
  case APP:
    v->a.f = normalize(v->a.f);
    v->a.g = normalize(v->a.g);
    return v;
  default: // P/L/N: already normalized
    return v;
  }
}

void mk_law() {
  to_nat(1); // a
  to_nat(2); // n
  Value *b = normalize(pop_deref());
  Value *a = pop_deref();
  Value *n = pop_deref();

  Law l = { .n = n, .a = a, .b=b, .w = { .n_lets = 0, .n_calls = 0 } };

  weigh_law(1, &l.w, b);

  push_val(a_Law(l));
}

void incr() {
  Value *x = pop_deref();

  if (is_direct(x)) {
    // this doesn't need to deal with overflow because get_direct returns
    // a u63, and push_word can handle a u64.
    push_word(get_direct(x) + 1);
    return;
  }

  if (x->type != NAT) {
    push_val(DIRECT_ONE);
    return;
  }

  push_val(x);
  BigPlusDirect(1, x->n.size);
}

void prim_case() {
  Value *o = pop_deref();
  Value *m = pop_deref();
  Value *z = pop_deref();
  Value *a = pop_deref();
  Value *l = pop_deref();
  Value *p = pop_deref();
  switch (TY(o)) {
    case PIN:
      push_val(IT(o)); // o
      push_val(p);     // o p
      mk_app_rev();    // (p o)
      return;
    case LAW:
      push_val(BD(o)); // b
      push_val(AR(o)); // b a
      push_val(NM(o)); // b a n
      push_val(l);     // b a n l
      mk_app_rev();    // b a (l n)
      mk_app_rev();    // b (l n a)
      mk_app_rev();    // (l n a b)
      return;
    case APP:
      push_val(TL(o)); // t
      push_val(HD(o)); // t h
      push_val(a);     // t h a
      mk_app_rev();    // t (a h)
      mk_app_rev();    // (a h t)
      return;
    case NAT: {
      if (EQZ(o)) {
        push_val(z);
        return;
      }
      push_val(m); // m
      push_val(o); // m o
      Dec();       // m d
      mk_app();    // (m d)
      return;
    }
    case IND: crash("plan_case: IND: impossible");
    case MOV:
      crash("MOV escaped GC");
  }
}

void setup_call(u64 depth) {
  // setup the call by pulling the TLs out of all apps which we have
  // unwound.
  for (u64 i = 0; i < depth; i++) {
    stack[(sp-1)-i] = TL(stack[(sp-1)-i]);
  }
}

void flip_stack(u64 depth) {
  if (depth == 0) return;
  Value *tmp;
  u64 d_1 = depth-1;
  for (u64 i = 0; i < depth/2; i++) {
    tmp                   = stack[(sp-1)-i];
    stack[(sp-1)-i]       = stack[(sp-1)-(d_1-i)];
    stack[(sp-1)-(d_1-i)] = tmp;
  }
}

void handle_oversaturated_application(u64 count) {
  // if our application is oversaturated, `depth` will exceed the arity. in this
  // case, we want to re-assemble the apps, and eval the result.
  for (u64 i = 0; i < count; i++) mk_app_rev();
  eval();
}

void backout(u64 depth) {
  // pop stack of unwound apps.
  for (u64 i = 0; i < depth; i++) {
    pop();
  }
  // `eval` saved the outermost APP, and that should now be at the bottom
  // of the stack.
}

Value *kal(u64 maxRef, Value **pool, Value *x) {
  if (is_direct(x)) {
    u64 xv = get_direct(x);
    if (xv > maxRef) return x;                   // unquoted constant
    return get(maxRef - xv);                     // var ref
  }

  if (x->type != APP) return x;                  // unquoted constant

  Value *hx = HD(x);

  if (EQZ(hx)) return TL(x);                     // quoted constant

  if (TY(hx) != APP) return x;                   // unquoted constant

  Value *hhx = HD(hx);

  if (!EQZ(hhx)) return x;                       // unquoted constant

  // (0 f g) is a call.

  Value *f = TL(hx);
  Value *g = TL(x);

  Value *this_call = (*pool)++;                  // allocte (type is preset)
  this_call->type = APP;
  this_call->a.f  = kal(maxRef, pool, f);
  this_call->a.g  = kal(maxRef, pool, g);
  return this_call;
}

// 0 indicates no lets
u64 length_let_spine(Value *x) {
  u64 count = 0;
loop:
  if (TY(x) == APP) {
    Value *car = deref(HD(x));
    if (TY(car) == APP) {
      Value *caar = deref(HD(car));
      if (EQ1(caar)) {
        // ((1 v) k)
        count++;
        x = deref(TL(x));
        goto loop;
      }
    }
  }
  return count;
}

typedef struct GrMem {
  Value *holes;
  Value *apps;
} GrMem;

void eval_law(Law l) {
  u64 args = get_direct(l.a); // this code is unreachable with bignat arity
  u64 lets = l.w.n_lets;
  u64 kals = l.w.n_calls;
  int maxRef = args + lets;

  const size_t bytes = sizeof(Value) * (lets + kals);

  push_val(l.b);                            // save (law body)
  Value *mem = bytes ? alloc(bytes) : NULL; // gc
  Value *b   = pop();                       // restore (law body)

  // initialize letrec slots, since they might be referenced before they
  // are filled in, but leave APPs uninitialized.  KAL will initialize.

  Value *holes = mem;
  Value *apps  = mem + lets;

  if (lets) {
    // Add a black hole per let.
    for (u64 i = 0; i < lets; i++) stack[sp++] = holes+i;

    // Compute the graph of each let, and fill the corresponding hole.
    for (u64 i = 0; i < lets; i++) {
      // (1 exp next)
      Value *next   = TL(b);
      Value *exp    = TL(HD(b));
      b             = next;
      Value *gr     = kal(maxRef, &apps, exp);
      holes[i].type = IND;
      holes[i].i    = gr;
    }

  }

  Value *gr = kal(maxRef, &apps, b);
  push_val(gr);                 // .. self args slots bodyGr
  eval();                       // .. self args slots bodyWhnf
  return slide(maxRef+1);       // .. bodyWhnf
}

void run_law(Value *self, u64 ar) {
  if (TY(self) != PIN) goto no_jet;

  switch (self->p.jet) {

  case J_ADD:
    to_nat(0);
    to_nat(1);
    Add();
    return;

  case J_SUB:
    to_nat(0);
    to_nat(1);
    Sub();
    return;

  case J_MUL:
    to_nat(0);
    to_nat(1);
    Mul();
    return;

  case J_DIV:
    to_nat(0);
    to_nat(1);
    Div();
    return;

  case J_MOD:
    to_nat(0);
    to_nat(1);
    Mod();
    return;

  case J_DEC:
    eval_update(0);
    Dec();
    return;

  case J_CMP:
    // TODO: cmp should only eval as much as needed in order to find
    // a difference.  These force calls are wrong.
    force_in_place(0);
    force_in_place(1);
    Value *a = pop();
    Value *b = pop();
    int ord = cmp_normalized(a, b);
    push_word(ord);
    return;

  default:
    goto no_jet;
  }

 no_jet:
  // self is still valid here, we haven't allocated
  push_val(self);
  flip_stack(ar+1);
  eval_law(FUNC(self));
}

JetTag jet_match(Value *item) {
  item = deref(item);

  if (TY(item) != LAW) return J_NONE;

  Law l = item->l;

  for (int i = 0; i < NUM_JETS; i++) {
    Jet jet = jet_table[i];

    if (NEQ(l.a, DIRECT(jet.arity))) continue;
    if (NEQ(l.n, jet.name)) continue;

    return jet.tag;
  }

  return J_NONE;
}

// returns true if it eval-ed
bool law_step(u64 depth) {
  Value *self = pop_deref();

  if (GT(AR(self), DIRECT(depth))) {
    // unsaturated application. this is a little weird, but works?
    if (depth <= 1) return false;
    backout(depth-1);
    return false;
  }

  setup_call(depth);
  if (!is_direct(AR(self))) crash("impossible: called law with huge arity");
  u64 ar = get_direct(AR(self));

  run_law(self, ar);

  if (ar < depth) handle_oversaturated_application(depth - ar);
  return true;
}

u64 prim_arity(Value *op) {
  if (!is_direct(op)) return 1;
  switch (get_direct(op)) {
    case 0:  return 1; // mk_pin
    case 1:  return 3; // mk_law
    case 2:  return 1; // incr
    case 3:  return 6; // case
    default: return 1;
  }
}

// this assumes there are sufficient stack args to saturate whichever primop
// we run.
void do_prim(Value *op) {
  if (!is_direct(op)) goto exception_case;

  switch (get_direct(op)) {
    case 0: { // mk_pin
      pop();
      force_in_place(0);
      return mk_pin();
    }
    case 1: { // mk_law
      pop();
      force_in_place(0);          // b
      eval_update(1);             // a
      eval_update(2);             // n
      return mk_law();
    }
    case 2: { // incr
      pop();
      eval_update(0);
      return incr();
    }
    case 3: { // case
      pop();
      eval_update(0);
      prim_case();
      eval();
      return;
    }
    default: {
      goto exception_case;
    }
  }
exception_case:
  force_in_place(1); // param
  exit(1);
}

bool unwind(u64 depth) {
 again:
  Value *x = get_deref(0);
  switch (TY(x)) {
    case APP: {
      push_val(HD(x));
      depth++;
      goto again;
    }
    case LAW: {
      return law_step(depth);
    }
    case PIN: {
      Value *item = deref(x->p.item);
      switch (TY(item)) {
        case NAT: {
          u64 arity = prim_arity(item);
          //
          if (depth < arity) {
            // if we are undersaturated, we backout.
            backout(depth);
            return false;
          }
          // run primop
          pop();
          setup_call(depth);
          flip_stack(arity);
          push_val(item);
          do_prim(item);
          //
          if (arity < depth) {
            // oversaturated
            handle_oversaturated_application(depth - arity);
          } else {
            // application was perfectly saturated.
          }
          return true;
        }
        // unwind "through" pins & apps
        // we don't increment `depth` here because we are just setting up
        // for the above APP case, which increments `depth`.
        case APP:
        case PIN: {
          pop(); // pop outer
          push_val(item);
          goto again;
        }
        case LAW: {
          return law_step(depth);
        }
        case IND: {
          crash("unwind: bad deref");
        }
        case MOV:
          crash("MOV escaped GC");
      }
    }
    case NAT: {
      backout(depth);
      return false;
    }
    case IND: {
      crash("unwind: bad deref");
    }
    case MOV:
      crash("MOV escaped GC");
    default:
      crash("unwind: this should never happen");
  }
}

// returns true if we eval-ed
bool eval() {
  Value *x = get_deref(0);
  switch (TY(x)) {
    case APP:
      return unwind(0);
    case PIN:
    case LAW:
    case NAT:
      return false;
    case IND: crash("eval: IND");
    default:  crash("eval: bad tag");
  }
}

void force_whnf() {
  Value *top = pop_deref();
  if (TY(top) == APP) {
    push_val(TL(top));
    push_val(HD(top));
    force_whnf();
    force();
  }
}

void force() {
  Value *top = get_deref(0);
  if (TY(top) == APP) {
    clone();
    eval();
    update(1);
    force_whnf();
  } else {
    pop();
  }
}

////////////////////////////////////////////////////////////////////////////////
//  Runner

len_t direct_byte_width(word_t w) {
  printf("word=%lu, bits=%lu\n", w, u64_bits(w));
  return (u64_bits(w) + 7) / 8;
}

len_t nat_byte_width(Value *bar) {
    if (is_direct(bar)) {
      printf("direct\n");
      return direct_byte_width(get_direct(bar));
    }
    printf("indirect\n");
    int sz           = WID(bar) * 8;
    word_t last_word = ((char*)BUF(bar))[sz-1];
    return ((sz-1) * 8) + direct_byte_width(last_word);
}

len_t barlen(Value *bar) {
  if (!is_direct(bar) && bar->type != NAT)
    crash("barlen: not nat");
  len_t str_len = nat_byte_width(bar);
  printf("str_len=%lu\n", str_len);
  if (str_len == 0) crash("barlen: given zero");
  return str_len - 1;
}

void repl (void) {
    static char buf[128];

    static const char *filename = "sire.seed";
    u64 seedSz;
    u64 *words = load_seed_file(filename, &seedSz);
    seed_load(words);
    force_in_place(0);

  next_input:
    // putv(get(0));
    int i=0;
    memset(buf, 0, 128);

  read_more:

    ssize_t bytes_read = read(0, buf+i, 1);

    if (bytes_read && i < 100 && buf[i] != '\n') { i++; goto read_more; }

    // Create a string from the input.  (TODO use a bar instead).
    buf[i+1] = 0;
    Value *v = start_bignat_alloc(16);
    memcpy(BUF(v), buf, 128);
    push_val(end_bignat_alloc(v)); // state input

    mk_app();                      // (state input)
    force_in_place(0);             // (0 output newstate)
    v = pop();
    Value *output = TL(HD(v));
    v = TL(v);
    push_val(v);                   // newstate

    len_t wid = barlen(deref(output));

    int wrote;
    if (wid) {
      fprintf(stderr, "[%lu]", wid);
      if (wid != (wrote = write(1, BUF(output), wid))) {
        printf("tried=%ld, wrote=%d\n", wid, wrote);
        crash("write() failed");
      }
    }

    if (i==0 && !bytes_read) exit(0);

    goto next_input;
}


int main (int argc, char **argv) {
  int prot   = PROT_READ | PROT_WRITE;
  int flags  = MAP_FIXED | MAP_PRIVATE | MAP_ANON | MAP_NORESERVE;

  if (tospace != mmap((void*) tospace, HEAP_MAP_SZ, prot, flags, -1, 0))
      { perror("tospace: mmap"); exit(1); }

  if (fromspace != mmap((void*) fromspace, HEAP_MAP_SZ, prot, flags, -1, 0))
      { perror("fromspace: mmap"); exit(1); }

  repl();
}
