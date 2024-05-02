#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <limits.h>
#include <stdio.h>
#include "bsdnt.h"

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

static inline
void nn_divrem_preinv_c(nn_t q, nn_t a, len_t m, nn_src_t d,
                               len_t n, preinv2_t dinv, word_t ci) {
   if (n <= DIVREM_CLASSICAL_CUTOFF || m == n)
      nn_divrem_classical_preinv_c(q, a, m, d, n, dinv, ci);
   else
      nn_divrem_divconquer_preinv_c(q, a, m, d, n, dinv, ci);
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