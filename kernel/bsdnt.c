#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <limits.h>
#include <stdio.h>
#include "bsdnt.h"

void nn_mul(nn_t p, nn_src_t a, len_t m, nn_src_t b, len_t n);

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

#define nn_mul1(a, b, m, c)    nn_mul1_c(a, b, m, c, (word_t) 0)
#define nn_addmul1(a, b, m, c) nn_addmul1_c(a, b, m, c, (word_t) 0)

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

#define nn_shr(a, b, m, bits) nn_shr_c(a, b, m, bits, (word_t) 0)
#define nn_mul_m(p, a, b, m)  nn_mul_classical(p, a, m, b, m)
#define nn_mul(p, a, m, b, n) nn_mul_classical(p, a, m, b, n)

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

#define nn_mullow_kara nn_mullow_classical

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

#define nn_mulmid_kara nn_mulmid_classical

/*
   As per nn_divapprox_classical_preinv_c.
*/
static inline
word_t nn_divapprox_preinv_c(nn_t q, nn_t a, len_t m,
                          nn_src_t d, len_t n, preinv2_t dinv, word_t ci)
{
   return nn_divapprox_classical_preinv_c(q, a, m, d, n, dinv, ci);
}


static inline
void nn_divrem_preinv_c(nn_t q, nn_t a, len_t m, nn_src_t d,
                               len_t n, preinv2_t dinv, word_t ci) {
    nn_divrem_classical_preinv_c(q, a, m, d, n, dinv, ci);
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
      nn_divrem_classical_preinv_c(q, a, m, t, n, inv, ci);
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
