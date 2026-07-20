#include "fme_ge_gmp/gmp/gmp_def.h"

void gmp_umul_ppmm(unsigned int *w0, unsigned int *w1,
                   unsigned int u, unsigned int v)
/*@ Require has_uint_permission(w0) *
            has_uint_permission(w1) 
    Ensure exists w0_value w1_value,
             w1_value * UINT_MOD + w0_value == u * v &&
             store_uint(w0, w0_value) *
             store_uint(w1, w1_value) */;

void gmp_udiv_qr_3by2(unsigned int *q, unsigned int *r1, unsigned int *r0,
                      unsigned int n2, unsigned int n1, unsigned int n0,
                      unsigned int d1, unsigned int d0, unsigned int dinv)
/*@
  Require 0 <= n2 && n2 <= UINT_MAX &&
          0 <= n1 && n1 <= UINT_MAX &&
          0 <= n0 && n0 <= UINT_MAX &&
          n2 * UINT_MOD + n1 < d1 * UINT_MOD + d0 &&
          UINT_MOD / 2 <= d1 && d1 <= UINT_MAX &&
          0 <= d0 && d0 <= UINT_MAX &&
          0 <= dinv && dinv <= UINT_MAX &&
          (dinv + UINT_MOD) * (UINT_MOD * d1 + d0) <=
            Z::pow(UINT_MOD, 3) - 1 &&
          Z::pow(UINT_MOD, 3) - 1 <
            (dinv + UINT_MOD + 1) * (UINT_MOD * d1 + d0) &&
          has_uint_permission(q) *
          has_uint_permission(r1) *
          has_uint_permission(r0)
  Ensure exists qv rv1 rv0,
          0 <= qv && qv <= UINT_MAX &&
          0 <= rv1 && rv1 <= UINT_MAX &&
          0 <= rv0 && rv0 <= UINT_MAX &&
          rv1 * UINT_MOD + rv0 < d1 * UINT_MOD + d0 &&
          n2 * Z::pow(UINT_MOD, 2) + n1 * UINT_MOD + n0 ==
            qv * (d1 * UINT_MOD + d0) + rv1 * UINT_MOD + rv0 &&
          store_uint(q, qv) *
          store_uint(r1, rv1) *
          store_uint(r0, rv0)
*/
{
  unsigned int qv;
  unsigned int q0;
  unsigned int t1;
  unsigned int t0;
  unsigned int mask;
  unsigned int x;
  unsigned int rv1;
  unsigned int rv0;

  gmp_umul_ppmm(&q0, &qv, n2, dinv);
  /*@ 0 <= q0 && q0 <= UINT_MAX by local */
  /*@ 0 <= qv && qv <= UINT_MAX by local */
  x = q0 + n1;
  qv = qv + n2 + (x < q0);
  q0 = x;

  rv1 = n1 - d1 * qv;
  x = n0 - d0;
  rv1 = rv1 - d1 - (n0 < d0);
  rv0 = x;

  gmp_umul_ppmm(&t0, &t1, d0, qv);
  /*@ 0 <= t0 && t0 <= UINT_MAX by local */
  /*@ 0 <= t1 && t1 <= UINT_MAX by local */
  x = rv0 - t0;
  rv1 = rv1 - t1 - (rv0 < t0);
  rv0 = x;

  /*@ Assert exists qhat qext rpre1 rpre0 qlo,
        qv == qhat &&
        qext == qhat + 1 &&
        rv1 == rpre1 &&
        rv0 == rpre0 &&
        q0 == qlo &&
        q == q@pre &&
        r1 == r1@pre &&
        r0 == r0@pre &&
        n2 == n2@pre &&
        n1 == n1@pre &&
        n0 == n0@pre &&
        d1 == d1@pre &&
        d0 == d0@pre &&
        dinv == dinv@pre &&
        0 <= n2@pre && n2@pre <= UINT_MAX &&
        n2@pre * UINT_MOD + n1@pre < d1@pre * UINT_MOD + d0@pre &&
        0 <= n1@pre && n1@pre <= UINT_MAX &&
        0 <= n0@pre && n0@pre <= UINT_MAX &&
        UINT_MOD / 2 <= d1@pre && d1@pre <= UINT_MAX &&
        0 <= d0@pre && d0@pre <= UINT_MAX &&
        0 <= dinv@pre && dinv@pre <= UINT_MAX &&
        0 <= qhat && qhat <= UINT_MAX &&
        1 <= qext && qext <= UINT_MOD &&
        0 <= rpre1 && rpre1 <= UINT_MAX &&
        0 <= rpre0 && rpre0 <= UINT_MAX &&
        0 <= qlo && qlo <= UINT_MAX &&
        ((rpre1 < qlo &&
          n2@pre * Z::pow(UINT_MOD, 2) + n1@pre * UINT_MOD + n0@pre ==
            qext * (d1@pre * UINT_MOD + d0@pre) + rpre1 * UINT_MOD + rpre0) ||
         (rpre1 >= qlo &&
          ((rpre1 * UINT_MOD + rpre0 +
              (d1@pre * UINT_MOD + d0@pre) < Z::pow(UINT_MOD, 2) &&
            n2@pre * Z::pow(UINT_MOD, 2) + n1@pre * UINT_MOD + n0@pre ==
              qext * (d1@pre * UINT_MOD + d0@pre) + rpre1 * UINT_MOD + rpre0) ||
           (rpre1 * UINT_MOD + rpre0 +
              (d1@pre * UINT_MOD + d0@pre) >= Z::pow(UINT_MOD, 2) &&
            n2@pre * Z::pow(UINT_MOD, 2) + n1@pre * UINT_MOD + n0@pre + Z::pow(UINT_MOD, 2) ==
              qext * (d1@pre * UINT_MOD + d0@pre) + rpre1 * UINT_MOD + rpre0)))) &&
        has_uint_permission(q) *
        has_uint_permission(r1) *
        has_uint_permission(r0) *
        has_uint_permission(&t1) *
        has_uint_permission(&t0) *
        has_uint_permission(&mask) *
        has_uint_permission(&x)
  */
  qv++;

  /*@ Assert exists qpre qext rpre1 rpre0 qlo,
        qv == qpre &&
        ((0 < qpre && qext == qpre) ||
         (qpre == 0 && qext == UINT_MOD)) &&
	        rv1 == rpre1 &&
	        rv0 == rpre0 &&
	        q0 == qlo &&
	        q == q@pre &&
	        r1 == r1@pre &&
	        r0 == r0@pre &&
	        n2 == n2@pre &&
        n1 == n1@pre &&
        n0 == n0@pre &&
        d1 == d1@pre &&
	        d0 == d0@pre &&
	        dinv == dinv@pre &&
	        0 <= n2@pre && n2@pre <= UINT_MAX &&
        n2@pre * UINT_MOD + n1@pre < d1@pre * UINT_MOD + d0@pre &&
	        0 <= n1@pre && n1@pre <= UINT_MAX &&
	        0 <= n0@pre && n0@pre <= UINT_MAX &&
	        UINT_MOD / 2 <= d1@pre && d1@pre <= UINT_MAX &&
	        0 <= d0@pre && d0@pre <= UINT_MAX &&
	        0 <= dinv@pre && dinv@pre <= UINT_MAX &&
	        0 <= qpre && qpre <= UINT_MAX &&
        1 <= qext && qext <= UINT_MOD &&
	        0 <= rpre1 && rpre1 <= UINT_MAX &&
	        0 <= rpre0 && rpre0 <= UINT_MAX &&
        0 <= qlo && qlo <= UINT_MAX &&
        ((rpre1 < qlo &&
          n2@pre * Z::pow(UINT_MOD, 2) + n1@pre * UINT_MOD + n0@pre ==
            qext * (d1@pre * UINT_MOD + d0@pre) + rpre1 * UINT_MOD + rpre0) ||
         (rpre1 >= qlo &&
          ((rpre1 * UINT_MOD + rpre0 +
              (d1@pre * UINT_MOD + d0@pre) < Z::pow(UINT_MOD, 2) &&
            n2@pre * Z::pow(UINT_MOD, 2) + n1@pre * UINT_MOD + n0@pre ==
              qext * (d1@pre * UINT_MOD + d0@pre) + rpre1 * UINT_MOD + rpre0) ||
           (rpre1 * UINT_MOD + rpre0 +
              (d1@pre * UINT_MOD + d0@pre) >= Z::pow(UINT_MOD, 2) &&
            n2@pre * Z::pow(UINT_MOD, 2) + n1@pre * UINT_MOD + n0@pre + Z::pow(UINT_MOD, 2) ==
              qext * (d1@pre * UINT_MOD + d0@pre) + rpre1 * UINT_MOD + rpre0)))) &&
	        has_uint_permission(q) *
	        has_uint_permission(r1) *
	        has_uint_permission(r0) *
	        has_uint_permission(&t1) *
	        has_uint_permission(&t0) *
	        has_uint_permission(&mask) *
	        has_uint_permission(&x)
  */

  mask = -(rv1 >= q0);
  /*@ Assert exists qpre qext rpre1 rpre0 qlo m,
        qv == qpre &&
        ((0 < qpre && qext == qpre) ||
         (qpre == 0 && qext == UINT_MOD)) &&
        rv1 == rpre1 &&
	        rv0 == rpre0 &&
	        q0 == qlo &&
	        mask == m &&
	        q == q@pre &&
	        r1 == r1@pre &&
	        r0 == r0@pre &&
	        n2 == n2@pre &&
        n1 == n1@pre &&
        n0 == n0@pre &&
        d1 == d1@pre &&
	        d0 == d0@pre &&
	        dinv == dinv@pre &&
	        0 <= n2@pre && n2@pre <= UINT_MAX &&
        n2@pre * UINT_MOD + n1@pre < d1@pre * UINT_MOD + d0@pre &&
	        0 <= n1@pre && n1@pre <= UINT_MAX &&
	        0 <= n0@pre && n0@pre <= UINT_MAX &&
	        UINT_MOD / 2 <= d1@pre && d1@pre <= UINT_MAX &&
	        0 <= d0@pre && d0@pre <= UINT_MAX &&
	        0 <= dinv@pre && dinv@pre <= UINT_MAX &&
	        0 <= qpre && qpre <= UINT_MAX &&
        1 <= qext && qext <= UINT_MOD &&
	        0 <= rpre1 && rpre1 <= UINT_MAX &&
	        0 <= rpre0 && rpre0 <= UINT_MAX &&
        0 <= qlo && qlo <= UINT_MAX &&
        ((m == 0 &&
          n2@pre * Z::pow(UINT_MOD, 2) + n1@pre * UINT_MOD + n0@pre ==
            qext * (d1@pre * UINT_MOD + d0@pre) + rpre1 * UINT_MOD + rpre0) ||
         (m == UINT_MAX &&
          ((rpre1 * UINT_MOD + rpre0 +
              (d1@pre * UINT_MOD + d0@pre) < Z::pow(UINT_MOD, 2) &&
            n2@pre * Z::pow(UINT_MOD, 2) + n1@pre * UINT_MOD + n0@pre ==
              qext * (d1@pre * UINT_MOD + d0@pre) + rpre1 * UINT_MOD + rpre0) ||
           (rpre1 * UINT_MOD + rpre0 +
              (d1@pre * UINT_MOD + d0@pre) >= Z::pow(UINT_MOD, 2) &&
            n2@pre * Z::pow(UINT_MOD, 2) + n1@pre * UINT_MOD + n0@pre + Z::pow(UINT_MOD, 2) ==
              qext * (d1@pre * UINT_MOD + d0@pre) + rpre1 * UINT_MOD + rpre0)))) &&
	        has_uint_permission(q) *
	        has_uint_permission(r1) *
	        has_uint_permission(r0) *
	        has_uint_permission(&t1) *
	        has_uint_permission(&t0) *
	        has_uint_permission(&x)
  */
  qv += mask;
  x = rv0 + (mask & d0);
  rv1 = rv1 + (mask & d1) + (x < rv0);
  rv0 = x;

  /*@ Assert exists qmid rmid1 rmid0,
	        qv == qmid &&
	        rv1 == rmid1 &&
	        rv0 == rmid0 &&
	        q == q@pre &&
	        r1 == r1@pre &&
	        r0 == r0@pre &&
	        n2 == n2@pre &&
        n1 == n1@pre &&
        n0 == n0@pre &&
        d1 == d1@pre &&
	        d0 == d0@pre &&
	        dinv == dinv@pre &&
	        0 <= n2@pre && n2@pre <= UINT_MAX &&
        n2@pre * UINT_MOD + n1@pre < d1@pre * UINT_MOD + d0@pre &&
	        0 <= n1@pre && n1@pre <= UINT_MAX &&
	        0 <= n0@pre && n0@pre <= UINT_MAX &&
	        UINT_MOD / 2 <= d1@pre && d1@pre <= UINT_MAX &&
	        0 <= d0@pre && d0@pre <= UINT_MAX &&
	        0 <= dinv@pre && dinv@pre <= UINT_MAX &&
	        0 <= qmid && qmid <= UINT_MAX &&
	        0 <= rmid1 && rmid1 <= UINT_MAX &&
	        0 <= rmid0 && rmid0 <= UINT_MAX &&
        rmid1 * UINT_MOD + rmid0 < 2 * (d1@pre * UINT_MOD + d0@pre) &&
        n2@pre * Z::pow(UINT_MOD, 2) + n1@pre * UINT_MOD + n0@pre ==
          qmid * (d1@pre * UINT_MOD + d0@pre) + rmid1 * UINT_MOD + rmid0 &&
	        has_uint_permission(q) *
	        has_uint_permission(r1) *
	        has_uint_permission(r0) *
	        has_uint_permission(&q0) *
	        has_uint_permission(&t1) *
	        has_uint_permission(&t0) *
	        has_uint_permission(&mask) *
	        has_uint_permission(&x)
  */

  if (rv1 >= d1) {
    if (rv1 > d1 || rv0 >= d0) {
      qv++;
      x = rv0 - d0;
      rv1 = rv1 - d1 - (rv0 < d0);
      rv0 = x;
    }
  }

  /*@ Assert exists qout rv1out rv0out,
	        qv == qout &&
	        rv1 == rv1out &&
	        rv0 == rv0out &&
	        q == q@pre &&
	        r1 == r1@pre &&
	        r0 == r0@pre &&
	        n2 == n2@pre &&
	        n1 == n1@pre &&
	        n0 == n0@pre &&
	        d1 == d1@pre &&
	        d0 == d0@pre &&
	        dinv == dinv@pre &&
	        0 <= n2@pre && n2@pre <= UINT_MAX &&
        n2@pre * UINT_MOD + n1@pre < d1@pre * UINT_MOD + d0@pre &&
	        0 <= n1@pre && n1@pre <= UINT_MAX &&
	        0 <= n0@pre && n0@pre <= UINT_MAX &&
	        UINT_MOD / 2 <= d1@pre && d1@pre <= UINT_MAX &&
	        0 <= d0@pre && d0@pre <= UINT_MAX &&
	        0 <= dinv@pre && dinv@pre <= UINT_MAX &&
	        0 <= qout && qout <= UINT_MAX &&
        0 <= rv1out && rv1out <= UINT_MAX &&
        0 <= rv0out && rv0out <= UINT_MAX &&
        rv1out * UINT_MOD + rv0out < d1@pre * UINT_MOD + d0@pre &&
        n2@pre * Z::pow(UINT_MOD, 2) + n1@pre * UINT_MOD + n0@pre ==
          qout * (d1@pre * UINT_MOD + d0@pre) + rv1out * UINT_MOD + rv0out &&
	        has_uint_permission(q) *
	        has_uint_permission(r1) *
	        has_uint_permission(r0) *
	        has_uint_permission(&q0) *
	        has_uint_permission(&t1) *
	        has_uint_permission(&t0) *
	        has_uint_permission(&mask) *
	        has_uint_permission(&x)
  */

  *q = qv;
  *r1 = rv1;
  *r0 = rv0;
}
