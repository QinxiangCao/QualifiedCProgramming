#include "fme_ge_gmp/gmp/gmp_def.h"

void gmp_umul_ppmm(unsigned int *w0, unsigned int *w1,
                   unsigned int u, unsigned int v)
/*@ Require has_uint_permission(w0) *
            has_uint_permission(w1) 
    Ensure exists w0_value w1_value,
             w1_value * UINT_MOD + w0_value == u * v &&
             store_uint(w0, w0_value) *
             store_uint(w1, w1_value) */;

void gmp_udiv_qrnnd_preinv(unsigned int *q, unsigned int *r,
                           unsigned int nh, unsigned int nl,
                           unsigned int d, unsigned int di)
/*@
  Require 0 <= nh && nh < d &&
          0 <= nl && nl <= UINT_MAX &&
          UINT_MOD / 2 <= d && d <= UINT_MAX &&
          0 <= di && di <= UINT_MAX &&
          (di + UINT_MOD) * (UINT_MOD * d) <= Z::pow(UINT_MOD, 3) - 1 &&
          Z::pow(UINT_MOD, 3) - 1 <
            (di + UINT_MOD + 1) * (UINT_MOD * d) &&
          has_uint_permission(q) *
          has_uint_permission(r)
  Ensure exists qv rv,
          0 <= qv && qv <= UINT_MAX &&
          0 <= rv && rv < d &&
          nh * UINT_MOD + nl == qv * d + rv &&
          store_uint(q, qv) *
          store_uint(r, rv)
*/
{
  unsigned int qh;
  unsigned int ql;
  unsigned int rr;
  unsigned int mask;
  unsigned int x;

  gmp_umul_ppmm(&ql, &qh, nh, di);
  /*@ 0 <= ql && ql <= UINT_MAX by local */
  /*@ 0 <= qh && qh <= UINT_MAX by local */
  x = ql + nl;
  qh = qh + (nh + 1) + (x < ql);
  ql = x;
  rr = nl - qh * d;
  mask = -(rr > ql);
  qh += mask;
  rr += mask & d;
  if (rr >= d) {
    rr -= d;
    qh++;
  }
  *r = rr;
  *q = qh;
}
