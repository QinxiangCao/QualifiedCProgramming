#include "fme_ge_gmp/gmp/gmp_def.h"

void gmp_umul_ppmm(unsigned int *w0, unsigned int *w1,
                   unsigned int u, unsigned int v)
/*@ Require has_uint_permission(w0) *
            has_uint_permission(w1) 
    Ensure exists w0_value w1_value,
             w1_value * UINT_MOD + w0_value == u * v &&
             store_uint(w0, w0_value) *
             store_uint(w1, w1_value) */;

unsigned int mpn_invert_3by2(unsigned int u1, unsigned int u0)
/*@
  Require UINT_MOD / 2 <= u1 && u1 <= UINT_MAX &&
          0 <= u0 && u0 <= UINT_MAX
  Ensure 0 <= __return && __return <= UINT_MAX &&
         (__return + UINT_MOD) * (UINT_MOD * u1 + u0) <=
           Z::pow(UINT_MOD, 3) - 1 &&
         Z::pow(UINT_MOD, 3) - 1 <
           (__return + UINT_MOD + 1) * (UINT_MOD * u1 + u0)
*/
{
  unsigned int r, m;

  {
    unsigned int p, ql;
    unsigned int ul, uh, qh;

    ul = u1 & 65535;
    uh = u1 >> 16;
    /*@ uh != 0 by local */
    qh = (u1 ^ 4294967295U) / uh;
    /*@ Assert exists ul0 uh0 qh0,
          u1 == u1@pre &&
          u0 == u0@pre &&
          0 <= u1@pre &&
          u1@pre <= UINT_MAX &&
          0 <= u0@pre &&
          u0@pre <= UINT_MAX &&
          ul == ul0 &&
          uh == uh0 &&
          qh == qh0 &&
          ul0 == (u1@pre & 65535) &&
          uh0 == (u1@pre >> 16) &&
          qh0 == ((u1@pre ^ 4294967295) / uh0) &&
          0 <= ul0 &&
          ul0 < 65536 &&
          1 <= uh0 &&
          uh0 < 65536 &&
          u1@pre == uh0 * 65536 + ul0 &&
          0 <= qh0 &&
          qh0 < 65536 &&
          UINT_MOD / 2 <= u1@pre &&
          has_uint_permission(&r) *
          has_uint_permission(&m) *
          has_uint_permission(&p) *
          has_uint_permission(&ql)
    */

    r = ((~u1 - qh * uh) << 16) | 65535;

    p = qh * ul;
    if (r < p)
      {
        qh--;
        r += u1;
        if (r >= u1)
          {
            if (r < p)
              {
                qh--;
                r += u1;
              }
          }
      }
    r -= p;
    /*@ Assert exists qh0 rhalf,
          u1 == u1@pre &&
          u0 == u0@pre &&
          0 <= u1@pre &&
          u1@pre <= UINT_MAX &&
          0 <= u0@pre &&
          u0@pre <= UINT_MAX &&
          qh == qh0 &&
          r == rhalf &&
          0 <= qh0 &&
          qh0 < 65536 &&
          0 <= rhalf &&
          rhalf < u1@pre &&
          (qh0 + 65536) * u1@pre + rhalf ==
            Z::pow(65536, 3) - 1 &&
          UINT_MOD / 2 <= u1@pre &&
          has_uint_permission(&m) *
          has_uint_permission(&p) *
          has_uint_permission(&ql) *
          has_uint_permission(&ul) *
          has_uint_permission(&uh)
    */

    p = (r >> 16) * qh + r;
    ql = (p >> 16) + 1;
    /*@ Assert exists qh0 rhalf p0 ql0,
          u1 == u1@pre &&
          u0 == u0@pre &&
          0 <= u1@pre &&
          u1@pre <= UINT_MAX &&
          0 <= u0@pre &&
          u0@pre <= UINT_MAX &&
          qh == qh0 &&
          r == rhalf &&
          p == p0 &&
          ql == ql0 &&
          0 <= qh0 &&
          qh0 < 65536 &&
          0 <= rhalf &&
          rhalf < u1@pre &&
          (qh0 + 65536) * u1@pre + rhalf ==
            Z::pow(65536, 3) - 1 &&
          0 <= p0 &&
          p0 <= UINT_MAX &&
          0 <= ql0 &&
          ql0 <= 65536 &&
          p0 == (rhalf >> 16) * qh0 + rhalf &&
          ql0 == (p0 >> 16) + 1 &&
          UINT_MOD / 2 <= u1@pre &&
          has_uint_permission(&m) *
          has_uint_permission(&ul) *
          has_uint_permission(&uh)
    */

    r = (r << 16) + 65535 - ql * u1;

    if (r >= (4294967295U & (p << 16)))
      {
        ql--;
        r += u1;
      }
    /*@ Assert exists qh0 ql0 rpre,
          u1 == u1@pre &&
          u0 == u0@pre &&
          0 <= u1@pre &&
          u1@pre <= UINT_MAX &&
          0 <= u0@pre &&
          u0@pre <= UINT_MAX &&
          qh == qh0 &&
          ql == ql0 &&
          r == rpre &&
          0 <= qh0 &&
          qh0 < 65536 &&
          0 <= ql0 &&
          ql0 <= 65536 &&
          0 <= qh0 * 65536 + ql0 &&
          qh0 * 65536 + ql0 <= UINT_MAX &&
          0 <= rpre &&
          rpre < 2 * u1@pre &&
          (qh0 * 65536 + ql0 + UINT_MOD) * u1@pre + rpre ==
            Z::pow(UINT_MOD, 2) - 1 &&
          UINT_MOD / 2 <= u1@pre &&
          has_uint_permission(&m) *
          has_uint_permission(&p) *
          has_uint_permission(&ul) *
          has_uint_permission(&uh)
    */
    m = (qh << 16) + ql;
    /*@ Assert exists mpre rpre,
          u1 == u1@pre &&
          u0 == u0@pre &&
          0 <= u1@pre &&
          u1@pre <= UINT_MAX &&
          0 <= u0@pre &&
          u0@pre <= UINT_MAX &&
          m == mpre &&
          r == rpre &&
          0 <= mpre &&
          mpre <= UINT_MAX &&
          0 <= rpre &&
          rpre < 2 * u1@pre &&
          (mpre + UINT_MOD) * u1@pre + rpre ==
            Z::pow(UINT_MOD, 2) - 1 &&
          UINT_MOD / 2 <= u1@pre &&
          has_uint_permission(&p) *
          has_uint_permission(&ql) *
          has_uint_permission(&ul) *
          has_uint_permission(&uh) *
          has_uint_permission(&qh)
    */
    if (r >= u1)
      {
        m++;
        r -= u1;
      }
  }
  /*@ Assert exists m0 r0,
        u1 == u1@pre &&
        u0 == u0@pre &&
        0 <= u1@pre &&
        u1@pre <= UINT_MAX &&
        0 <= u0@pre &&
        u0@pre <= UINT_MAX &&
        m == m0 &&
        r == r0 &&
        0 <= m0 &&
        m0 <= UINT_MAX &&
        0 <= r0 &&
        r0 < u1@pre &&
        (m0 + UINT_MOD) * u1@pre + r0 == Z::pow(UINT_MOD, 2) - 1 &&
        UINT_MOD / 2 <= u1@pre
  */

  if (u0 > 0)
    {
      unsigned int th, tl;
      r = ~r;
      r += u0;
      if (r < u0)
        {
          m--;
          if (r >= u1)
            {
              m--;
              r -= u1;
            }
          r -= u1;
        }
      /*@ Assert exists m1 r1,
            u1 == u1@pre &&
            u0 == u0@pre &&
            0 <= u1@pre &&
            u1@pre <= UINT_MAX &&
            0 <= u0@pre &&
            u0@pre <= UINT_MAX &&
            u0@pre > 0 &&
            m == m1 &&
            r == r1 &&
            0 <= m1 &&
            m1 <= UINT_MAX &&
            0 <= r1 &&
            r1 <= UINT_MAX &&
            (m1 + UINT_MOD) * u1@pre + (UINT_MOD - 1 - r1) ==
              Z::pow(UINT_MOD, 2) - 1 - u0@pre &&
            UINT_MOD - 1 - r1 < u1@pre &&
            UINT_MOD / 2 <= u1@pre &&
            has_uint_permission(&th) *
            has_uint_permission(&tl)
      */
      gmp_umul_ppmm(&tl, &th, u0, m);
      /*@ 0 <= tl && tl <= UINT_MAX by local */
      /*@ 0 <= th && th <= UINT_MAX by local */
      /*@ Assert exists m1 r1 tlv thv,
            u1 == u1@pre &&
            u0 == u0@pre &&
            0 <= u1@pre &&
            u1@pre <= UINT_MAX &&
            0 <= u0@pre &&
            u0@pre <= UINT_MAX &&
            u0@pre > 0 &&
            m == m1 &&
            r == r1 &&
            tl == tlv &&
            th == thv &&
            0 <= m1 &&
            m1 <= UINT_MAX &&
            0 <= r1 &&
            r1 <= UINT_MAX &&
            0 <= tlv &&
            tlv <= UINT_MAX &&
            0 <= thv &&
            thv <= UINT_MAX &&
            thv * UINT_MOD + tlv == u0@pre * m1 &&
            (m1 + UINT_MOD) * u1@pre + (UINT_MOD - 1 - r1) ==
              Z::pow(UINT_MOD, 2) - 1 - u0@pre &&
            UINT_MOD - 1 - r1 < u1@pre &&
            UINT_MOD / 2 <= u1@pre
      */
      r += th;
      if (r < th)
        {
          m--;
          m -= ((r > u1) | ((r == u1) & (tl > u0)));
        }
      /*@ Assert exists m2 r2 tlv thv,
            u1 == u1@pre &&
            u0 == u0@pre &&
            0 <= u1@pre &&
            u1@pre <= UINT_MAX &&
            0 <= u0@pre &&
            u0@pre <= UINT_MAX &&
            u0@pre > 0 &&
            m == m2 &&
            r == r2 &&
            tl == tlv &&
            th == thv &&
            0 <= m2 &&
            m2 <= UINT_MAX &&
            0 <= r2 &&
            r2 <= UINT_MAX &&
            0 <= tlv &&
            tlv <= UINT_MAX &&
            0 <= thv &&
            thv <= UINT_MAX &&
            (m2 + UINT_MOD) * (UINT_MOD * u1@pre + u0@pre) <=
              Z::pow(UINT_MOD, 3) - 1 &&
            Z::pow(UINT_MOD, 3) - 1 <
              (m2 + UINT_MOD + 1) * (UINT_MOD * u1@pre + u0@pre) &&
            UINT_MOD / 2 <= u1@pre
      */
    }
  /*@ Assert exists m3 r3,
        u1 == u1@pre &&
        u0 == u0@pre &&
        0 <= u1@pre &&
        u1@pre <= UINT_MAX &&
        0 <= u0@pre &&
        u0@pre <= UINT_MAX &&
        m == m3 &&
        r == r3 &&
        0 <= m3 &&
        m3 <= UINT_MAX &&
        0 <= r3 &&
        r3 <= UINT_MAX &&
        (m3 + UINT_MOD) * (UINT_MOD * u1@pre + u0@pre) <=
          Z::pow(UINT_MOD, 3) - 1 &&
        Z::pow(UINT_MOD, 3) - 1 <
          (m3 + UINT_MOD + 1) * (UINT_MOD * u1@pre + u0@pre) &&
        UINT_MOD / 2 <= u1@pre
  */

  return m;
}
