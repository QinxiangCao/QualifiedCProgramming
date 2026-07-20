#include "fme_ge_gmp/gmp/gmp_def.h"

/*@ Extern Coq (optional_q_undef : Z -> Z -> Assertion)
               (optional_q_full : Z -> Z -> list Z -> Assertion) */

unsigned int mpn_lshift(unsigned int *rp, unsigned int *up,
                        int n, unsigned int cnt)
/*@ nonalias
  With l_up
  Require rp != up &&
          n > 0 && n <= INT_MAX &&
          1 <= cnt && cnt < 32 &&
          Zlength(l_up) == n &&
          list_within_bound(UINT_MOD, l_up) &&
          UIntArray::undef_full(rp, n) *
          UIntArray::full(up, n, l_up)
  Ensure exists l_out,
          Zlength(l_out) == n &&
          list_within_bound(UINT_MOD, l_out) &&
          list_to_Z(UINT_MOD, l_out) + __return * Z::pow(UINT_MOD, n) ==
            list_to_Z(UINT_MOD, l_up) * Z::pow(2, cnt) &&
          UIntArray::full(rp, n, l_out) *
          UIntArray::full(up, n, l_up)
*/
/*@ inplace
  With l_up
  Require rp == up &&
          n > 0 && n <= INT_MAX &&
          1 <= cnt && cnt < 32 &&
          Zlength(l_up) == n &&
          list_within_bound(UINT_MOD, l_up) &&
          UIntArray::full(up, n, l_up)
  Ensure exists l_out,
          Zlength(l_out) == n &&
          list_within_bound(UINT_MOD, l_out) &&
          list_to_Z(UINT_MOD, l_out) + __return * Z::pow(UINT_MOD, n) ==
            list_to_Z(UINT_MOD, l_up) * Z::pow(2, cnt) &&
          UIntArray::full(rp, n, l_out)
*/;

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
*/;

void mpn_div_qr_2_preinv(unsigned int *qp, unsigned int *np, int nn,
                         struct gmp_div_inverse *inv)
/*@ bare
  With qp0 np0 nn0 inv0 l_np d_orig
  Require qp0 == qp && np0 == np && nn0 == nn && inv0 == inv &&
          nn >= 2 && nn <= INT_MAX &&
          Zlength(l_np) == nn &&
          list_within_bound(UINT_MOD, l_np) &&
          ((qp == 0 && emp) ||
           (qp != 0 && UIntArray::undef_full(qp, nn - 1))) *
          UIntArray::full(np, nn, l_np) *
          store_div_inverse(inv, 2, d_orig)
  Ensure exists l_q l_rem l_tail qv rv,
          Zlength(l_q) == nn0 - 1 &&
          Zlength(l_rem) == 2 &&
          Zlength(l_tail) == nn0 - 2 &&
          list_within_bound(UINT_MOD, l_q) &&
          list_within_bound(UINT_MOD, l_rem) &&
          list_within_bound(UINT_MOD, l_tail) &&
          list_to_Z(UINT_MOD, l_q) == qv &&
          list_to_Z(UINT_MOD, l_rem) == rv &&
          list_to_Z(UINT_MOD, l_np) == qv * d_orig + rv &&
          0 <= rv && rv < d_orig &&
          ((qp0 == 0 && emp) ||
           (qp0 != 0 && UIntArray::full(qp0, nn0 - 1, l_q))) *
          UIntArray::seg(np0, 0, 2, l_rem) *
          UIntArray::seg(np0, 2, nn0, l_tail) *
          store_div_inverse(inv0, 2, d_orig)
*/;

void mpn_div_qr_2_preinv(unsigned int *qp, unsigned int *np, int nn,
                         struct gmp_div_inverse *inv)
/*@ optional <= bare
  With qp0 np0 nn0 inv0 l_np d_orig
  Require qp0 == qp && np0 == np && nn0 == nn && inv0 == inv &&
          nn >= 2 && nn <= INT_MAX &&
          Zlength(l_np) == nn &&
          list_within_bound(UINT_MOD, l_np) &&
          optional_q_undef(qp, nn - 1) *
          UIntArray::full(np, nn, l_np) *
          store_div_inverse(inv, 2, d_orig)
  Ensure exists l_q l_rem l_tail qv rv,
          Zlength(l_q) == nn0 - 1 &&
          Zlength(l_rem) == 2 &&
          Zlength(l_tail) == nn0 - 2 &&
          list_within_bound(UINT_MOD, l_q) &&
          list_within_bound(UINT_MOD, l_rem) &&
          list_within_bound(UINT_MOD, l_tail) &&
          list_to_Z(UINT_MOD, l_q) == qv &&
          list_to_Z(UINT_MOD, l_rem) == rv &&
          list_to_Z(UINT_MOD, l_np) == qv * d_orig + rv &&
          0 <= rv && rv < d_orig &&
          optional_q_full(qp0, nn0 - 1, l_q) *
          UIntArray::seg(np0, 0, 2, l_rem) *
          UIntArray::seg(np0, 2, nn0, l_tail) *
          store_div_inverse(inv0, 2, d_orig)
*/;

void mpn_div_qr_2_preinv(unsigned int *qp, unsigned int *np, int nn,
                         struct gmp_div_inverse *inv)
/*@ bare */
{
  unsigned int shift;
  int i;
  unsigned int d1;
  unsigned int d0;
  unsigned int di;
  unsigned int r1;
  unsigned int r0;

  /*@ Assert exists shift_orig d1_orig d0_orig di_orig,
          nn >= 2 && nn <= INT_MAX &&
          qp0 == qp && np0 == np && nn0 == nn && inv0 == inv &&
          0 <= shift_orig && shift_orig < 32 &&
          0 < d_orig &&
          (d1_orig * UINT_MOD + d0_orig) == d_orig * Z::pow(2, shift_orig) &&
          UINT_MOD / 2 <= d1_orig && d1_orig <= UINT_MAX &&
          0 <= d0_orig && d0_orig <= UINT_MAX &&
          0 <= di_orig && di_orig <= UINT_MAX &&
          (di_orig + UINT_MOD) * (UINT_MOD * d1_orig + d0_orig) <=
            Z::pow(UINT_MOD, 3) - 1 &&
          Z::pow(UINT_MOD, 3) - 1 <
            (di_orig + UINT_MOD + 1) * (UINT_MOD * d1_orig + d0_orig) &&
          Zlength(l_np) == nn &&
          list_within_bound(UINT_MOD, l_np) &&
          ((qp == 0 && emp) ||
           (qp != 0 && UIntArray::undef_full(qp, nn - 1))) *
          UIntArray::full(np, nn, l_np) *
          store(&(inv->shift), shift_orig) *
          store(&(inv->d1), d1_orig) *
          store(&(inv->d0), d0_orig) *
          store(&(inv->di), di_orig) *
          has_uint_permission(&shift) *
          undef_data_at(&i, int) *
          has_uint_permission(&d1) *
          has_uint_permission(&d0) *
          has_uint_permission(&di) *
          has_uint_permission(&r1) *
          has_uint_permission(&r0)
  */
  shift = inv->shift;
  d1 = inv->d1;
  d0 = inv->d0;
  di = inv->di;

  if (shift > 0)
    r1 = mpn_lshift(np, np, nn, shift)
         /*@ where (inplace) l_up = l_np */;
  else
    r1 = 0;

  r0 = np[nn - 1];

  i = nn - 2;
  /*@ Inv Assert exists shift_orig d1_orig d0_orig di_orig l_cur l_done qv_done remv carry,
          shift == shift_orig &&
          d1 == d1_orig &&
          d0 == d0_orig &&
          di == di_orig &&
          0 < d_orig &&
          (d1 * UINT_MOD + d0) == d_orig * Z::pow(2, shift) &&
          UINT_MOD / 2 <= d1 && d1 <= UINT_MAX &&
          0 <= d0 && d0 <= UINT_MAX &&
          0 <= di && di <= UINT_MAX &&
          (di + UINT_MOD) * (UINT_MOD * d1 + d0) <=
            Z::pow(UINT_MOD, 3) - 1 &&
          Z::pow(UINT_MOD, 3) - 1 <
            (di + UINT_MOD + 1) * (UINT_MOD * d1 + d0) &&
          0 <= shift && shift < 32 &&
          nn >= 2 && nn <= INT_MAX &&
          qp0 == qp && np0 == np && nn0 == nn && inv0 == inv &&
          -1 <= i && i <= nn - 2 &&
          Zlength(l_cur) == nn &&
          Zlength(l_done) == nn - 2 - i &&
          list_within_bound(UINT_MOD, l_cur) &&
          list_within_bound(UINT_MOD, l_done) &&
          list_to_Z(UINT_MOD, l_done) == qv_done &&
          r1 * UINT_MOD + r0 == remv &&
          0 <= carry && carry <= UINT_MAX &&
          0 <= r1 && r1 <= UINT_MAX &&
          0 <= r0 && r0 <= UINT_MAX &&
          0 <= remv && remv < d1 * UINT_MOD + d0 &&
          carry * Z::pow(UINT_MOD, nn - (i + 1)) +
            list_to_Z(UINT_MOD, sublist(i + 1, nn, l_cur)) ==
            qv_done * (d1 * UINT_MOD + d0) + remv &&
          ((shift == 0 && carry == 0 && l_cur == l_np) ||
           (shift > 0 &&
            list_to_Z(UINT_MOD, l_cur) + carry * Z::pow(UINT_MOD, nn) ==
              list_to_Z(UINT_MOD, l_np) * Z::pow(2, shift))) &&
          UIntArray::full(np, nn, l_cur) *
          ((qp == 0 && emp) ||
           (qp != 0 &&
            UIntArray::undef_seg(qp, 0, i + 1) *
            UIntArray::seg(qp, i + 1, nn - 1, l_done))) *
          store(&(inv->shift), shift) *
          store(&(inv->d1), d1) *
          store(&(inv->d0), d0) *
          store(&(inv->di), di)
  */
  while (i >= 0)
    {
      unsigned int n0;
      unsigned int q;

      n0 = np[i];
      gmp_udiv_qr_3by2(&q, &r1, &r0, r1, r0, n0, d1, d0, di);

      if (qp)
        qp[i] = q;
      i = i - 1;
    }

  if (shift > 0)
    {
      r0 = (r0 >> shift) | (r1 << (32 - shift));
      r1 = r1 >> shift;
    }

  np[1] = r1;
  np[0] = r0;
}
