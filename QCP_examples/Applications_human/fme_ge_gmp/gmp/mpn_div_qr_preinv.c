#include "fme_ge_gmp/gmp/gmp_def.h"

/*@ Extern Coq (optional_q_undef : Z -> Z -> Assertion)
               (optional_q_full : Z -> Z -> list Z -> Assertion) */

unsigned int mpn_div_qr_1_preinv(unsigned int *qp, unsigned int *np,
                                 int nn, struct gmp_div_inverse *inv)
/*@
  With qp0 np0 nn0 inv0 l_np d_orig
  Require qp0 == qp && np0 == np && nn0 == nn && inv0 == inv &&
          nn > 0 && nn <= INT_MAX &&
          Zlength(l_np) == nn &&
          list_within_bound(UINT_MOD, l_np) &&
          optional_q_undef(qp, nn) *
          UIntArray::full(np, nn, l_np) *
          store_div_inverse(inv, 1, d_orig)
  Ensure exists l_q qv,
          Zlength(l_q) == nn0 &&
          list_within_bound(UINT_MOD, l_q) &&
          list_to_Z(UINT_MOD, l_q) == qv &&
          list_to_Z(UINT_MOD, l_np) == qv * d_orig + __return &&
          0 <= __return && __return < d_orig &&
          optional_q_full(qp0, nn0, l_q) *
          UIntArray::full(np0, nn0, l_np) *
          store_div_inverse(inv0, 1, d_orig)
*/;

void mpn_div_qr_2_preinv(unsigned int *qp, unsigned int *np, int nn,
                         struct gmp_div_inverse *inv)
/*@
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

unsigned int mpn_lshift(unsigned int *rp, unsigned int *up,
                        int n, unsigned int cnt)
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

unsigned int mpn_rshift(unsigned int *rp, unsigned int *up,
                        int n, unsigned int cnt)
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
          __return == unsigned_last_nbits(Znth(0, l_up, 0) * Z::pow(2, 32 - cnt), 32) &&
          list_to_Z(UINT_MOD, l_up) ==
            list_to_Z(UINT_MOD, l_out) * Z::pow(2, cnt) +
            __return / Z::pow(2, 32 - cnt) &&
          UIntArray::full(rp, n, l_out)
*/;

void mpn_div_qr_pi1(unsigned int *qp,
                    unsigned int *np, int nn, unsigned int n1,
                    unsigned int *dp, int dn,
                    unsigned int dinv)
/*@
  With qp0 np0 dp0 nn0 dn0 n1_orig l_np l_dp dval
  Require qp0 == qp && np0 == np && dp0 == dp &&
          nn0 == nn && dn0 == dn && n1_orig == n1 &&
          dn > 2 && dn <= nn && nn <= INT_MAX &&
          Zlength(l_np) == nn &&
          Zlength(l_dp) == dn &&
          list_within_bound(UINT_MOD, l_np) &&
          list_within_bound(UINT_MOD, l_dp) &&
          list_to_Z(UINT_MOD, l_dp) == dval &&
          0 < dval &&
          0 <= n1 && n1 <= UINT_MAX &&
          UINT_MOD / 2 <= Znth(dn - 1, l_dp, 0) &&
          Znth(dn - 1, l_dp, 0) <= UINT_MAX &&
          0 <= Znth(dn - 2, l_dp, 0) &&
          Znth(dn - 2, l_dp, 0) <= UINT_MAX &&
          0 <= dinv && dinv <= UINT_MAX &&
          (dinv + UINT_MOD) *
            (UINT_MOD * Znth(dn - 1, l_dp, 0) + Znth(dn - 2, l_dp, 0)) <=
            Z::pow(UINT_MOD, 3) - 1 &&
          Z::pow(UINT_MOD, 3) - 1 <
            (dinv + UINT_MOD + 1) *
            (UINT_MOD * Znth(dn - 1, l_dp, 0) + Znth(dn - 2, l_dp, 0)) &&
          n1 * Z::pow(UINT_MOD, nn) + list_to_Z(UINT_MOD, l_np) <
            dval * Z::pow(UINT_MOD, nn - dn + 1) &&
          optional_q_undef(qp, nn - dn + 1) *
          UIntArray::full(np, nn, l_np) *
          UIntArray::full(dp, dn, l_dp)
  Ensure exists l_q l_rem l_tail qv rv,
          Zlength(l_q) == nn0 - dn0 + 1 &&
          Zlength(l_rem) == dn0 &&
          Zlength(l_tail) == nn0 - dn0 &&
          list_within_bound(UINT_MOD, l_q) &&
          list_within_bound(UINT_MOD, l_rem) &&
          list_within_bound(UINT_MOD, l_tail) &&
          list_to_Z(UINT_MOD, l_q) == qv &&
          list_to_Z(UINT_MOD, l_rem) == rv &&
          n1_orig * Z::pow(UINT_MOD, nn0) + list_to_Z(UINT_MOD, l_np) ==
            qv * dval + rv &&
          0 <= rv && rv < dval &&
          optional_q_full(qp0, nn0 - dn0 + 1, l_q) *
          UIntArray::seg(np0, 0, dn0, l_rem) *
          UIntArray::seg(np0, dn0, nn0, l_tail) *
          UIntArray::full(dp0, dn0, l_dp)
*/;

void mpn_div_qr_preinv(unsigned int *qp, unsigned int *np, int nn,
                       unsigned int *dp, int dn,
                       struct gmp_div_inverse *inv)
/*@
  With qp0 np0 dp0 inv0 nn0 dn0 l_np d_orig
  Require qp0 == qp && np0 == np && dp0 == dp && inv0 == inv &&
          nn0 == nn && dn0 == dn &&
          dn > 0 && dn <= nn && nn <= INT_MAX &&
          Zlength(l_np) == nn &&
          list_within_bound(UINT_MOD, l_np) &&
          optional_q_undef(qp, nn - dn + 1) *
          UIntArray::full(np, nn, l_np) *
          store_preinv_divisor(dp, inv, dn, d_orig)
  Ensure exists l_q l_rem l_tail qv rv,
          Zlength(l_q) == nn0 - dn0 + 1 &&
          Zlength(l_rem) == dn0 &&
          Zlength(l_tail) == nn0 - dn0 &&
          list_within_bound(UINT_MOD, l_q) &&
          list_within_bound(UINT_MOD, l_rem) &&
          list_within_bound(UINT_MOD, l_tail) &&
          list_to_Z(UINT_MOD, l_q) == qv &&
          list_to_Z(UINT_MOD, l_rem) == rv &&
          list_to_Z(UINT_MOD, l_np) == qv * d_orig + rv &&
          0 <= rv && rv < d_orig &&
          optional_q_full(qp0, nn0 - dn0 + 1, l_q) *
          UIntArray::seg(np0, 0, dn0, l_rem) *
          UIntArray::seg(np0, dn0, nn0, l_tail) *
          store_preinv_divisor(dp0, inv0, dn0, d_orig)
*/
{
  if (dn == 1)
    {
      /*@ Assert
        qp0 == qp && np0 == np && dp0 == dp && inv0 == inv &&
        nn0 == nn && dn0 == dn &&
        dn == 1 &&
        dn > 0 && dn <= nn && nn <= INT_MAX &&
        Zlength(l_np) == nn &&
        list_within_bound(UINT_MOD, l_np) &&
        optional_q_undef(qp, nn) *
        UIntArray::full(np, nn, l_np) *
        store_div_inverse(inv, 1, d_orig) *
        mpd_store_Z_compact(UINT_MOD, dp, d_orig, 1)
      */
      np[0] = mpn_div_qr_1_preinv(qp, np, nn, inv)
              /*@ where qp0 = qp, np0 = np, nn0 = nn, inv0 = inv,
                         l_np = l_np, d_orig = d_orig */;
      /*@ Assert exists l_q l_rem l_tail qv rv,
        qp0 == qp && np0 == np && dp0 == dp && inv0 == inv &&
        nn0 == nn && dn0 == dn &&
        dn == 1 &&
        Zlength(l_q) == nn - dn + 1 &&
        Zlength(l_rem) == dn &&
        Zlength(l_tail) == nn - dn &&
        list_within_bound(UINT_MOD, l_q) &&
        list_within_bound(UINT_MOD, l_rem) &&
        list_within_bound(UINT_MOD, l_tail) &&
        list_to_Z(UINT_MOD, l_q) == qv &&
        list_to_Z(UINT_MOD, l_rem) == rv &&
        list_to_Z(UINT_MOD, l_np) == qv * d_orig + rv &&
        0 <= rv && rv < d_orig &&
        optional_q_full(qp, nn - dn + 1, l_q) *
        UIntArray::seg(np, 0, dn, l_rem) *
        UIntArray::seg(np, dn, nn, l_tail) *
        store_preinv_divisor(dp, inv, dn, d_orig)
      */
    }
  else if (dn == 2)
    {
      /*@ Assert
        qp0 == qp && np0 == np && dp0 == dp && inv0 == inv &&
        nn0 == nn && dn0 == dn &&
        dn == 2 &&
        dn > 0 && dn <= nn && nn <= INT_MAX &&
        Zlength(l_np) == nn &&
        list_within_bound(UINT_MOD, l_np) &&
        optional_q_undef(qp, nn - 1) *
        UIntArray::full(np, nn, l_np) *
        store_div_inverse(inv, 2, d_orig) *
        mpd_store_Z_compact(UINT_MOD, dp, d_orig, 2)
      */
      mpn_div_qr_2_preinv(qp, np, nn, inv)
      /*@ where qp0 = qp, np0 = np, nn0 = nn, inv0 = inv,
                 l_np = l_np, d_orig = d_orig */;
      /*@ Assert exists l_q l_rem l_tail qv rv,
        qp0 == qp && np0 == np && dp0 == dp && inv0 == inv &&
        nn0 == nn && dn0 == dn &&
        dn == 2 &&
        Zlength(l_q) == nn - dn + 1 &&
        Zlength(l_rem) == dn &&
        Zlength(l_tail) == nn - dn &&
        list_within_bound(UINT_MOD, l_q) &&
        list_within_bound(UINT_MOD, l_rem) &&
        list_within_bound(UINT_MOD, l_tail) &&
        list_to_Z(UINT_MOD, l_q) == qv &&
        list_to_Z(UINT_MOD, l_rem) == rv &&
        list_to_Z(UINT_MOD, l_np) == qv * d_orig + rv &&
        0 <= rv && rv < d_orig &&
        optional_q_full(qp, nn - dn + 1, l_q) *
        UIntArray::seg(np, 0, dn, l_rem) *
        UIntArray::seg(np, dn, nn, l_tail) *
        store_preinv_divisor(dp, inv, dn, d_orig)
      */
    }
  else
    {
      unsigned int nh;
      unsigned int shift;
      unsigned int cy;

      /*@ Assert exists l_dp shift_orig d1_orig d0_orig di_orig,
        qp0 == qp && np0 == np && dp0 == dp && inv0 == inv &&
        nn0 == nn && dn0 == dn &&
        dn > 2 &&
        dn <= nn && nn <= INT_MAX &&
        0 < d_orig &&
        0 <= shift_orig && shift_orig < 32 &&
        Zlength(l_np) == nn &&
        Zlength(l_dp) == dn &&
        list_within_bound(UINT_MOD, l_np) &&
        list_within_bound(UINT_MOD, l_dp) &&
        list_to_Z(UINT_MOD, l_dp) == d_orig * Z::pow(2, shift_orig) &&
        d1_orig == Znth(dn - 1, l_dp, 0) &&
        d0_orig == Znth(dn - 2, l_dp, 0) &&
        UINT_MOD / 2 <= d1_orig && d1_orig <= UINT_MAX &&
        0 <= d0_orig && d0_orig <= UINT_MAX &&
        0 <= di_orig && di_orig <= UINT_MAX &&
        (di_orig + UINT_MOD) *
          (UINT_MOD * d1_orig + d0_orig) <= Z::pow(UINT_MOD, 3) - 1 &&
        Z::pow(UINT_MOD, 3) - 1 <
          (di_orig + UINT_MOD + 1) * (UINT_MOD * d1_orig + d0_orig) &&
        optional_q_undef(qp, nn - dn + 1) *
        UIntArray::full(np, nn, l_np) *
        UIntArray::full(dp, dn, l_dp) *
        store(&(inv->shift), shift_orig) *
        store(&(inv->d1), d1_orig) *
        store(&(inv->d0), d0_orig) *
        store(&(inv->di), di_orig) *
        has_uint_permission(&nh) *
        has_uint_permission(&shift) *
        has_uint_permission(&cy)
      */
      shift = inv->shift;
      if (shift > 0)
        nh = mpn_lshift(np, np, nn, shift)
             /*@ where (inplace) l_up = l_np */;
      else
        nh = 0;

      mpn_div_qr_pi1(qp, np, nn, nh, dp, dn, inv->di);

      if (shift > 0)
        {
          /*@ Assert exists l_dp l_norm l_q l_rem l_tail qv rv nh_orig d1_orig d0_orig di_orig,
            qp0 == qp && np0 == np && dp0 == dp && inv0 == inv &&
            nn0 == nn && dn0 == dn &&
            dn > 2 &&
            dn <= nn && nn <= INT_MAX &&
            0 < d_orig &&
            1 <= shift && shift < 32 &&
            nh == nh_orig &&
            d1_orig == Znth(dn - 1, l_dp, 0) &&
            d0_orig == Znth(dn - 2, l_dp, 0) &&
            UINT_MOD / 2 <= d1_orig && d1_orig <= UINT_MAX &&
            0 <= d0_orig && d0_orig <= UINT_MAX &&
            0 <= di_orig && di_orig <= UINT_MAX &&
            (di_orig + UINT_MOD) *
              (UINT_MOD * d1_orig + d0_orig) <= Z::pow(UINT_MOD, 3) - 1 &&
            Z::pow(UINT_MOD, 3) - 1 <
              (di_orig + UINT_MOD + 1) * (UINT_MOD * d1_orig + d0_orig) &&
            Zlength(l_np) == nn &&
            Zlength(l_norm) == nn &&
            Zlength(l_dp) == dn &&
            Zlength(l_q) == nn - dn + 1 &&
            Zlength(l_rem) == dn &&
            Zlength(l_tail) == nn - dn &&
            list_within_bound(UINT_MOD, l_np) &&
            list_within_bound(UINT_MOD, l_norm) &&
            list_within_bound(UINT_MOD, l_dp) &&
            list_within_bound(UINT_MOD, l_q) &&
            list_within_bound(UINT_MOD, l_rem) &&
            list_within_bound(UINT_MOD, l_tail) &&
            list_to_Z(UINT_MOD, l_dp) == d_orig * Z::pow(2, shift) &&
            list_to_Z(UINT_MOD, l_norm) + nh_orig * Z::pow(UINT_MOD, nn) ==
              list_to_Z(UINT_MOD, l_np) * Z::pow(2, shift) &&
            list_to_Z(UINT_MOD, l_q) == qv &&
            list_to_Z(UINT_MOD, l_rem) == rv &&
            nh_orig * Z::pow(UINT_MOD, nn) + list_to_Z(UINT_MOD, l_norm) ==
              qv * list_to_Z(UINT_MOD, l_dp) + rv &&
            0 <= rv && rv < list_to_Z(UINT_MOD, l_dp) &&
            optional_q_full(qp, nn - dn + 1, l_q) *
            UIntArray::full(np, dn, l_rem) *
            UIntArray::seg(np, dn, nn, l_tail) *
            UIntArray::full(dp, dn, l_dp) *
            store(&(inv->shift), shift) *
            store(&(inv->d1), d1_orig) *
            store(&(inv->d0), d0_orig) *
            store(&(inv->di), di_orig) *
            has_uint_permission(&cy)
          */
          /*@ Given l_rem */
          cy = mpn_rshift(np, np, dn, shift)
                 /*@ where (inplace) l_up = l_rem */;
          /*@ cy == 0 by local */
	}
    }
}
