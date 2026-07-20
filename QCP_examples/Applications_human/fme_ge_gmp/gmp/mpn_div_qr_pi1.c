#include "fme_ge_gmp/gmp/gmp_def.h"

/*@ Extern Coq (optional_q_undef : Z -> Z -> Assertion)
               (optional_q_full : Z -> Z -> list Z -> Assertion) */

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

unsigned int mpn_submul_1(unsigned int *rp, unsigned int *up,
                          int n, unsigned int vl)
/*@
  With l_rp l_up
  Require n > 0 && n <= INT_MAX &&
          0 <= vl && vl <= UINT_MAX &&
          Zlength(l_rp) == n &&
          Zlength(l_up) == n &&
          list_within_bound(UINT_MOD, l_rp) &&
          list_within_bound(UINT_MOD, l_up) &&
          UIntArray::full(rp, n, l_rp) *
          UIntArray::full(up, n, l_up)
  Ensure exists l_out val_out,
          Zlength(l_out) == n &&
          list_within_bound(UINT_MOD, l_out) &&
          list_to_Z(UINT_MOD, l_out) == val_out &&
          val_out - __return * Z::pow(UINT_MOD, n) ==
            list_to_Z(UINT_MOD, l_rp) - list_to_Z(UINT_MOD, l_up) * vl &&
          UIntArray::full(rp, n, l_out) *
          UIntArray::full(up, n, l_up)
*/;

unsigned int
mpn_add_n (unsigned int *rp, unsigned int *ap, unsigned int *bp, int n)
/*@ rp_eq_ap
  With val_a val_b
  Require
    rp == ap && n >= 0 &&
    mpd_store_Z(UINT_MOD, ap, val_a, n) *
    mpd_store_Z(UINT_MOD, bp, val_b, n)
  Ensure exists val_r_out,
    (val_r_out + __return * Z::pow(UINT_MOD, n) == val_a + val_b) &&
    rp == ap &&
    mpd_store_Z(UINT_MOD, rp, val_r_out, n) *
    mpd_store_Z(UINT_MOD, bp, val_b, n)
*/;

void mpn_div_qr_pi1(unsigned int *qp,
                    unsigned int *np, int nn, unsigned int n1,
                    unsigned int *dp, int dn,
                    unsigned int dinv)
/*@ bare
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
          ((qp == 0 && emp) ||
           (qp != 0 && UIntArray::undef_full(qp, nn - dn + 1))) *
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
          ((qp0 == 0 && emp) ||
           (qp0 != 0 && UIntArray::full(qp0, nn0 - dn0 + 1, l_q))) *
          UIntArray::seg(np0, 0, dn0, l_rem) *
          UIntArray::seg(np0, dn0, nn0, l_tail) *
          UIntArray::full(dp0, dn0, l_dp)
*/;

void mpn_div_qr_pi1(unsigned int *qp,
                    unsigned int *np, int nn, unsigned int n1,
                    unsigned int *dp, int dn,
                    unsigned int dinv)
/*@ optional <= bare
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

void mpn_div_qr_pi1(unsigned int *qp,
                    unsigned int *np, int nn, unsigned int n1,
                    unsigned int *dp, int dn,
                    unsigned int dinv)
/*@ bare */
{
  int i;

  unsigned int d1, d0;
  unsigned int cy, cy1;
  unsigned int q;

  d1 = dp[dn - 1];
  d0 = dp[dn - 2];

  i = nn - dn;
  /*@ Inv Assert exists l_cur l_done qv_done remv,
          qp == qp0 &&
          np == np0 &&
          dp == dp0 &&
          nn == nn0 &&
          dn == dn0 &&
          d1 == Znth(dn - 1, l_dp, 0) &&
          d0 == Znth(dn - 2, l_dp, 0) &&
          dn > 2 &&
          dn <= nn &&
          nn <= INT_MAX &&
          -1 <= i &&
          i <= nn - dn &&
          Zlength(l_cur) == nn &&
          Zlength(l_dp) == dn &&
          Zlength(l_done) == nn - dn - i &&
          list_within_bound(UINT_MOD, l_cur) &&
          list_within_bound(UINT_MOD, l_dp) &&
          list_within_bound(UINT_MOD, l_done) &&
          list_to_Z(UINT_MOD, l_dp) == dval &&
          list_to_Z(UINT_MOD, l_done) == qv_done &&
          0 < dval &&
          0 <= n1 &&
          n1 <= UINT_MAX &&
          UINT_MOD / 2 <= d1 &&
          d1 <= UINT_MAX &&
          0 <= d0 &&
          d0 <= UINT_MAX &&
          0 <= dinv &&
          dinv <= UINT_MAX &&
          (dinv + UINT_MOD) * (UINT_MOD * d1 + d0) <=
            Z::pow(UINT_MOD, 3) - 1 &&
          Z::pow(UINT_MOD, 3) - 1 <
            (dinv + UINT_MOD + 1) * (UINT_MOD * d1 + d0) &&
          remv ==
            n1 * Z::pow(UINT_MOD, dn + i) +
            list_to_Z(UINT_MOD, sublist(0, dn + i, l_cur)) &&
          0 <= remv &&
          remv < dval * Z::pow(UINT_MOD, i + 1) &&
          n1_orig * Z::pow(UINT_MOD, nn) + list_to_Z(UINT_MOD, l_np) ==
            qv_done * Z::pow(UINT_MOD, i + 1) * dval + remv &&
          UIntArray::full(np, nn, l_cur) *
          UIntArray::full(dp, dn, l_dp) *
          ((qp == 0 && emp) ||
           (qp != 0 &&
            UIntArray::undef_seg(qp, 0, i + 1) *
            UIntArray::seg(qp, i + 1, nn - dn + 1, l_done))) *
          has_uint_permission(&q) *
          has_uint_permission(&cy) *
          has_uint_permission(&cy1)
  */
  while (i >= 0)
    {
      unsigned int *np_i;
      unsigned int n0;

      np_i = np + i;
      /*@ Assert exists l_cur l_done l_low l_mid l_high qv_done remv,
            qp == qp0 &&
            np == np0 &&
            dp == dp0 &&
            nn == nn0 &&
            dn == dn0 &&
            d1 == Znth(dn - 1, l_dp, 0) &&
            d0 == Znth(dn - 2, l_dp, 0) &&
            dn > 2 &&
            dn <= nn &&
            nn <= INT_MAX &&
            0 <= i &&
            i <= nn - dn &&
            Zlength(l_cur) == nn &&
            Zlength(l_dp) == dn &&
            Zlength(l_done) == nn - dn - i &&
            l_low == sublist(0, i, l_cur) &&
            l_mid == sublist(i, i + dn, l_cur) &&
            l_high == sublist(i + dn, nn, l_cur) &&
            Zlength(l_low) == i &&
            Zlength(l_mid) == dn &&
            Zlength(l_high) == nn - (i + dn) &&
            list_within_bound(UINT_MOD, l_cur) &&
            list_within_bound(UINT_MOD, l_dp) &&
            list_within_bound(UINT_MOD, l_done) &&
            list_within_bound(UINT_MOD, l_low) &&
            list_within_bound(UINT_MOD, l_mid) &&
            list_within_bound(UINT_MOD, l_high) &&
            list_to_Z(UINT_MOD, l_dp) == dval &&
            list_to_Z(UINT_MOD, l_done) == qv_done &&
            0 < dval &&
            0 <= n1 &&
            n1 <= UINT_MAX &&
            UINT_MOD / 2 <= d1 &&
            d1 <= UINT_MAX &&
            0 <= d0 &&
            d0 <= UINT_MAX &&
            0 <= dinv &&
            dinv <= UINT_MAX &&
            (dinv + UINT_MOD) * (UINT_MOD * d1 + d0) <=
              Z::pow(UINT_MOD, 3) - 1 &&
            Z::pow(UINT_MOD, 3) - 1 <
              (dinv + UINT_MOD + 1) * (UINT_MOD * d1 + d0) &&
            remv ==
              n1 * Z::pow(UINT_MOD, dn + i) +
              list_to_Z(UINT_MOD, sublist(0, dn + i, l_cur)) &&
            0 <= remv &&
            remv < dval * Z::pow(UINT_MOD, i + 1) &&
            n1_orig * Z::pow(UINT_MOD, nn) + list_to_Z(UINT_MOD, l_np) ==
              qv_done * Z::pow(UINT_MOD, i + 1) * dval + remv &&
            np_i == np + i * sizeof(unsigned int) &&
            has_uint_permission(&n0) *
            UIntArray::seg(np, 0, i, l_low) *
            UIntArray::full(np_i, dn, l_mid) *
            UIntArray::seg(np, i + dn, nn, l_high) *
            UIntArray::full(dp, dn, l_dp) *
            ((qp == 0 && emp) ||
             (qp != 0 &&
              UIntArray::undef_seg(qp, 0, i + 1) *
              UIntArray::seg(qp, i + 1, nn - dn + 1, l_done))) *
            has_uint_permission(&q) *
            has_uint_permission(&cy) *
            has_uint_permission(&cy1)
      */
      n0 = np_i[dn - 1];

      if (n1 == d1 && n0 == d0)
        {
          q = 4294967295U;
          /*@ 0 <= q && q <= UINT_MAX by local */
          /*@ Given l_cur l_done l_low l_mid l_high qv_done remv */
          mpn_submul_1(np_i, dp, dn, q)
          /*@ where l_rp = l_mid, l_up = l_dp */;
          n1 = np_i[dn - 1];
        }
      else
        {
          gmp_udiv_qr_3by2(&q, &n1, &n0, n1, n0, np_i[dn - 2], d1, d0, dinv);

          /*@ Assert exists l_cur l_done l_low l_mid l_high
                    l_mid_low l_mid_high l_dp_low l_dp_high
                    qv_done remv n1_in,
                qp == qp0 &&
                np == np0 &&
                dp == dp0 &&
                nn == nn0 &&
                dn == dn0 &&
                d1 == Znth(dn - 1, l_dp, 0) &&
                d0 == Znth(dn - 2, l_dp, 0) &&
                dn > 2 &&
                dn <= nn &&
                nn <= INT_MAX &&
                0 <= i &&
                i <= nn - dn &&
                Zlength(l_cur) == nn &&
                Zlength(l_dp) == dn &&
                Zlength(l_done) == nn - dn - i &&
                l_low == sublist(0, i, l_cur) &&
                l_mid == sublist(i, i + dn, l_cur) &&
                l_high == sublist(i + dn, nn, l_cur) &&
                l_mid_low == sublist(0, dn - 2, l_mid) &&
                l_mid_high == sublist(dn - 2, dn, l_mid) &&
                l_dp_low == sublist(0, dn - 2, l_dp) &&
                l_dp_high == sublist(dn - 2, dn, l_dp) &&
                Zlength(l_low) == i &&
                Zlength(l_mid) == dn &&
                Zlength(l_high) == nn - (i + dn) &&
                Zlength(l_mid_low) == dn - 2 &&
                Zlength(l_mid_high) == 2 &&
                Zlength(l_dp_low) == dn - 2 &&
                Zlength(l_dp_high) == 2 &&
                list_within_bound(UINT_MOD, l_cur) &&
                list_within_bound(UINT_MOD, l_dp) &&
                list_within_bound(UINT_MOD, l_done) &&
                list_within_bound(UINT_MOD, l_low) &&
                list_within_bound(UINT_MOD, l_mid) &&
                list_within_bound(UINT_MOD, l_high) &&
                list_within_bound(UINT_MOD, l_mid_low) &&
                list_within_bound(UINT_MOD, l_mid_high) &&
                list_within_bound(UINT_MOD, l_dp_low) &&
                list_within_bound(UINT_MOD, l_dp_high) &&
                list_to_Z(UINT_MOD, l_dp) == dval &&
                list_to_Z(UINT_MOD, l_done) == qv_done &&
                0 < dval &&
                0 <= n1_in &&
                n1_in <= UINT_MAX &&
                0 <= q &&
                q <= UINT_MAX &&
                0 <= n1 &&
                n1 <= UINT_MAX &&
                0 <= n0 &&
                n0 <= UINT_MAX &&
                UINT_MOD / 2 <= d1 &&
                d1 <= UINT_MAX &&
                0 <= d0 &&
                d0 <= UINT_MAX &&
                0 <= dinv &&
                dinv <= UINT_MAX &&
                (dinv + UINT_MOD) * (UINT_MOD * d1 + d0) <=
                  Z::pow(UINT_MOD, 3) - 1 &&
                Z::pow(UINT_MOD, 3) - 1 <
                  (dinv + UINT_MOD + 1) * (UINT_MOD * d1 + d0) &&
                n1_in * UINT_MOD + Znth(dn - 1, l_mid, 0) <
                  d1 * UINT_MOD + d0 &&
                n1_in * Z::pow(UINT_MOD, 2) +
                  Znth(dn - 1, l_mid, 0) * UINT_MOD +
                  Znth(dn - 2, l_mid, 0) ==
                  q * (d1 * UINT_MOD + d0) + n1 * UINT_MOD + n0 &&
                n1 * UINT_MOD + n0 < d1 * UINT_MOD + d0 &&
                remv ==
                  n1_in * Z::pow(UINT_MOD, dn + i) +
                  list_to_Z(UINT_MOD, sublist(0, dn + i, l_cur)) &&
                0 <= remv &&
                remv < dval * Z::pow(UINT_MOD, i + 1) &&
                n1_orig * Z::pow(UINT_MOD, nn) + list_to_Z(UINT_MOD, l_np) ==
                  qv_done * Z::pow(UINT_MOD, i + 1) * dval + remv &&
                np_i == np + i * sizeof(unsigned int) &&
                UIntArray::seg(np, 0, i, l_low) *
                UIntArray::full(np_i, dn - 2, l_mid_low) *
                UIntArray::seg(np_i, dn - 2, dn, l_mid_high) *
                UIntArray::seg(np, i + dn, nn, l_high) *
                UIntArray::full(dp, dn - 2, l_dp_low) *
                UIntArray::seg(dp, dn - 2, dn, l_dp_high) *
                ((qp == 0 && emp) ||
                 (qp != 0 &&
                  UIntArray::undef_seg(qp, 0, i + 1) *
                  UIntArray::seg(qp, i + 1, nn - dn + 1, l_done))) *
                has_uint_permission(&cy) *
                has_uint_permission(&cy1)
          */
          /*@ Given l_cur l_done l_low l_mid l_high
                    l_mid_low l_mid_high l_dp_low l_dp_high
	                    qv_done remv n1_in */
	          cy = mpn_submul_1(np_i, dp, dn - 2, q)
	               /*@ where l_rp = l_mid_low, l_up = l_dp_low */;
          /*@ 0 <= cy && cy <= UINT_MAX by local */

	          cy1 = n0 < cy;
          n0 = n0 - cy;
          cy = n1 < cy1;
          n1 = n1 - cy1;
          np_i[dn - 2] = n0;

	      if (cy != 0)
	        {
	          /*@ Assert exists l_cur l_done l_low l_mid l_high
	                    l_mid_low l_mid_high l_dp_low l_dp_high
	                    l_np_add l_np_tail l_dp_add l_dp_tail
	                    qv_done remv n1_in n1_before n0_before
	                    val_out l_out retval val_np_add val_dp_add,
	                qp == qp0 &&
	                np == np0 &&
	                dp == dp0 &&
	                nn == nn0 &&
	                dn == dn0 &&
	                d1 == Znth(dn - 1, l_dp, 0) &&
	                d0 == Znth(dn - 2, l_dp, 0) &&
	                dn > 2 &&
	                dn - 1 >= 0 &&
	                dn - 1 <= INT_MAX &&
	                dn <= nn &&
	                nn <= INT_MAX &&
	                0 <= i &&
	                i <= nn - dn &&
	                Zlength(l_cur) == nn &&
	                Zlength(l_dp) == dn &&
	                Zlength(l_done) == nn - dn - i &&
	                l_low == sublist(0, i, l_cur) &&
	                l_mid == sublist(i, i + dn, l_cur) &&
	                l_high == sublist(i + dn, nn, l_cur) &&
	                l_mid_low == sublist(0, dn - 2, l_mid) &&
	                l_mid_high == sublist(dn - 2, dn, l_mid) &&
	                l_dp_low == sublist(0, dn - 2, l_dp) &&
	                l_dp_high == sublist(dn - 2, dn, l_dp) &&
	                l_np_add == app(l_out, sublist(0, 1, replace_Znth(0, n0, l_mid_high))) &&
	                l_np_tail == sublist(1, 2, replace_Znth(0, n0, l_mid_high)) &&
	                l_dp_add == app(l_dp_low, sublist(0, 1, l_dp_high)) &&
	                l_dp_tail == sublist(1, 2, l_dp_high) &&
	                Zlength(l_low) == i &&
	                Zlength(l_mid) == dn &&
	                Zlength(l_high) == nn - (i + dn) &&
	                Zlength(l_mid_low) == dn - 2 &&
	                Zlength(l_mid_high) == 2 &&
	                Zlength(l_dp_low) == dn - 2 &&
	                Zlength(l_dp_high) == 2 &&
	                Zlength(l_out) == dn - 2 &&
	                Zlength(l_np_add) == dn - 1 &&
	                Zlength(l_np_tail) == 1 &&
	                Zlength(l_dp_add) == dn - 1 &&
	                Zlength(l_dp_tail) == 1 &&
	                list_within_bound(UINT_MOD, l_cur) &&
	                list_within_bound(UINT_MOD, l_dp) &&
	                list_within_bound(UINT_MOD, l_done) &&
	                list_within_bound(UINT_MOD, l_low) &&
	                list_within_bound(UINT_MOD, l_high) &&
	                list_within_bound(UINT_MOD, l_mid_high) &&
	                list_within_bound(UINT_MOD, l_dp_low) &&
	                list_within_bound(UINT_MOD, l_dp_high) &&
	                list_within_bound(UINT_MOD, l_out) &&
	                list_within_bound(UINT_MOD, l_np_add) &&
	                list_within_bound(UINT_MOD, l_np_tail) &&
	                list_within_bound(UINT_MOD, l_dp_add) &&
	                list_within_bound(UINT_MOD, l_dp_tail) &&
	                list_to_Z(UINT_MOD, l_dp) == dval &&
	                list_to_Z(UINT_MOD, l_done) == qv_done &&
	                list_to_Z(UINT_MOD, l_out) == val_out &&
	                list_to_Z(UINT_MOD, l_np_add) == val_np_add &&
	                list_to_Z(UINT_MOD, l_dp_add) == val_dp_add &&
	                val_out - retval * Z::pow(UINT_MOD, dn - 2) ==
	                  list_to_Z(UINT_MOD, l_mid_low) -
	                  list_to_Z(UINT_MOD, l_dp_low) * q &&
	                0 < dval &&
	                0 <= n1_in &&
	                n1_in <= UINT_MAX &&
	                0 <= q &&
	                q <= UINT_MAX &&
	                0 <= n1_before &&
	                n1_before <= UINT_MAX &&
	                0 <= n0_before &&
	                n0_before <= UINT_MAX &&
	                n1_before < 1 &&
	                n0_before < retval &&
	                n1 == unsigned_last_nbits(n1_before - 1, 32) &&
	                n0 == unsigned_last_nbits(n0_before - retval, 32) &&
	                cy == 1 &&
	                cy1 == 1 &&
	                UINT_MOD / 2 <= d1 &&
	                d1 <= UINT_MAX &&
	                0 <= d0 &&
	                d0 <= UINT_MAX &&
	                0 <= dinv &&
	                dinv <= UINT_MAX &&
	                (dinv + UINT_MOD) * (UINT_MOD * d1 + d0) <=
	                  Z::pow(UINT_MOD, 3) - 1 &&
	                Z::pow(UINT_MOD, 3) - 1 <
	                  (dinv + UINT_MOD + 1) * (UINT_MOD * d1 + d0) &&
	                n1_in * UINT_MOD + Znth(dn - 1, l_mid, 0) <
	                  d1 * UINT_MOD + d0 &&
	                n1_in * Z::pow(UINT_MOD, 2) +
	                  Znth(dn - 1, l_mid, 0) * UINT_MOD +
	                  Znth(dn - 2, l_mid, 0) ==
	                  q * (d1 * UINT_MOD + d0) + n1_before * UINT_MOD + n0_before &&
	                n1_before * UINT_MOD + n0_before < d1 * UINT_MOD + d0 &&
	                remv ==
	                  n1_in * Z::pow(UINT_MOD, dn + i) +
	                  list_to_Z(UINT_MOD, sublist(0, dn + i, l_cur)) &&
	                0 <= remv &&
	                remv < dval * Z::pow(UINT_MOD, i + 1) &&
	                n1_orig * Z::pow(UINT_MOD, nn) + list_to_Z(UINT_MOD, l_np) ==
	                  qv_done * Z::pow(UINT_MOD, i + 1) * dval + remv &&
	                np_i == np + i * sizeof(unsigned int) &&
	                UIntArray::seg(np, 0, i, l_low) *
	                mpd_store_Z(UINT_MOD, np_i, val_np_add, dn - 1) *
	                UIntArray::seg(np_i, dn - 1, dn, l_np_tail) *
	                UIntArray::seg(np, i + dn, nn, l_high) *
	                mpd_store_Z(UINT_MOD, dp, val_dp_add, dn - 1) *
	                UIntArray::seg(dp, dn - 1, dn, l_dp_tail) *
	                ((qp == 0 && emp) ||
	                 (qp != 0 &&
	                  UIntArray::undef_seg(qp, 0, i + 1) *
	                  UIntArray::seg(qp, i + 1, nn - dn + 1, l_done)))
	          */
	          n1 = n1 + d1 + mpn_add_n(np_i, np_i, dp, dn - 1);
	          q = q - 1;
	        }
        }

      if (qp)
        qp[i] = q;
      i = i - 1;
    }

  np[dn - 1] = n1;
}
