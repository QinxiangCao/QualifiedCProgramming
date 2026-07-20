#include "fme_ge_gmp/gmp/gmp_def.h"

/*@ Extern Coq (optional_q_undef : Z -> Z -> Assertion)
               (optional_q_full : Z -> Z -> list Z -> Assertion)
               (gmp_div_inverse_valid : Z -> Z -> Z -> Z -> Z -> Z -> Prop) */

static unsigned int *
gmp_alloc_limbs (int size)
/*@ pos
  Require
    size > 0
  Ensure
    __return != 0 &&
    UIntArray::undef_full(__return, size)
*/
/*@ nonneg
  Require
    size >= 0
  Ensure
    UIntArray::undef_full(__return, size)
*/;

static void
gmp_free_limbs (unsigned int *old, int size)
/*@
  With
    n len
  Require
    mpd_store_Z_compact(UINT_MOD,old, n, len) *
    UIntArray::undef_seg(old, len, size)
  Ensure
    emp
*/;

struct gmp_div_inverse *malloc_gmp_div_inverse()
/*@ Require emp
  Ensure
    __return != 0 &&
    div_inverse_slot(__return)
*/;

void free_gmp_div_inverse(struct gmp_div_inverse *inv)
/*@
  Require
    div_inverse_slot(inv)
  Ensure emp
*/;

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
*/;

void mpn_div_qr_invert(struct gmp_div_inverse *inv,
                       unsigned int *dp, int dn)
/*@
  With d
  Require dn > 0 && dn <= INT_MAX &&
          mpd_store_Z_compact(UINT_MOD, dp, d, dn) *
          div_inverse_slot(inv)
  Ensure
          mpd_store_Z_compact(UINT_MOD, dp, d, dn) *
          store_div_inverse(inv, dn, d)
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
*/;

void mpn_div_qr(unsigned int *qp, unsigned int *np,
                int nn, unsigned int *dp, int dn)
/*@
  With qp0 np0 dp0 nn0 dn0 l_np d_orig
  Require qp0 == qp && np0 == np && dp0 == dp &&
          nn0 == nn && dn0 == dn &&
          dn > 0 && dn <= nn && nn <= INT_MAX &&
          Zlength(l_np) == nn &&
          list_within_bound(UINT_MOD, l_np) &&
          optional_q_undef(qp, nn - dn + 1) *
          UIntArray::full(np, nn, l_np) *
          mpd_store_Z_compact(UINT_MOD, dp, d_orig, dn)
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
          mpd_store_Z_compact(UINT_MOD, dp0, d_orig, dn0)
*/
{
  struct gmp_div_inverse *inv;
  unsigned int *tp;

  inv = malloc_gmp_div_inverse();
  tp = (void *)0;
  /*@ Assert
      qp0 == qp && np0 == np && dp0 == dp && dp0 == dp@pre &&
      nn0 == nn && dn0 == dn &&
      tp == 0 &&
      dn > 0 && dn <= nn && nn <= INT_MAX &&
      Zlength(l_np) == nn &&
      list_within_bound(UINT_MOD, l_np) &&
      optional_q_undef(qp, nn - dn + 1) *
      UIntArray::full(np, nn, l_np) *
      mpd_store_Z_compact(UINT_MOD, dp, d_orig, dn) *
      div_inverse_slot(inv)
  */

  mpn_div_qr_invert(inv, dp, dn)
  /*@ where d = d_orig */;
  /*@ Assert exists shift d1 d0 di,
      qp0 == qp && np0 == np && dp0 == dp && dp0 == dp@pre &&
      nn0 == nn && dn0 == dn &&
      tp == 0 &&
      dn > 0 && dn <= nn && nn <= INT_MAX &&
      Zlength(l_np) == nn &&
      list_within_bound(UINT_MOD, l_np) &&
      gmp_div_inverse_valid(dn, d_orig, shift, d1, d0, di) &&
      optional_q_undef(qp, nn - dn + 1) *
      UIntArray::full(np, nn, l_np) *
      mpd_store_Z_compact(UINT_MOD, dp, d_orig, dn) *
      ((dn == 1 &&
        store(&(inv->shift), shift) *
        store(&(inv->d1), d1) *
        undef_data_at(&(inv->d0), unsigned int) *
        store(&(inv->di), di)) ||
       (dn != 1 &&
        store(&(inv->shift), shift) *
        store(&(inv->d1), d1) *
        store(&(inv->d0), d0) *
        store(&(inv->di), di)))
  */

  if (dn > 2 && inv->shift > 0)
    {
      unsigned int cy;

      tp = gmp_alloc_limbs(dn) /*@ where (pos) */;
      /*@ Assert exists shift d1 d0 di l_dp,
          qp0 == qp && np0 == np && dp0 == dp && dp0 == dp@pre &&
          nn0 == nn && dn0 == dn &&
          tp != 0 &&
          dn > 2 && 1 <= shift && shift < 32 &&
          dn <= nn && nn <= INT_MAX &&
          Zlength(l_np) == nn &&
          Zlength(l_dp) == dn &&
          list_within_bound(UINT_MOD, l_np) &&
          list_within_bound(UINT_MOD, l_dp) &&
          list_to_Z(UINT_MOD, l_dp) == d_orig &&
          last(l_dp, 1) >= 1 &&
          gmp_div_inverse_valid(dn, d_orig, shift, d1, d0, di) &&
          optional_q_undef(qp, nn - dn + 1) *
          UIntArray::full(np, nn, l_np) *
          UIntArray::full(dp, dn, l_dp) *
          UIntArray::undef_full(tp, dn) *
          store(&(inv->shift), shift) *
          store(&(inv->d1), d1) *
          store(&(inv->d0), d0) *
          store(&(inv->di), di) *
          has_uint_permission(&cy)
      */
      /*@ Given l_dp */
      cy = mpn_lshift(tp, dp, dn, inv->shift)
           /*@ where (nonalias) l_up = l_dp */;
      /*@ cy == 0 by local */
      dp = tp;
      /*@ Assert exists shift d1 d0 di l_dp l_norm,
          qp0 == qp && np0 == np && dp0 == dp@pre &&
          nn0 == nn && dn0 == dn &&
          tp != 0 && dp == tp &&
          dn > 2 && 1 <= shift && shift < 32 &&
          dn <= nn && nn <= INT_MAX &&
          Zlength(l_np) == nn &&
          Zlength(l_dp) == dn &&
          Zlength(l_norm) == dn &&
          list_within_bound(UINT_MOD, l_np) &&
          list_within_bound(UINT_MOD, l_dp) &&
          list_within_bound(UINT_MOD, l_norm) &&
          list_to_Z(UINT_MOD, l_dp) == d_orig &&
          last(l_dp, 1) >= 1 &&
          list_to_Z(UINT_MOD, l_norm) == d_orig * Z::pow(2, shift) &&
          gmp_div_inverse_valid(dn, d_orig, shift, d1, d0, di) &&
          optional_q_undef(qp, nn - dn + 1) *
          UIntArray::full(np, nn, l_np) *
          UIntArray::full(dp0, dn, l_dp) *
          UIntArray::full(dp, dn, l_norm) *
          store(&(inv->shift), shift) *
          store(&(inv->d1), d1) *
          store(&(inv->d0), d0) *
          store(&(inv->di), di) *
          has_uint_permission(&cy)
      */
    }
  /*@ Assert exists shift d1 d0 di,
      qp0 == qp && np0 == np && dp0 == dp@pre &&
      nn0 == nn && dn0 == dn &&
      dn > 0 && dn <= nn && nn <= INT_MAX &&
      Zlength(l_np) == nn &&
      list_within_bound(UINT_MOD, l_np) &&
      gmp_div_inverse_valid(dn, d_orig, shift, d1, d0, di) &&
      ((tp == 0 && dp == dp0 &&
        (dn <= 2 || shift == 0) &&
        optional_q_undef(qp, nn - dn + 1) *
        UIntArray::full(np, nn, l_np) *
        store_preinv_divisor(dp, inv, dn, d_orig)) ||
       (tp != 0 && dp == tp && dn > 2 &&
        optional_q_undef(qp, nn - dn + 1) *
        UIntArray::full(np, nn, l_np) *
        mpd_store_Z_compact(UINT_MOD, dp0, d_orig, dn) *
        store_preinv_divisor(dp, inv, dn, d_orig)))
  */

  mpn_div_qr_preinv(qp, np, nn, dp, dn, inv)
  /*@ where qp0 = qp, np0 = np, dp0 = dp, inv0 = inv,
             nn0 = nn, dn0 = dn, l_np = l_np, d_orig = d_orig */;
  /*@ Assert exists l_q l_rem l_tail qv rv shift d1 d0 di,
      qp0 == qp && np0 == np && dp0 == dp@pre &&
      nn0 == nn && dn0 == dn &&
      dn > 0 && dn <= nn && nn <= INT_MAX &&
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
      gmp_div_inverse_valid(dn, d_orig, shift, d1, d0, di) &&
      ((tp == 0 && dp == dp0 &&
        (dn <= 2 || shift == 0) &&
        optional_q_full(qp, nn - dn + 1, l_q) *
        UIntArray::seg(np, 0, dn, l_rem) *
        UIntArray::seg(np, dn, nn, l_tail) *
        store_preinv_divisor(dp, inv, dn, d_orig)) ||
       (tp != 0 && dp == tp && dn > 2 &&
        optional_q_full(qp, nn - dn + 1, l_q) *
        UIntArray::seg(np, 0, dn, l_rem) *
        UIntArray::seg(np, dn, nn, l_tail) *
        mpd_store_Z_compact(UINT_MOD, dp0, d_orig, dn) *
        store_preinv_divisor(dp, inv, dn, d_orig)))
  */

  if (tp)
    {
      /*@ Assert exists l_q l_rem l_tail qv rv l_dp shift d1 d0 di norm_val,
          qp0 == qp && np0 == np && dp0 == dp@pre &&
          nn0 == nn && dn0 == dn &&
          tp != 0 && dp == tp &&
          dn > 2 && dn <= nn && nn <= INT_MAX &&
          Zlength(l_q) == nn - dn + 1 &&
          Zlength(l_rem) == dn &&
          Zlength(l_tail) == nn - dn &&
          Zlength(l_dp) == dn &&
          list_within_bound(UINT_MOD, l_q) &&
          list_within_bound(UINT_MOD, l_rem) &&
          list_within_bound(UINT_MOD, l_tail) &&
          list_within_bound(UINT_MOD, l_dp) &&
          list_to_Z(UINT_MOD, l_q) == qv &&
          list_to_Z(UINT_MOD, l_rem) == rv &&
          list_to_Z(UINT_MOD, l_np) == qv * d_orig + rv &&
          0 <= rv && rv < d_orig &&
          list_to_Z(UINT_MOD, l_dp) == norm_val &&
          is_compact_Z(UINT_MOD, norm_val, dn) &&
          optional_q_full(qp, nn - dn + 1, l_q) *
          UIntArray::seg(np, 0, dn, l_rem) *
          UIntArray::seg(np, dn, nn, l_tail) *
          mpd_store_Z_compact(UINT_MOD, dp0, d_orig, dn) *
          mpd_store_Z_compact(UINT_MOD, tp, norm_val, dn) *
          UIntArray::undef_seg(tp, dn, dn) *
          store(&(inv->shift), shift) *
          store(&(inv->d1), d1) *
          store(&(inv->d0), d0) *
          store(&(inv->di), di)
      */
      /*@ Given norm_val */
      gmp_free_limbs(tp, dn)
      /*@ where n = norm_val, len = dn */;
    }
  /*@ Assert exists l_q l_rem l_tail qv rv,
      qp0 == qp && np0 == np && dp0 == dp@pre &&
      nn0 == nn && dn0 == dn &&
      dn > 0 && dn <= nn && nn <= INT_MAX &&
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
      mpd_store_Z_compact(UINT_MOD, dp0, d_orig, dn) *
      store(&tp, unsigned int *, tp) *
      store(&dp, unsigned int *, dp) *
      div_inverse_slot(inv)
  */
  free_gmp_div_inverse(inv);
  /*@ Assert exists l_q l_rem l_tail qv rv,
      qp0 == qp && np0 == np && dp0 == dp@pre &&
      nn0 == nn && dn0 == dn &&
      dn > 0 && dn <= nn && nn <= INT_MAX &&
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
      mpd_store_Z_compact(UINT_MOD, dp0, d_orig, dn) *
      store(&tp, unsigned int *, tp) *
      store(&dp, unsigned int *, dp) *
      store(&inv, struct gmp_div_inverse *, inv)
  */
}
