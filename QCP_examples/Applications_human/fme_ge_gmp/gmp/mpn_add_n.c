#include "fme_ge_gmp/gmp/gmp_def.h"

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
*/
/*@ rp_eq_bp
  With val_a val_b
  Require
    rp == bp && n >= 0 &&
    mpd_store_Z(UINT_MOD, ap, val_a, n) *
    mpd_store_Z(UINT_MOD, bp, val_b, n)
  Ensure exists val_r_out,
    (val_r_out + __return * Z::pow(UINT_MOD, n) == val_a + val_b) &&
    rp == bp &&
    mpd_store_Z(UINT_MOD, ap, val_a, n) *
    mpd_store_Z(UINT_MOD, rp, val_r_out, n)
*/
/*@ rp_eq_ap */
/*@ rp_eq_bp */
{
  /*@
    mpd_store_Z(UINT_MOD, ap, val_a_rp_eq_ap, n) *
    mpd_store_Z(UINT_MOD, bp, val_b_rp_eq_ap, n)
      $ rp_eq_ap
    which implies
    exists l_a l_b,
      Zlength(l_a) == n && Zlength(l_b) == n &&
      list_to_Z(UINT_MOD, l_a) == val_a_rp_eq_ap &&
      list_to_Z(UINT_MOD, l_b) == val_b_rp_eq_ap &&
      list_within_bound(UINT_MOD, l_a) &&
      list_within_bound(UINT_MOD, l_b) &&
      UIntArray::full(ap, n, l_a) *
      UIntArray::full(bp, n, l_b)
  */
  /*@
    mpd_store_Z(UINT_MOD, ap, val_a_rp_eq_bp, n) *
    mpd_store_Z(UINT_MOD, bp, val_b_rp_eq_bp, n)
      $ rp_eq_bp
    which implies
    exists l_a l_b,
      Zlength(l_a) == n && Zlength(l_b) == n &&
      list_to_Z(UINT_MOD, l_a) == val_a_rp_eq_bp &&
      list_to_Z(UINT_MOD, l_b) == val_b_rp_eq_bp &&
      list_within_bound(UINT_MOD, l_a) &&
      list_within_bound(UINT_MOD, l_b) &&
      UIntArray::full(ap, n, l_a) *
      UIntArray::full(bp, n, l_b)
  */
  int i;
  unsigned int cy;

  i = 0;
  cy = 0;
  /*@ Given l_a l_b */
  /*@
    n >= 0 && UIntArray::full(ap, n, l_a) $ rp_eq_ap
    which implies
    n >= 0 &&
    UIntArray::seg(ap, 0, 0, nil) *
    UIntArray::seg(ap, 0, Zlength(l_a), sublist(0, Zlength(l_a), l_a))
  */
  /*@
    n >= 0 && Zlength(l_a) == n && UIntArray::full(bp, n, l_b) $ rp_eq_bp
    which implies
    n >= 0 &&
    UIntArray::seg(bp, 0, 0, nil) *
    UIntArray::seg(bp, 0, Zlength(l_a), sublist(0, Zlength(l_a), l_b))
  */
  /*@
    rp == ap &&
    UIntArray::seg(ap, 0, 0, nil) *
    UIntArray::seg(ap, 0, Zlength(l_a), sublist(0, Zlength(l_a), l_a))
      $ rp_eq_ap
    which implies
    rp == ap &&
    UIntArray::seg(rp, 0, 0, nil) *
    UIntArray::seg(rp, 0, Zlength(l_a), sublist(0, Zlength(l_a), l_a))
  */
  /*@
    rp == bp &&
    UIntArray::seg(bp, 0, 0, nil) *
    UIntArray::seg(bp, 0, Zlength(l_a), sublist(0, Zlength(l_a), l_b))
      $ rp_eq_bp
    which implies
    rp == bp &&
    UIntArray::seg(rp, 0, 0, nil) *
    UIntArray::seg(rp, 0, Zlength(l_a), sublist(0, Zlength(l_a), l_b))
  */
  /*@ Inv
    rp_eq_ap:
    exists l_r val_a_prefix val_b_prefix val_r,
      rp == ap &&
      rp == rp@pre && ap == ap@pre && bp == bp@pre && n == n@pre &&
      n >= 0 &&
      0 <= i && i <= n && 0 <= cy && cy <= 2 &&
      list_to_Z(UINT_MOD, sublist(0, i, l_a)) == val_a_prefix &&
      list_to_Z(UINT_MOD, sublist(0, i, l_b)) == val_b_prefix &&
      list_to_Z(UINT_MOD, l_r) == val_r &&
      list_within_bound(UINT_MOD, l_r) &&
      list_within_bound(UINT_MOD, l_a) &&
      list_within_bound(UINT_MOD, l_b) &&
      Zlength(l_r) == i &&
      Zlength(l_a) == n && Zlength(l_b) == n &&
      val_r + cy * Z::pow(UINT_MOD, i) == val_a_prefix + val_b_prefix &&
      UIntArray::seg(rp, 0, i, l_r) *
      UIntArray::seg(rp, i, Zlength(l_a), sublist(i, Zlength(l_a), l_a));
    rp_eq_bp:
    exists l_r val_a_prefix val_b_prefix val_r,
      rp == bp &&
      rp == rp@pre && ap == ap@pre && bp == bp@pre && n == n@pre &&
      n >= 0 &&
      0 <= i && i <= n && 0 <= cy && cy <= 2 &&
      list_to_Z(UINT_MOD, sublist(0, i, l_a)) == val_a_prefix &&
      list_to_Z(UINT_MOD, sublist(0, i, l_b)) == val_b_prefix &&
      list_to_Z(UINT_MOD, l_r) == val_r &&
      list_within_bound(UINT_MOD, l_r) &&
      list_within_bound(UINT_MOD, l_a) &&
      list_within_bound(UINT_MOD, l_b) &&
      Zlength(l_r) == i &&
      Zlength(l_a) == n && Zlength(l_b) == n &&
      val_r + cy * Z::pow(UINT_MOD, i) == val_a_prefix + val_b_prefix &&
      UIntArray::seg(rp, 0, i, l_r) *
      UIntArray::seg(rp, i, Zlength(l_a), sublist(i, Zlength(l_a), l_b))
    with
      rp_eq_ap ==> rp_eq_ap
      rp_eq_bp ==> rp_eq_bp
  */
  while (i < n)
  {
    unsigned int a, b, r;
    /*@
      rp == ap && UIntArray::seg(rp, i, Zlength(l_a), sublist(i, Zlength(l_a), l_a))
        $ rp_eq_ap
      which implies
      rp == ap && UIntArray::seg(ap, i, Zlength(l_a), sublist(i, Zlength(l_a), l_a))
    */
    /*@
      rp == bp && UIntArray::seg(rp, i, Zlength(l_a), sublist(i, Zlength(l_a), l_b))
        $ rp_eq_bp
      which implies
      rp == bp && UIntArray::seg(bp, i, Zlength(l_a), sublist(i, Zlength(l_a), l_b))
    */
    a = ap[i]; b = bp[i];
    r = a + cy;
    cy = (r < cy);
    r += b;
    cy += (r < b);
    /*@
      rp == ap && UIntArray::seg(ap, i, Zlength(l_a), sublist(i, Zlength(l_a), l_a))
        $ rp_eq_ap
      which implies
      rp == ap && UIntArray::seg(rp, i, Zlength(l_a), sublist(i, Zlength(l_a), l_a))
    */
    /*@
      rp == bp && UIntArray::seg(bp, i, Zlength(l_a), sublist(i, Zlength(l_a), l_b))
        $ rp_eq_bp
      which implies
      rp == bp && UIntArray::seg(rp, i, Zlength(l_a), sublist(i, Zlength(l_a), l_b))
    */
    rp[i] = r;
    ++i;
  }
  return cy;
}
