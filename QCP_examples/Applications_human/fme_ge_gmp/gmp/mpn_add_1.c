#include "fme_ge_gmp/gmp/gmp_def.h"

unsigned int
mpn_add_1 (unsigned int *rp, unsigned int *ap, int n, unsigned int b)
/*@ rp_eq_ap
  With val b0
  Require
    rp == ap && n > 0 && b == b0 && 0 <= b0 && b0 <= UINT_MAX &&
    mpd_store_Z(UINT_MOD, ap, val, n)
  Ensure exists val',
    (val' + __return * Z::pow(UINT_MOD, n) == val + b0) &&
    rp == ap &&
    mpd_store_Z(UINT_MOD, rp, val', n)
*/
/*@ non_alias
  With val b0
  Require
    rp != ap && n > 0 && b == b0 && 0 <= b0 && b0 <= UINT_MAX &&
    mpd_store_Z(UINT_MOD, ap, val, n) *
    UIntArray::undef_full(rp, n)
  Ensure exists val',
    (val' + __return * Z::pow(UINT_MOD, n) == val + b0) &&
    mpd_store_Z(UINT_MOD, ap, val, n) *
    mpd_store_Z(UINT_MOD, rp, val', n)
*/
/*@ rp_eq_ap */
/*@ non_alias */
{
  /*@
    mpd_store_Z(UINT_MOD, ap, val_rp_eq_ap, n)
    $ rp_eq_ap
    which implies
    exists l,
      Zlength(l) == n &&
      list_to_Z(UINT_MOD, l) == val_rp_eq_ap &&
      list_within_bound(UINT_MOD, l) &&
      UIntArray::full(ap, n, l)
  */
  /*@
    mpd_store_Z(UINT_MOD, ap, val_non_alias, n)
    $ non_alias
    which implies
    exists l,
      Zlength(l) == n &&
      list_to_Z(UINT_MOD, l) == val_non_alias &&
      list_within_bound(UINT_MOD, l) &&
      UIntArray::full(ap, n, l)
  */

  /*@ Given l */
  int i;
  i = 0;
  /*@
    n >= 0 && UIntArray::full(ap, n, l)
    $ rp_eq_ap
    which implies
    n >= 0 &&
    UIntArray::seg(ap, 0, 0, nil) *
    UIntArray::seg(ap, 0, Zlength(l), sublist(0, Zlength(l), l))
  */
  /*@
    rp == ap &&
    UIntArray::seg(ap, 0, 0, nil) *
    UIntArray::seg(ap, 0, Zlength(l), sublist(0, Zlength(l), l))
    $ rp_eq_ap
    which implies
    rp == ap &&
    UIntArray::seg(rp, 0, 0, nil) *
    UIntArray::seg(rp, 0, Zlength(l), sublist(0, Zlength(l), l))
  */
  /*@ Assert
      b == b0_rp_eq_ap && 0 <= b && b <= UINT_MAX &&
      i == 0 && rp == ap &&
      rp == rp@pre && ap == ap@pre && n == n@pre &&
      n > 0 &&
      Zlength(l) == n &&
      list_to_Z(UINT_MOD, l) == val_rp_eq_ap &&
      list_within_bound(UINT_MOD, l) &&
      UIntArray::seg(rp, 0, 0, nil) *
      UIntArray::seg(rp, 0, Zlength(l), sublist(0, Zlength(l), l))
      $ rp_eq_ap
  */
  /*@ Assert
      b == b0_non_alias && 0 <= b && b <= UINT_MAX &&
      i == 0 && rp != ap &&
      rp == rp@pre && ap == ap@pre && n == n@pre &&
      n > 0 &&
      Zlength(l) == n &&
      list_to_Z(UINT_MOD, l) == val_non_alias &&
      list_within_bound(UINT_MOD, l) &&
      UIntArray::full(ap, n, l) *
      UIntArray::undef_full(rp, n)
      $ non_alias
  */
  /*@ Branch name
      rp_eq_ap: rp == ap;
      non_alias: rp != ap
  */
  do
  {
    /*@
      rp == ap && rp == rp@pre && ap == ap@pre && n == n@pre &&
      UIntArray::seg(rp, i, Zlength(l), sublist(i, Zlength(l), l))
      $ rp_eq_ap
      which implies
      rp == ap && rp == rp@pre && ap == ap@pre && n == n@pre &&
      UIntArray::seg(ap, i, Zlength(l), sublist(i, Zlength(l), l))
    */
    unsigned int r = ap[i] + b;
    /*@
      rp == ap && rp == rp@pre && ap == ap@pre && n == n@pre &&
      UIntArray::seg(ap, i, Zlength(l), sublist(i, Zlength(l), l))
      $ rp_eq_ap
      which implies
      rp == ap && rp == rp@pre && ap == ap@pre && n == n@pre &&
      UIntArray::seg(rp, i, Zlength(l), sublist(i, Zlength(l), l))
    */
    // Carry out
    b = (r < b);
    rp[i] = r;
    ++i;
  }
  /*@ Inv
    rp_eq_ap:
    Assert
    exists l' val1 val2,
      1 <= i && i <= n && 0 <= b && b <= 1 &&
      rp == ap &&
      rp == rp@pre && ap == ap@pre && n == n@pre &&
      n > 0 &&
      Zlength(l') == i &&
      list_to_Z(UINT_MOD, sublist(0, i, l)) == val1 &&
      list_to_Z(UINT_MOD, l') == val2 &&
      list_within_bound(UINT_MOD, l') &&
      list_within_bound(UINT_MOD, l) &&
      Zlength(l) == n &&
      list_to_Z(UINT_MOD, l) == val_rp_eq_ap &&
      val2 + b * Z::pow(UINT_MOD, i) == val1 + b0_rp_eq_ap &&
      UIntArray::seg(rp, 0, i, l') *
      UIntArray::seg(rp, i, Zlength(l), sublist(i, Zlength(l), l));
    non_alias:
    Assert
    exists l' val1 val2,
      1 <= i && i <= n && 0 <= b && b <= 1 &&
      rp != ap &&
      rp == rp@pre && ap == ap@pre && n == n@pre &&
      n > 0 &&
      Zlength(l') == i &&
      list_to_Z(UINT_MOD, sublist(0, i, l)) == val1 &&
      list_to_Z(UINT_MOD, l') == val2 &&
      list_within_bound(UINT_MOD, l') &&
      list_within_bound(UINT_MOD, l) &&
      Zlength(l) == n &&
      list_to_Z(UINT_MOD, l) == val_non_alias &&
      val2 + b * Z::pow(UINT_MOD, i) == val1 + b0_non_alias &&
      UIntArray::full(ap, n, l) *
      UIntArray::seg(rp, 0, i, l') *
      UIntArray::undef_seg(rp, i, n)
  */
  while (i < n);

  return b;
}
