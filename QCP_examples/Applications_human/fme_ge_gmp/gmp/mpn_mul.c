#include "fme_ge_gmp/gmp/gmp_def.h"

unsigned int mpn_mul_1(unsigned int * rp, unsigned int * up, int n, unsigned int vl)
/*@
  With l
  Require
    n > 0 && n <= INT_MAX && 0 <= vl && vl <= UINT_MAX &&
    Zlength(l) == n &&
    list_within_bound(UINT_MOD, l) &&
    UIntArray::full(up, n, l) *
    UIntArray::undef_full(rp, n)
  Ensure
    exists l' val',
    Zlength(l') == n &&
    list_within_bound(UINT_MOD, l') &&
    list_to_Z(UINT_MOD, l') == val' &&
    (val' + __return * Z::pow(UINT_MOD, n) == list_to_Z(UINT_MOD, l) * vl) &&
    UIntArray::full(up, n, l) *
    UIntArray::full(rp, n, l')
*/;

unsigned int mpn_addmul_1(unsigned int *rp, unsigned int *up,
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
          val_out + __return * Z::pow(UINT_MOD, n) ==
            list_to_Z(UINT_MOD, l_rp) + list_to_Z(UINT_MOD, l_up) * vl &&
          UIntArray::full(rp, n, l_out) *
          UIntArray::full(up, n, l_up)
*/;

unsigned int mpn_mul(unsigned int *rp, unsigned int *up, int un,
                     unsigned int *vp, int vn)
/*@
  With l_src l_vp
  Require un > 0 && vn > 0 && vn <= un &&
          Zlength(l_src) == un &&
          Zlength(l_vp) == vn &&
          list_within_bound(UINT_MOD, l_src) &&
          list_within_bound(UINT_MOD, l_vp) &&
          UIntArray::undef_full(rp, un + vn) *
          UIntArray::full(up, un, l_src) *
          UIntArray::full(vp, vn, l_vp)
  Ensure exists l_out val_out,
          Zlength(l_out) == un + vn &&
          list_within_bound(UINT_MOD, l_out) &&
          list_to_Z(UINT_MOD, l_out) == val_out &&
          val_out == list_to_Z(UINT_MOD, l_src) * list_to_Z(UINT_MOD, l_vp) &&
          UIntArray::full(rp, un + vn, l_out) *
          UIntArray::full(up, un, l_src) *
          UIntArray::full(vp, vn, l_vp)
*/
{
  unsigned int cy;
  unsigned int vl;
  int i;
  unsigned int *rp_i;

  /*@ Assert
        rp == rp@pre &&
        up == up@pre &&
        vp == vp@pre &&
        un == un@pre &&
        vn == vn@pre &&
        un@pre > 0 &&
        vn@pre > 0 &&
        vn@pre <= un@pre &&
        un@pre + vn@pre <= INT_MAX &&
        Zlength(l_src) == un@pre &&
        Zlength(l_vp) == vn@pre &&
        list_within_bound(UINT_MOD, l_src) &&
        list_within_bound(UINT_MOD, l_vp) &&
        0 <= l_vp[0] &&
        l_vp[0] <= UINT_MAX &&
        has_permission(&cy) *
        has_permission(&vl) *
        has_permission(&i) *
        has_permission(&rp_i) *
        UIntArray::undef_full(rp@pre, un@pre) *
        UIntArray::undef_seg(rp@pre, un@pre, un@pre + vn@pre) *
        UIntArray::full(up@pre, un@pre, l_src) *
        UIntArray::full(vp@pre, vn@pre, l_vp)
  */
  vl = vp[0];
  cy = mpn_mul_1(rp, up, un, vl) /*@ where l = l_src */;
  rp[un] = cy;
  i = 1;
  /*@ Inv Assert
        exists l_done,
          rp == rp@pre &&
          up == up@pre &&
          vp == vp@pre &&
          un == un@pre &&
          vn == vn@pre &&
          un@pre > 0 &&
          vn@pre > 0 &&
          vn@pre <= un@pre &&
          un@pre <= INT_MAX &&
          un@pre + vn@pre <= INT_MAX &&
          1 <= i &&
          i <= vn@pre &&
          0 <= cy &&
          cy <= UINT_MAX &&
          Zlength(l_done) == un@pre + i &&
          Zlength(l_src) == un@pre &&
          Zlength(l_vp) == vn@pre &&
          list_within_bound(UINT_MOD, l_done) &&
          list_within_bound(UINT_MOD, l_src) &&
          list_within_bound(UINT_MOD, l_vp) &&
          list_to_Z(UINT_MOD, l_done) ==
            list_to_Z(UINT_MOD, l_src) *
            list_to_Z(UINT_MOD, sublist(0, i, l_vp)) &&
          has_permission(&vl) *
          has_permission(&rp_i) *
          UIntArray::seg(rp@pre, 0, un@pre + i, l_done) *
          UIntArray::undef_seg(rp@pre, un@pre + i, un@pre + vn@pre) *
          UIntArray::full(up@pre, un@pre, l_src) *
          UIntArray::full(vp@pre, vn@pre, l_vp)
  */
  while (i < vn) {
    /*@ Assert
        exists l_done l_low l_mid,
          rp == rp@pre &&
          up == up@pre &&
          vp == vp@pre &&
          un == un@pre &&
          vn == vn@pre &&
          un@pre > 0 &&
          vn@pre > 0 &&
          vn@pre <= un@pre &&
          un@pre <= INT_MAX &&
          un@pre + vn@pre <= INT_MAX &&
          1 <= i &&
          i < vn@pre &&
          0 <= cy &&
          cy <= UINT_MAX &&
          Zlength(l_low) == i &&
          Zlength(l_mid) == un@pre &&
          l_done == app(l_low, l_mid) &&
          Zlength(l_done) == un@pre + i &&
          Zlength(l_src) == un@pre &&
          Zlength(l_vp) == vn@pre &&
          list_within_bound(UINT_MOD, l_done) &&
          list_within_bound(UINT_MOD, l_low) &&
          list_within_bound(UINT_MOD, l_mid) &&
          list_within_bound(UINT_MOD, l_src) &&
          list_within_bound(UINT_MOD, l_vp) &&
          list_to_Z(UINT_MOD, l_done) ==
            list_to_Z(UINT_MOD, l_src) *
            list_to_Z(UINT_MOD, sublist(0, i, l_vp)) &&
          has_permission(&vl) *
          has_permission(&rp_i) *
          UIntArray::seg(rp@pre, 0, i, l_low) *
          UIntArray::seg(rp@pre, i, i + un@pre, l_mid) *
          UIntArray::undef_seg(rp@pre, i + un@pre, un@pre + vn@pre) *
          UIntArray::full(up@pre, un@pre, l_src) *
          UIntArray::full(vp@pre, vn@pre, l_vp)
    */
    vl = vp[i];
    rp_i = rp + i;
    /*@ Assert
        exists l_done l_low l_mid,
          rp == rp@pre &&
          up == up@pre &&
          vp == vp@pre &&
          un == un@pre &&
          vn == vn@pre &&
          un > 0 &&
          vn > 0 &&
          vn <= un &&
          un <= INT_MAX &&
          un + vn <= INT_MAX &&
          1 <= i &&
          i < vn &&
          0 <= cy &&
          cy <= UINT_MAX &&
          0 <= vl &&
          vl <= UINT_MAX &&
          Zlength(l_low) == i &&
          Zlength(l_mid) == un &&
          l_done == app(l_low, l_mid) &&
          Zlength(l_done) == un + i &&
          Zlength(l_src) == un &&
          Zlength(l_vp) == vn &&
          list_within_bound(UINT_MOD, l_done) &&
          list_within_bound(UINT_MOD, l_low) &&
          list_within_bound(UINT_MOD, l_mid) &&
          list_within_bound(UINT_MOD, l_src) &&
          list_within_bound(UINT_MOD, l_vp) &&
          list_to_Z(UINT_MOD, l_done) ==
            list_to_Z(UINT_MOD, l_src) *
            list_to_Z(UINT_MOD, sublist(0, i, l_vp)) &&
          rp_i == rp + i * sizeof(unsigned int) &&
          (vl == l_vp[i]) *
          UIntArray::seg(rp, 0, i, l_low) *
          UIntArray::full(rp_i, un, l_mid) *
          UIntArray::undef_seg(rp, i + un, un + vn) *
          UIntArray::full(up, un, l_src) *
          UIntArray::full(vp, vn, l_vp)
    */
    /*@ Given l_done l_low l_mid */
    cy = mpn_addmul_1(rp_i, up, un, vl)
      /*@ where l_rp = l_mid, l_up = l_src */;
    rp[i + un] = cy;
    i = i + 1;
  }
  return cy;
}
