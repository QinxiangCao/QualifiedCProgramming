#include "fme_ge_gmp/gmp/gmp_def.h"

void gmp_umul_ppmm(unsigned int *w0, unsigned int *w1,
                   unsigned int u, unsigned int v)
/*@ Require has_uint_permission(w0) *
            has_uint_permission(w1) 
    Ensure exists w0_value w1_value,
             w1_value * UINT_MOD + w0_value == u * v &&
             store_uint(w0, w0_value) *
             store_uint(w1, w1_value) */;

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
*/
{
  unsigned int ul;
  unsigned int cl;
  unsigned int hpl;
  unsigned int lpl;
  unsigned int rl;
  int i;

  i = 0;
  cl = 0;
  /*@ Inv Assert
        exists l_done,
          rp == rp@pre &&
          up == up@pre &&
          n == n@pre &&
          vl == vl@pre &&
          0 <= vl@pre &&
          vl@pre <= UINT_MAX &&
          0 <= i &&
          i <= n@pre &&
          0 <= cl &&
          cl <= UINT_MAX &&
          Zlength(l_done) == i &&
          Zlength(l_rp) == n@pre &&
          Zlength(l_up) == n@pre &&
          list_within_bound(UINT_MOD, l_done) &&
          list_within_bound(UINT_MOD, l_rp) &&
          list_within_bound(UINT_MOD, l_up) &&
          list_to_Z(UINT_MOD, l_done) + cl * Z::pow(UINT_MOD, i) ==
            list_to_Z(UINT_MOD, sublist(0, i, l_rp)) +
            list_to_Z(UINT_MOD, sublist(0, i, l_up)) * vl@pre &&
          has_uint_permission(&ul) *
          has_uint_permission(&lpl) *
          has_uint_permission(&hpl) *
          has_uint_permission(&rl) *
          UIntArray::seg(rp@pre, 0, i, l_done) *
          UIntArray::seg(rp@pre, i, n@pre, sublist(i, n@pre, l_rp)) *
          UIntArray::full(up@pre, n@pre, l_up)
  */
  while (i < n) {
    ul = up[i];
    gmp_umul_ppmm(&lpl, &hpl, ul, vl);
    /*@ 0 <= lpl && lpl <= UINT_MAX by local */
    /*@ 0 <= hpl && hpl <= UINT_MAX by local */
    /*@ Assert
          exists l_done,
            rp == rp@pre &&
            up == up@pre &&
            n == n@pre &&
            vl == vl@pre &&
            0 <= vl@pre &&
            vl@pre <= UINT_MAX &&
            0 <= i &&
            i < n@pre &&
            0 <= cl &&
            cl <= UINT_MAX &&
            0 <= lpl &&
            lpl <= UINT_MAX &&
            0 <= hpl &&
            hpl <= UINT_MAX &&
            Zlength(l_done) == i &&
            Zlength(l_rp) == n@pre &&
            Zlength(l_up) == n@pre &&
            list_within_bound(UINT_MOD, l_done) &&
            list_within_bound(UINT_MOD, l_rp) &&
            list_within_bound(UINT_MOD, l_up) &&
            list_to_Z(UINT_MOD, l_done) + cl * Z::pow(UINT_MOD, i) ==
              list_to_Z(UINT_MOD, sublist(0, i, l_rp)) +
              list_to_Z(UINT_MOD, sublist(0, i, l_up)) * vl@pre &&
            hpl * UINT_MOD + lpl == Znth(i, l_up, 0) * vl@pre &&
            store_uint(&ul, Znth(i, l_up, 0)) *
            has_uint_permission(&rl) *
            UIntArray::seg(rp@pre, 0, i, l_done) *
            UIntArray::seg(rp@pre, i, n@pre, sublist(i, n@pre, l_rp)) *
            UIntArray::full(up@pre, n@pre, l_up)
    */
    lpl = lpl + cl;
    cl = (lpl < cl) + hpl;
    rl = rp[i];
    lpl = rl + lpl;
    cl = cl + (lpl < rl);
    rp[i] = lpl;
    i = i + 1;
  }
  return cl;
}
