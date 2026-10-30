#include "gmp/minigmp/gmp_def.h"
/*@ Import Coq Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_base_lib */

void
gmp_free_limbs (unsigned int *old, int size)
/*@
  With
    n len
  Require
    mpd_store_Z_compact(UINT_MOD,old, n, len) *
    UIntArray::undef_seg(old, len, size)
  Ensure
    emp
*/
;

int gmp_cmp(int a, int b)
/*@
  Require emp
  Ensure 
    emp * 
    (a > b && __return == 1 || 
    a == b && __return == 0 ||
    a < b && __return == -1)
*/;

void gmp_umul_ppmm (unsigned int * w0, unsigned int * w1, unsigned int u, unsigned int v)
/*@ Require has_uint_permission(w0) *
            has_uint_permission(w1) 
    Ensure exists w0_value w1_value,
             w1_value * UINT_MOD + w0_value == u * v &&
             store_uint(w0, w0_value) *
             store_uint(w1, w1_value) */;

int gmp_abs(int x)
/*@
  Require INT_MIN < x && x <= INT_MAX
  Ensure __return == Zabs(x)
*/
{
  return x >= 0 ? x : -x;
}

int gmp_max(int a, int b)
/*@
  Require emp
  Ensure __return == Z::max(a, b)
*/
{
  return a > b ? a : b;
}

int gmp_cmp(int a, int b)
/*@ default */
{
  return (a > b) - (a < b);
}

int
mpn_cmp (unsigned int *ap, unsigned int *bp, int n)
/*@
  With val1 val2
  Require
    0 <= n &&
    mpd_store_Z_compact(UINT_MOD, ap, val1, n) *
    mpd_store_Z_compact(UINT_MOD, bp, val2, n)  
  Ensure
    (val1 > val2 && __return == 1 ||
    val1 == val2 && __return == 0 ||
    val1 < val2 && __return == -1) &&
    mpd_store_Z_compact(UINT_MOD, ap, val1, n) *
    mpd_store_Z_compact(UINT_MOD, bp, val2, n)
*/
{
  /*@
    mpd_store_Z_compact(UINT_MOD, ap, val1, n) * mpd_store_Z_compact(UINT_MOD, bp, val2, n)
    which implies
    exists l1 l2,
    list_to_Z(UINT_MOD, l1) == val1 && last(l1, 1) >= 1 && list_within_bound(UINT_MOD, l1) &&
    list_to_Z(UINT_MOD, l2) == val2 && last(l2, 1) >= 1 && list_within_bound(UINT_MOD, l2) &&
    n == Zlength(l1) && n == Zlength(l2) && 
    UIntArray::full(ap, n, l1) * UIntArray::full(bp, n, l2) 
  */
  /*@
    Given l1 l2
  */
  --n;
  /*@ Inv Assert
    ap == ap@pre && bp == bp@pre &&
    -1 <= n && n < n@pre &&
    sublist(n + 1, n@pre, l1) == sublist(n + 1, n@pre, l2) &&
    list_to_Z(UINT_MOD, l1) == val1 && last(l1, 1) >= 1 && list_within_bound(UINT_MOD, l1) &&
    list_to_Z(UINT_MOD, l2) == val2 && last(l2, 1) >= 1 && list_within_bound(UINT_MOD, l2) &&
    UIntArray::full(ap, n@pre, l1) * UIntArray::full(bp, n@pre, l2)
  */
  while (n >= 0)
    {
      if (ap[n] != bp[n])
	      return ap[n] > bp[n] ? 1 : -1;
      --n;
    }
  // Note: The parser cannot parse "--n" in loop condition so we paraphrased it.
  /*
  while (--n >= 0)
    {
      if (ap[n] != bp[n])
	return ap[n] > bp[n] ? 1 : -1;
    }
  */
  return 0;
}

int
mpn_cmp4 (unsigned int *ap, int an, unsigned int *bp, int bn)
/*@
  With val1 val2
  Require
    an >= 0 && bn >= 0 && 
    mpd_store_Z_compact(UINT_MOD, ap, val1, an) *
    mpd_store_Z_compact(UINT_MOD, bp, val2, bn)
  Ensure
    (val1 > val2 && __return == 1 ||
    val1 == val2 && __return == 0 ||
    val1 < val2 && __return == -1) &&
    mpd_store_Z_compact(UINT_MOD, ap, val1, an) *
    mpd_store_Z_compact(UINT_MOD, bp, val2, bn)
*/
{
  if (an != bn)
    return an < bn ? -1 : 1;
  else {
    return mpn_cmp (ap, bp, an);
  }
}

void gmp_umul_ppmm (unsigned int * w0, unsigned int * w1, unsigned int u, unsigned int v)
/*@ default */
{
      unsigned int __x0, __x1, __x2, __x3;
      unsigned __ul, __vl, __uh, __vh;
      unsigned int __u = (u), __v = (v);
      /*@ 0 <= u && u <= UINT_MAX by local */
      /*@ 0 <= v && v <= UINT_MAX by local */
      __ul = __u & 65535;
      __uh = __u >> 16;
      __vl = __v & 65535;
      __vh = __v >> 16;

      __x0 = (unsigned int) __ul * __vl;
      __x1 = (unsigned int) __ul * __vh;
      __x2 = (unsigned int) __uh * __vl;
      __x3 = (unsigned int) __uh * __vh;

      __x1 += __x0 >> 16; /* this can't give carry */
      __x1 += __x2; /* but this indeed can */
      if (__x1 < __x2)/* did we get it? */
        __x3 += 65536;	/* yes, add it in the proper pos. */
      * w1 = __x3 + (__x1 >> 16);
      * w0 = (__x1 << 16) + (__x0 & 65535);
}

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
*/
{
  unsigned int ul, cl, hpl, lpl;
  int i;
  i = 0;
  cl = 0;
  /*@
    Inv Assert
      exists l_rp,
      rp == rp@pre && up == up@pre && n == n@pre && vl == vl@pre &&
      0 < n && n <= INT_MAX && 0 <= vl && vl <= UINT_MAX &&
      0 <= i && i <= n &&
      0 <= cl && cl <= UINT_MAX &&
      list_within_bound(UINT_MOD, l) &&
      list_within_bound(UINT_MOD, l_rp) &&
      (list_to_Z(UINT_MOD, l_rp) + cl * Z::pow(UINT_MOD, i) == list_to_Z(UINT_MOD, sublist(0, i, l)) * vl) &&
      has_uint_permission(&ul) * has_uint_permission(&lpl) * has_uint_permission(&hpl) *
      UIntArray::full(up, n, l) *
      UIntArray::seg(rp, 0, i, l_rp) *
      UIntArray::undef_seg(rp, i, n)
  */
  while (i < n)
    {
      ul = up[i];
      gmp_umul_ppmm (&lpl, &hpl, ul, vl);
      /*@ 0 <= lpl && lpl <= UINT_MAX by local */
      /*@ 0 <= hpl && hpl <= UINT_MAX by local */
      /*@ Assert
            exists l_rp,
            rp == rp@pre && up == up@pre &&
            n == n@pre && vl == vl@pre &&
            0 <= i && i < n &&
            0 <= cl && cl <= UINT_MAX &&
            0 <= lpl && lpl <= UINT_MAX &&
            0 <= hpl && hpl <= UINT_MAX &&
            list_within_bound(UINT_MOD, l_rp) &&
            (list_to_Z(UINT_MOD, l_rp) + cl * Z::pow(UINT_MOD, i) == list_to_Z(UINT_MOD, sublist(0, i, l)) * vl) &&
            (hpl * UINT_MOD + lpl == l[i] * vl) &&
            n > 0 && n <= INT_MAX &&
            0 <= vl && vl <= UINT_MAX &&
            list_within_bound(UINT_MOD, l) &&
            store_uint(&ul, l[i]) *
            UIntArray::full(up, n, l) *
            UIntArray::seg(rp, 0, i, l_rp) *
            UIntArray::undef_seg(rp, i, n)
       */
      lpl += cl;
      cl = (lpl < cl) + hpl;
      rp[i] = lpl;
      i = i + 1;
    }
  return cl;
}

void
mpz_clear (mpz_ptr r)
/*@
  With
    n
  Require
    store_Z(r, n)
  Ensure
    exists size cap ptr,
      r -> _mp_size == size && r -> _mp_alloc == cap && r -> _mp_d == ptr
*/
{
  if (r->_mp_alloc)
    gmp_free_limbs (r->_mp_d, r->_mp_alloc) ;
}

int
mpz_sgn (mpz_srcptr u)
/*@
  With
    n
  Require
    store_Z(u, n)
  Ensure
    store_Z(u, n) &&
    (n > 0 && __return == 1 || n == 0 && __return == 0 ||
      n < 0 && __return == -1)
*/
{
  return gmp_cmp (u->_mp_size, 0);
}
