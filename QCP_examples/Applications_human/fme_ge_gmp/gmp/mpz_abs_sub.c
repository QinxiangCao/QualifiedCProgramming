#include "fme_ge_gmp/gmp/gmp_def.h"

int gmp_abs(int x)
/*@
  Require INT_MIN < x && x <= INT_MAX
  Ensure __return == Zabs(x)
*/;

unsigned int *mrz_realloc_if(mpz_t z,int n)
/*@
  With
    ptr old cap m
  Require
    cap >= 0 && cap <= INT_MAX && n >= 1 && n <= INT_MAX &&
    Zabs(old) <= cap && same_sign(m, old) &&
    mpd_store_Z_compact(UINT_MOD,ptr, Zabs(m), Zabs(old)) * UIntArray::undef_seg(ptr, Zabs(old), cap) &&
      z -> _mp_size == old &&
      z -> _mp_alloc == cap &&
      z -> _mp_d == ptr
  Ensure
    same_sign(m, old) &&
    mpd_store_Z_compact(UINT_MOD,__return, Zabs(m), Zabs(old)) * UIntArray::undef_seg(__return, Zabs(old), Z::max(Z::max(n,1),cap)) &&
    z -> _mp_size == old &&
    z -> _mp_alloc == Z::max(Z::max(n,1),cap) &&
    z -> _mp_d == __return
*/;

int mpn_cmp4(unsigned int *ap, int an, unsigned int *bp, int bn)
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
*/;

unsigned int mpn_sub(unsigned int *rp, unsigned int *ap, int an,
                     unsigned int *bp, int bn)
/*@ rp_eq_ap
  With
    val_a val_b
  Require
    rp == ap && an >= bn && an > 0 && bn >= 0 &&
    an <= INT_MAX && bn <= INT_MAX &&
    mpd_store_Z(UINT_MOD, ap, val_a, an) *
    mpd_store_Z(UINT_MOD, bp, val_b, bn)
  Ensure exists val_r_out,
    val_r_out - __return * Z::pow(UINT_MOD, an) == val_a - val_b &&
    rp == ap &&
    mpd_store_Z(UINT_MOD, ap, val_r_out, an) *
    mpd_store_Z(UINT_MOD, bp, val_b, bn)
*/
/*@ rp_eq_bp
  With
    val_a val_b
  Require
    rp == bp && an >= bn && an > 0 && bn >= 0 &&
    an <= INT_MAX && bn <= INT_MAX &&
    mpd_store_Z(UINT_MOD, ap, val_a, an) *
    mpd_store_Z(UINT_MOD, bp, val_b, bn) *
    UIntArray::undef_seg(rp, bn, an)
  Ensure exists val_r_out,
    val_r_out - __return * Z::pow(UINT_MOD, an) == val_a - val_b &&
    rp == bp &&
    mpd_store_Z(UINT_MOD, ap, val_a, an) *
    mpd_store_Z(UINT_MOD, rp, val_r_out, an)
*/;

int mpn_normalized_size(unsigned int *xp, int n)
/*@
  With val
  Require
    0 <= n && 
    mpd_store_Z(UINT_MOD, xp, val, n) 
  Ensure
    0 <= __return && __return <= n &&
    mpd_store_Z_compact(UINT_MOD, xp, val, __return) * 
    UIntArray::undef_seg(xp, __return, n)
*/;

static int mpz_abs_sub(mpz_ptr r, mpz_srcptr a, mpz_srcptr b)
/*@ r_eq_a
  With
    za zb
  Require
    r == a &&
    store_Z(a, za) * store_Z(b, zb)
  Ensure
    store_Z_with_old_size(a, za, Zabs(za) - Zabs(zb), __return) *
    store_Z(b, zb)
*/
{
  int an;
  int bn;
  int cmp;
  unsigned int *rp;

  /*@ Assert
      exists rptr rsize rcap bptr bsize bcap,
      r@pre == a@pre &&
      INT_MIN < rsize && rsize <= INT_MAX &&
      INT_MIN < bsize && bsize <= INT_MAX &&
      0 <= rcap && rcap <= INT_MAX &&
      0 <= bcap && bcap <= INT_MAX &&
      Zabs(rsize) <= rcap && same_sign(za, rsize) &&
      Zabs(bsize) <= bcap && same_sign(zb, bsize) &&
      has_permission(&rp) *
      has_permission(&cmp) *
      has_permission(&bn) *
      has_permission(&an) *
      store(&r, r@pre) *
      store(&a, a@pre) *
      store(&b, b@pre) *
      store(&(a@pre->_mp_size), rsize) *
      store(&(a@pre->_mp_alloc), rcap) *
      store(&(a@pre->_mp_d), unsigned int *, rptr) *
      mpd_store_Z_compact(UINT_MOD, rptr, Zabs(za), Zabs(rsize)) *
      UIntArray::undef_seg(rptr, Zabs(rsize), rcap) *
      store(&(b@pre->_mp_size), bsize) *
      store(&(b@pre->_mp_alloc), bcap) *
      store(&(b@pre->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb), Zabs(bsize)) *
      UIntArray::undef_seg(bptr, Zabs(bsize), bcap)
  */
  /*@ Given rptr rsize rcap bptr bsize bcap */
  an = gmp_abs(a->_mp_size);
  bn = gmp_abs(b->_mp_size);
  cmp = mpn_cmp4(a->_mp_d, an, b->_mp_d, bn);
  if (cmp > 0) {
    /*@ Assert
      cmp > 0 && Zabs(za) > Zabs(zb) && cmp == 1 &&
      an == Zabs(rsize) && bn == Zabs(bsize) &&
      same_sign(za, rsize) && same_sign(zb, bsize) &&
      Zabs(rsize) <= rcap && 0 <= rcap && rcap <= INT_MAX &&
      Zabs(bsize) <= bcap &&
      r == r@pre && r@pre == a@pre && b == b@pre &&
      has_permission(&rp) *
      store(&a, a@pre) *
      store(&(r->_mp_size), rsize) *
      store(&(r->_mp_alloc), rcap) *
      store(&(r->_mp_d), unsigned int *, rptr) *
      mpd_store_Z_compact(UINT_MOD, rptr, Zabs(za), Zabs(rsize)) *
      UIntArray::undef_seg(rptr, Zabs(rsize), rcap) *
      store(&(b->_mp_size), bsize) *
      store(&(b->_mp_alloc), bcap) *
      store(&(b->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb), bn) *
      UIntArray::undef_seg(bptr, bn, bcap)
    */
    /*@ 1 <= an && an <= INT_MAX by local */
    /*@ 0 <= bn && bn <= INT_MAX by local */
    /*@ 0 <= r->_mp_alloc && r->_mp_alloc <= INT_MAX by local */
    rp = mrz_realloc_if(r, an);
    /*@ Assert
      exists rptr_new rcap_new,
      cmp > 0 && Zabs(za) > Zabs(zb) && cmp == 1 &&
      an == Zabs(rsize) && bn == Zabs(bsize) &&
      same_sign(za, rsize) && same_sign(zb, bsize) &&
      Zabs(rsize) <= rcap_new && 0 <= rcap_new && rcap_new <= INT_MAX &&
      Zabs(bsize) <= bcap &&
      an <= rcap_new &&
      a == r &&
      r == r@pre && r@pre == a@pre && b == b@pre &&
      rp == rptr_new &&
      store(&(a->_mp_size), rsize) *
      store(&(a->_mp_alloc), rcap_new) *
      store(&(a->_mp_d), unsigned int *, rptr_new) *
      mpd_store_Z_compact(UINT_MOD, rptr_new, Zabs(za), an) *
      UIntArray::undef_seg(rptr_new, an, rcap_new) *
      store(&(b->_mp_size), bsize) *
      store(&(b->_mp_alloc), bcap) *
      store(&(b->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb), bn) *
      UIntArray::undef_seg(bptr, bn, bcap)
    */
    mpn_sub(rp, a->_mp_d, an, b->_mp_d, bn)
      /*@ where (rp_eq_ap) val_a = Zabs(za), val_b = Zabs(zb) */;
    return mpn_normalized_size(rp, an);
  } else if (cmp < 0) {
    /*@ Assert
      cmp < 0 && Zabs(za) < Zabs(zb) && cmp == -1 &&
      an == Zabs(rsize) && bn == Zabs(bsize) &&
      same_sign(za, rsize) && same_sign(zb, bsize) &&
      Zabs(rsize) <= rcap && 0 <= rcap && rcap <= INT_MAX &&
      Zabs(bsize) <= bcap &&
      r == r@pre && r@pre == a@pre && b == b@pre &&
      has_permission(&rp) *
      store(&a, a@pre) *
      store(&(r->_mp_size), rsize) *
      store(&(r->_mp_alloc), rcap) *
      store(&(r->_mp_d), unsigned int *, rptr) *
      mpd_store_Z_compact(UINT_MOD, rptr, Zabs(za), Zabs(rsize)) *
      UIntArray::undef_seg(rptr, Zabs(rsize), rcap) *
      store(&(b->_mp_size), bsize) *
      store(&(b->_mp_alloc), bcap) *
      store(&(b->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb), bn) *
      UIntArray::undef_seg(bptr, bn, bcap)
    */
    /*@ 1 <= bn && bn <= INT_MAX by local */
    /*@ 0 <= an && an <= INT_MAX by local */
    /*@ 0 <= r->_mp_alloc && r->_mp_alloc <= INT_MAX by local */
    rp = mrz_realloc_if(r, bn);
    /*@ Assert
      exists rptr_new rcap_new,
      cmp < 0 && Zabs(za) < Zabs(zb) && cmp == -1 &&
      an == Zabs(rsize) && bn == Zabs(bsize) &&
      same_sign(za, rsize) && same_sign(zb, bsize) &&
      Zabs(rsize) <= rcap_new && 0 <= rcap_new && rcap_new <= INT_MAX &&
      Zabs(bsize) <= bcap &&
      bn <= rcap_new &&
      a == r &&
      r == r@pre && r@pre == a@pre && b == b@pre &&
      rp == rptr_new &&
      store(&(a->_mp_size), rsize) *
      store(&(a->_mp_alloc), rcap_new) *
      store(&(a->_mp_d), unsigned int *, rptr_new) *
      mpd_store_Z_compact(UINT_MOD, rptr_new, Zabs(za), an) *
      UIntArray::undef_seg(rptr_new, an, bn) *
      UIntArray::undef_seg(rptr_new, bn, rcap_new) *
      store(&(b->_mp_size), bsize) *
      store(&(b->_mp_alloc), bcap) *
      store(&(b->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb), bn) *
      UIntArray::undef_seg(bptr, bn, bcap)
    */
    mpn_sub(rp, b->_mp_d, bn, a->_mp_d, an)
      /*@ where (rp_eq_bp) val_a = Zabs(zb), val_b = Zabs(za) */;
    return -mpn_normalized_size(rp, bn);
  } else {
    return 0;
  }
}
