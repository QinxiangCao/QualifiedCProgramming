#include "fme_ge_gmp/gmp/gmp_def.h"

int gmp_abs(int x)
/*@
  Require INT_MIN < x && x <= INT_MAX
  Ensure __return == Zabs(x)
*/;

void int_swap(int *x, int *y)
/*@
  With
    px py
  Require
    *x == px && *y == py
  Ensure
    *x == py && *y == px
*/;

void mpz_srcptr_swap(mpz_srcptr *x, mpz_srcptr *y)
/*@
  With
    px py
  Require
    *x == px && *y == py
  Ensure
    *x == py && *y == px
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

unsigned int mpn_add(unsigned int *rp, unsigned int *ap, int an,
                     unsigned int *bp, int bn)
/*@ rp_eq_ap
  With
    val_a val_b
  Require
    rp == ap && an >= bn && an >= 0 && bn >= 0 &&
    mpd_store_Z(UINT_MOD, ap, val_a, an) *
    mpd_store_Z(UINT_MOD, bp, val_b, bn)
  Ensure exists val_r_out,
    val_r_out + __return * Z::pow(UINT_MOD, an) == val_a + val_b &&
    rp == ap &&
    mpd_store_Z(UINT_MOD, ap, val_r_out, an) *
    mpd_store_Z(UINT_MOD, bp, val_b, bn)
*/
/*@ rp_eq_bp
  With
    val_a val_b
  Require
    rp == bp && an >= bn && an >= 0 && bn >= 0 &&
    mpd_store_Z(UINT_MOD, ap, val_a, an) *
    mpd_store_Z(UINT_MOD, bp, val_b, bn) *
    UIntArray::undef_seg(rp, bn, an)
  Ensure exists val_r_out,
    val_r_out + __return * Z::pow(UINT_MOD, an) == val_a + val_b &&
    rp == bp &&
    mpd_store_Z(UINT_MOD, ap, val_a, an) *
    mpd_store_Z(UINT_MOD, rp, val_r_out, an)
*/;

static int mpz_abs_add(mpz_ptr r, mpz_srcptr a, mpz_srcptr b)
/*@ r_eq_a
  With
    za zb
  Require
    r == a &&
    store_Z(a, za) * store_Z(b, zb)
  Ensure
    store_Z_with_old_size(a, za, Zabs(za) + Zabs(zb), __return) *
    store_Z(b, zb)
*/
{
  int an;
  int bn;
  unsigned int *rp;
  unsigned int cy;

  /*@ Assert
      exists rptr rsize rcap bptr bsize bcap,
      r@pre == a@pre &&
      INT_MIN < rsize && rsize <= INT_MAX &&
      INT_MIN < bsize && bsize <= INT_MAX &&
      0 <= rcap && rcap <= INT_MAX &&
      0 <= bcap && bcap <= INT_MAX &&
      Zabs(rsize) <= rcap && same_sign(za, rsize) &&
      Zabs(bsize) <= bcap && same_sign(zb, bsize) &&
      has_permission(&cy) *
      has_permission(&rp) *
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

  if (an < bn) {
    mpz_srcptr_swap(&a, &b);
    int_swap(&an, &bn);
  }

  rp = mrz_realloc_if(r, an + 1);
  /*@ Branch name
      rp_eq_ap: a == r;
      rp_eq_bp: b == r
  */
  /*@ Assert
      exists rptr_new rcap_new,
      a == r &&
      b == b@pre &&
      r == r@pre &&
      r@pre == a@pre &&
      an >= bn &&
      an == Zabs(rsize) &&
      bn == Zabs(bsize) &&
      same_sign(za, rsize) &&
      same_sign(zb, bsize) &&
      Zabs(rsize) <= rcap_new &&
      Zabs(bsize) <= bcap &&
      0 <= rcap_new &&
      rcap_new <= INT_MAX &&
      an < rcap_new &&
      rp == rptr_new &&
      has_permission(&cy) *
      store(&(r->_mp_size), rsize) *
      store(&(r->_mp_alloc), rcap_new) *
      store(&(r->_mp_d), unsigned int *, rptr_new) *
      mpd_store_Z_compact(UINT_MOD, rptr_new, Zabs(za), an) *
      UIntArray::undef_seg(rptr_new, an, rcap_new) *
      store(&(b->_mp_size), bsize) *
      store(&(b->_mp_alloc), bcap) *
      store(&(b->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb), bn) *
      UIntArray::undef_seg(bptr, bn, bcap)
      $ rp_eq_ap
  */
  /*@ Assert
      exists rptr_new rcap_new,
      b == r &&
      a == b@pre &&
      r == r@pre &&
      r@pre == a@pre &&
      bn < an &&
      an == Zabs(bsize) &&
      bn == Zabs(rsize) &&
      same_sign(zb, bsize) &&
      same_sign(za, rsize) &&
      Zabs(bsize) <= bcap &&
      Zabs(rsize) <= rcap_new &&
      0 <= rcap_new &&
      rcap_new <= INT_MAX &&
      an < rcap_new &&
      bn <= rcap_new &&
      rp == rptr_new &&
      has_permission(&cy) *
      store(&(a->_mp_size), bsize) *
      store(&(a->_mp_alloc), bcap) *
      store(&(a->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb), an) *
      UIntArray::undef_seg(bptr, an, bcap) *
      store(&(b->_mp_size), rsize) *
      store(&(b->_mp_alloc), rcap_new) *
      store(&(b->_mp_d), unsigned int *, rptr_new) *
      mpd_store_Z_compact(UINT_MOD, rptr_new, Zabs(za), bn) *
      UIntArray::undef_seg(rptr_new, bn, an) *
      UIntArray::undef_seg(rptr_new, an, rcap_new)
      $ rp_eq_bp
  */
  /*@ Branch name
      rp_eq_ap: a == r;
      rp_eq_bp: b == r
  */
  cy = mpn_add(rp, a->_mp_d, an, b->_mp_d, bn)
    /*@ where (rp_eq_ap) val_a = Zabs(za), val_b = Zabs(zb) $ rp_eq_ap
        where (rp_eq_bp) val_a = Zabs(zb), val_b = Zabs(za) $ rp_eq_bp */;
  /*@ 0 <= cy && cy <= UINT_MAX by local */
  /*@ Assert
      exists rptr_new rcap_new val_r_out,
      a == r &&
      b == b@pre &&
      r == r@pre &&
      r@pre == a@pre &&
      an >= bn &&
      an == Zabs(rsize) &&
      bn == Zabs(bsize) &&
      same_sign(za, rsize) &&
      same_sign(zb, bsize) &&
      Zabs(rsize) <= rcap_new &&
      Zabs(bsize) <= bcap &&
      0 <= rcap_new &&
      rcap_new <= INT_MAX &&
      an < rcap_new &&
      rp == rptr_new &&
      0 <= cy && cy <= 1 &&
      val_r_out + cy * Z::pow(UINT_MOD, an) == Zabs(za) + Zabs(zb) &&
      (cy == 0 && is_compact_Z(UINT_MOD, val_r_out, an) ||
       cy == 1 && is_compact_Z(UINT_MOD, val_r_out + Z::pow(UINT_MOD, an), an + 1)) &&
      store(&(r->_mp_size), rsize) *
      store(&(r->_mp_alloc), rcap_new) *
      store(&(r->_mp_d), unsigned int *, rptr_new) *
      mpd_store_Z(UINT_MOD, rptr_new, val_r_out, an) *
      UIntArray::undef_seg(rptr_new, an, rcap_new) *
      store(&(b->_mp_size), bsize) *
      store(&(b->_mp_alloc), bcap) *
      store(&(b->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb), bn) *
      UIntArray::undef_seg(bptr, bn, bcap)
      $ rp_eq_ap
  */
  /*@ Assert
      exists rptr_new rcap_new val_r_out,
      b == r &&
      a == b@pre &&
      r == r@pre &&
      r@pre == a@pre &&
      bn < an &&
      an == Zabs(bsize) &&
      bn == Zabs(rsize) &&
      same_sign(zb, bsize) &&
      same_sign(za, rsize) &&
      Zabs(bsize) <= bcap &&
      Zabs(rsize) <= rcap_new &&
      0 <= rcap_new &&
      rcap_new <= INT_MAX &&
      an < rcap_new &&
      bn <= rcap_new &&
      rp == rptr_new &&
      0 <= cy && cy <= 1 &&
      val_r_out + cy * Z::pow(UINT_MOD, an) == Zabs(za) + Zabs(zb) &&
      (cy == 0 && is_compact_Z(UINT_MOD, val_r_out, an) ||
       cy == 1 && is_compact_Z(UINT_MOD, val_r_out + Z::pow(UINT_MOD, an), an + 1)) &&
      store(&(a->_mp_size), bsize) *
      store(&(a->_mp_alloc), bcap) *
      store(&(a->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb), an) *
      UIntArray::undef_seg(bptr, an, bcap) *
      store(&(b->_mp_size), rsize) *
      store(&(b->_mp_alloc), rcap_new) *
      store(&(b->_mp_d), unsigned int *, rptr_new) *
      mpd_store_Z(UINT_MOD, rptr_new, val_r_out, an) *
      UIntArray::undef_seg(rptr_new, an, rcap_new)
      $ rp_eq_bp
  */
  rp[an] = cy;
  return an + cy;
}
