#include "fme_ge_gmp/gmp/gmp_def.h"

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
*/;

void mpz_add(mpz_ptr r, mpz_srcptr a, mpz_srcptr b)
/*@ r_eq_a
  With
    za zb
  Require
    r == a && store_Z(a, za) * store_Z(b, zb)
  Ensure
    store_Z(a, za + zb) * store_Z(b, zb)
*/
{
  int rn;

  if ((a->_mp_size ^ b->_mp_size) >= 0) {
    rn = mpz_abs_add(r, a, b) /*@ where (r_eq_a) */;
    /*@ Assert
      exists ptr old_size cap bptr bsize bcap rn_v,
      r == r@pre && a == a@pre && b == b@pre && r@pre == a@pre &&
      0 <= cap && cap <= INT_MAX &&
      Zabs(rn_v) <= cap &&
      Zabs(bsize) <= bcap &&
      (old_size ^ bsize) >= 0 &&
      same_sign(Zabs(za) + Zabs(zb), rn_v) &&
      same_sign(za, old_size) &&
      same_sign(zb, bsize) &&
      store(&rn, rn_v) *
      store(&(a->_mp_size), old_size) *
      store(&(a->_mp_alloc), cap) *
      store(&(a->_mp_d), unsigned int *, ptr) *
      mpd_store_Z_compact(UINT_MOD, ptr, Zabs(za) + Zabs(zb), Zabs(rn_v)) *
      UIntArray::undef_seg(ptr, Zabs(rn_v), cap) *
      store(&(b->_mp_size), bsize) *
      store(&(b->_mp_alloc), bcap) *
      store(&(b->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb), Zabs(bsize)) *
      UIntArray::undef_seg(bptr, Zabs(bsize), bcap)
    */
  } else {
    rn = mpz_abs_sub(r, a, b) /*@ where (r_eq_a) */;
    /*@ Assert
      exists ptr old_size cap bptr bsize bcap rn_v,
      r == r@pre && a == a@pre && b == b@pre && r@pre == a@pre &&
      0 <= cap && cap <= INT_MAX &&
      Zabs(rn_v) <= cap &&
      Zabs(bsize) <= bcap &&
      (old_size ^ bsize) < 0 &&
      same_sign(Zabs(za) - Zabs(zb), rn_v) &&
      same_sign(za, old_size) &&
      same_sign(zb, bsize) &&
      store(&rn, rn_v) *
      store(&(a->_mp_size), old_size) *
      store(&(a->_mp_alloc), cap) *
      store(&(a->_mp_d), unsigned int *, ptr) *
      mpd_store_Z_compact(UINT_MOD, ptr, Zabs(Zabs(za) - Zabs(zb)), Zabs(rn_v)) *
      UIntArray::undef_seg(ptr, Zabs(rn_v), cap) *
      store(&(b->_mp_size), bsize) *
      store(&(b->_mp_alloc), bcap) *
      store(&(b->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb), Zabs(bsize)) *
      UIntArray::undef_seg(bptr, Zabs(bsize), bcap)
    */
  }

  r->_mp_size = a->_mp_size >= 0 ? rn : -rn;
}
