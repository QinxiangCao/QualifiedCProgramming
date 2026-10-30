#include "gmp/minigmp/gmp_def.h"

int mpz_abs_add(mpz_ptr r, mpz_srcptr a, mpz_srcptr b)
/*@ non_alias
  With n m l
  Require
    store_Z(a, n) * store_Z(b, m) * store_Z(r, l)
  Ensure
    store_Z(a, n) * store_Z(b, m) *
    store_Z_remain_size(r, Zabs(n) + Zabs(m), __return)
*/
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

int mpz_abs_sub(mpz_ptr r, mpz_srcptr a, mpz_srcptr b)
/*@ non_alias
  With n m l
  Require
    store_Z(a, n) * store_Z(b, m) * store_Z(r, l)
  Ensure
    store_Z(a, n) * store_Z(b, m) *
    store_Z_remain_size(r, Zabs(n) - Zabs(m), __return)
*/
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
/*@ nonalias
  With n m l
  Require
    store_Z(a, n) * store_Z(b, m) * store_Z(r, l)
  Ensure
    store_Z(a, n) * store_Z(b, m) * store_Z(r, n + m)
*/
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
    rn = mpz_abs_add(r, a, b) /*@ where (non_alias) $ nonalias
        where (r_eq_a) $ r_eq_a */;
    /*@ Assert
      exists ptr old_size cap bptr bsize bcap rn_v,
      r == r@pre && a == a@pre && b == b@pre && r@pre == a@pre &&
      0 <= cap && cap <= INT_MAX &&
      Zabs(rn_v) <= cap &&
      Zabs(bsize) <= bcap &&
      (old_size ^ bsize) >= 0 &&
      same_sign(Zabs(za_r_eq_a) + Zabs(zb_r_eq_a), rn_v) &&
      same_sign(za_r_eq_a, old_size) &&
      same_sign(zb_r_eq_a, bsize) &&
      store(&rn, rn_v) *
      store(&(a->_mp_size), old_size) *
      store(&(a->_mp_alloc), cap) *
      store(&(a->_mp_d), unsigned int *, ptr) *
      mpd_store_Z_compact(UINT_MOD, ptr, Zabs(za_r_eq_a) + Zabs(zb_r_eq_a), Zabs(rn_v)) *
      UIntArray::undef_seg(ptr, Zabs(rn_v), cap) *
      store(&(b->_mp_size), bsize) *
      store(&(b->_mp_alloc), bcap) *
      store(&(b->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb_r_eq_a), Zabs(bsize)) *
      UIntArray::undef_seg(bptr, Zabs(bsize), bcap)
    $ r_eq_a */
  } else {
    rn = mpz_abs_sub(r, a, b) /*@ where (non_alias) $ nonalias
        where (r_eq_a) $ r_eq_a */;
    /*@ Assert
      exists ptr old_size cap bptr bsize bcap rn_v,
      r == r@pre && a == a@pre && b == b@pre && r@pre == a@pre &&
      0 <= cap && cap <= INT_MAX &&
      Zabs(rn_v) <= cap &&
      Zabs(bsize) <= bcap &&
      (old_size ^ bsize) < 0 &&
      same_sign(Zabs(za_r_eq_a) - Zabs(zb_r_eq_a), rn_v) &&
      same_sign(za_r_eq_a, old_size) &&
      same_sign(zb_r_eq_a, bsize) &&
      store(&rn, rn_v) *
      store(&(a->_mp_size), old_size) *
      store(&(a->_mp_alloc), cap) *
      store(&(a->_mp_d), unsigned int *, ptr) *
      mpd_store_Z_compact(UINT_MOD, ptr, Zabs(Zabs(za_r_eq_a) - Zabs(zb_r_eq_a)), Zabs(rn_v)) *
      UIntArray::undef_seg(ptr, Zabs(rn_v), cap) *
      store(&(b->_mp_size), bsize) *
      store(&(b->_mp_alloc), bcap) *
      store(&(b->_mp_d), unsigned int *, bptr) *
      mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb_r_eq_a), Zabs(bsize)) *
      UIntArray::undef_seg(bptr, Zabs(bsize), bcap)
    $ r_eq_a */
  }

  r->_mp_size = a->_mp_size >= 0 ? rn : -rn;
}
