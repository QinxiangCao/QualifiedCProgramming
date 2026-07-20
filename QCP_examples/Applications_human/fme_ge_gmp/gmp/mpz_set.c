#include "fme_ge_gmp/gmp/gmp_def.h"

int gmp_abs(int x)
/*@
  Require INT_MIN < x && x <= INT_MAX
  Ensure __return == Zabs(x)
*/;

void mpn_copyi (unsigned int *d, unsigned int *s, int n)
/*@
  With val
  Require
    mpd_store_Z(UINT_MOD, s, val, n) *
    UIntArray::undef_full(d, n)
  Ensure 
    mpd_store_Z(UINT_MOD,s, val, n) *
    mpd_store_Z(UINT_MOD,d, val, n)
*/;

unsigned int *mrz_realloc_if(mpz_t z,int n)
/*@
  With
    ptr old cap m
  Require
    cap >= 0 && cap <= INT_MAX && n >= 0 && n <= INT_MAX &&
    Zabs(old) <= cap && same_sign(m, old) &&
    mpd_store_Z_compact(UINT_MOD,ptr, Zabs(m), Zabs(old)) * UIntArray::undef_seg(ptr, Zabs(old), cap) &&
      z -> _mp_size == old &&
      z -> _mp_alloc == cap &&
      z -> _mp_d == ptr
  Ensure
    same_sign(m, old) &&
    mpd_store_Z_compact(UINT_MOD,__return, Zabs(m), Zabs(old)) * UIntArray::undef_seg(__return, Zabs(old), Z::max(n,cap)) &&
    z -> _mp_size == old &&
    z -> _mp_alloc == Z::max(n,cap) &&
    z -> _mp_d == __return
*/;

void mpz_set(mpz_t rop, const mpz_t op)
/*@ neq
  With old z
  Require store_Z(rop, old) * store_Z(op, z)
  Ensure store_Z(rop, z) * store_Z(op, z)
*/;

void mpz_set(mpz_t rop, const mpz_t op)
/*@ eq
  With z
  Require rop == op && store_Z(op, z)
  Ensure rop == op && store_Z(op, z)
*/;

void mpz_set(mpz_t rop, const mpz_t op)
/*@ eq */
/*@ neq */
{
  /*@ Assert rop == op && rop == rop@pre && op == op@pre &&
              store_Z(op, z_eq) $ eq */
  /*@ Assert rop == rop@pre && op == op@pre &&
              store_Z(rop@pre, old_neq) * store_Z(op@pre, z_neq) $ neq */
  int n;
  unsigned int *rp;

  if (rop != op) {
    n = gmp_abs(op->_mp_size);

    /*@ Assert
        exists optr osize ocap rptr rsize rcap,
          n == Zabs(osize) &&
          n >= 0 &&
          same_sign(z_neq, osize) &&
          Zabs(osize) <= ocap &&
          same_sign(old_neq, rsize) &&
          Zabs(rsize) <= rcap &&
          rcap >= 0 &&
          rop != op &&
          has_permission(&rp) *
          store(&(op->_mp_d), optr) *
          store(&(op->_mp_size), osize) *
          store(&(op->_mp_alloc), ocap) *
          store(&(rop->_mp_d), rptr) *
          store(&(rop->_mp_size), rsize) *
          store(&(rop->_mp_alloc), rcap) *
          mpd_store_Z_compact(UINT_MOD, optr, Zabs(z_neq), n) *
          UIntArray::undef_seg(optr, n, ocap) *
          mpd_store_Z_compact(UINT_MOD, rptr, Zabs(old_neq), Zabs(rsize)) *
          UIntArray::undef_seg(rptr, Zabs(rsize), rcap) *
          (op == op@pre) *
          (rop == rop@pre)
    */
    rp = mrz_realloc_if(rop, n);
    /*@ Assert
        exists optr osize ocap rsize rcap,
          n == Zabs(osize) &&
          n >= 0 &&
          n <= Z::max(n, rcap) &&
          same_sign(z_neq, osize) &&
          Zabs(osize) <= ocap &&
          same_sign(old_neq, rsize) &&
          Zabs(rsize) <= rcap &&
          rcap >= 0 &&
          rop->_mp_size == rsize &&
          rop->_mp_alloc == Z::max(n, rcap) &&
          rop->_mp_d == rp &&
          rop != op &&
          store(&(op->_mp_d), optr) *
          store(&(op->_mp_size), osize) *
          store(&(op->_mp_alloc), ocap) *
          mpd_store_Z_compact(UINT_MOD, optr, Zabs(z_neq), n) *
          UIntArray::undef_seg(optr, n, ocap) *
          UIntArray::undef_full(rp, n) *
          UIntArray::undef_seg(rp, n, Z::max(n, rcap)) *
          (op == op@pre) *
          (rop == rop@pre)
    */
    /*@ Given optr osize ocap rsize rcap */
    mpn_copyi(rp, op->_mp_d, n) /*@ where val=Zabs(z_neq) */;
    /*@ Assert
        exists optr osize ocap rsize rcap,
          n == Zabs(osize) &&
          n >= 0 &&
          n <= Z::max(n, rcap) &&
          same_sign(z_neq, osize) &&
          Zabs(osize) <= ocap &&
          same_sign(old_neq, rsize) &&
          Zabs(rsize) <= rcap &&
          rcap >= 0 &&
          rop->_mp_size == rsize &&
          rop->_mp_alloc == Z::max(n, rcap) &&
          rop->_mp_d == rp &&
          rop != op &&
          store(&(op->_mp_d), optr) *
          store(&(op->_mp_size), osize) *
          store(&(op->_mp_alloc), ocap) *
          mpd_store_Z_compact(UINT_MOD, optr, Zabs(z_neq), n) *
          UIntArray::undef_seg(optr, n, ocap) *
          mpd_store_Z(UINT_MOD, rp, Zabs(z_neq), n) *
          UIntArray::undef_seg(rp, n, Z::max(n, rcap)) *
          (op == op@pre) *
          (rop == rop@pre)
    */
    rop->_mp_size = op->_mp_size;
  }
}
