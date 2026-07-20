#include "fme_ge_gmp/gmp/gmp_def.h"

int gmp_abs(int x)
/*@
  Require INT_MIN < x && x <= INT_MAX
  Ensure __return == Zabs(x)
*/;

void mpz_set(mpz_t rop, const mpz_t op)
/*@ neq
  With old z
  Require store_Z(rop, old) * store_Z(op, z)
  Ensure store_Z(rop, z) * store_Z(op, z)
*/
/*@ eq
  With z
  Require rop == op && store_Z(op, z)
  Ensure rop == op && store_Z(op, z)
*/;

void mpz_abs(mpz_t rop, const mpz_t op)
/*@ neq
  With old z
  Require store_Z(rop, old) * store_Z(op, z)
  Ensure store_Z(rop, Zabs(z)) * store_Z(op, z)
*/;

void mpz_abs(mpz_t rop, const mpz_t op)
/*@ eq
  With z
  Require rop == op && store_Z(op, z)
  Ensure rop == op && store_Z(op, Zabs(z))
*/;

void mpz_abs(mpz_t rop, const mpz_t op)
/*@ eq */
/*@ neq */
{
  mpz_set(rop, op) /*@ where (eq) z = z_eq $ eq
                        where (neq) old = old_neq, z = z_neq $ neq */;
  /*@ Assert
      exists ptr size cap,
        rop == op &&
        rop == rop@pre &&
        op == op@pre &&
        same_sign(z_eq, size) &&
        Zabs(size) <= cap &&
        store(&(rop->_mp_d), ptr) *
        store(&(rop->_mp_size), size) *
        store(&(rop->_mp_alloc), cap) *
        mpd_store_Z_compact(UINT_MOD, ptr, Zabs(z_eq), Zabs(size)) *
        UIntArray::undef_seg(ptr, Zabs(size), cap)
      $ eq
  */
  /*@ Assert
      exists rptr rsize rcap optr osize ocap,
        rop == rop@pre &&
        op == op@pre &&
        same_sign(z_neq, rsize) &&
        Zabs(rsize) <= rcap &&
        same_sign(z_neq, osize) &&
        Zabs(osize) <= ocap &&
        store(&(rop->_mp_d), rptr) *
        store(&(rop->_mp_size), rsize) *
        store(&(rop->_mp_alloc), rcap) *
        mpd_store_Z_compact(UINT_MOD, rptr, Zabs(z_neq), Zabs(rsize)) *
        UIntArray::undef_seg(rptr, Zabs(rsize), rcap) *
        store(&(op->_mp_d), optr) *
        store(&(op->_mp_size), osize) *
        store(&(op->_mp_alloc), ocap) *
        mpd_store_Z_compact(UINT_MOD, optr, Zabs(z_neq), Zabs(osize)) *
        UIntArray::undef_seg(optr, Zabs(osize), ocap)
      $ neq
  */
  rop->_mp_size = gmp_abs(rop->_mp_size);
}
