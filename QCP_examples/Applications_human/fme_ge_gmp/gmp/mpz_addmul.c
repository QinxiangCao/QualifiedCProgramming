#include "fme_ge_gmp/gmp/gmp_def.h"

mpz_ptr malloc_mpz_struct()
  /*@ Require emp
      Ensure __return != 0 &&
             undef_data_at(&(__return->_mp_alloc)) *
             undef_data_at(&(__return->_mp_size)) *
             undef_data_at(&(__return->_mp_d))
    */;

void free_mpz_struct(mpz_ptr x)
  /*@ With size cap ptr
      Require x->_mp_size == size &&
              x->_mp_alloc == cap &&
              x->_mp_d == ptr
      Ensure emp
    */;

void mpz_init(mpz_t x)
/*@
  Require
    undef_data_at(&(x->_mp_alloc)) *
    undef_data_at(&(x->_mp_size)) *
    undef_data_at(&(x->_mp_d))
  Ensure
    store_Z(x, 0)
*/;

void mpz_clear (mpz_t r)
/*@
  With
    n
  Require
    store_Z(r, n)
  Ensure
    exists size cap ptr,
      r -> _mp_size == size && r -> _mp_alloc == cap && r -> _mp_d == ptr
*/;

void mpz_mul(mpz_ptr rop, mpz_srcptr op1, mpz_srcptr op2)
/*@
  With
    old z1 z2
  Require
    store_Z(rop, old) * store_Z(op1, z1) * store_Z(op2, z2)
  Ensure
    store_Z(rop, z1 * z2) * store_Z(op1, z1) * store_Z(op2, z2)
*/;

void mpz_add(mpz_ptr r, mpz_srcptr a, mpz_srcptr b)
/*@ r_eq_a
  With
    za zb
  Require
    r == a && store_Z(a, za) * store_Z(b, zb)
  Ensure
    store_Z(a, za + zb) * store_Z(b, zb)
*/;

void mpz_addmul(mpz_ptr rop, mpz_srcptr op1, mpz_srcptr op2)
/*@
  With
    old z1 z2
  Require
    store_Z(rop, old) * store_Z(op1, z1) * store_Z(op2, z2)
  Ensure
    store_Z(rop, old + z1 * z2) * store_Z(op1, z1) * store_Z(op2, z2)
*/
{
  mpz_ptr t;

  t = malloc_mpz_struct();

  mpz_init(t);

  mpz_mul(t, op1, op2);
  mpz_add(rop, rop, t) /*@ where (r_eq_a) */;

  mpz_clear(t);
  free_mpz_struct(t);
}
