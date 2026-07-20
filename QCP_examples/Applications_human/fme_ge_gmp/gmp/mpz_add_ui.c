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

void mpz_init_set_ui(mpz_t r, unsigned long x)
/*@
  With x0
  Require
    x == x0 &&
    0 <= x0 &&
    undef_data_at(&(r->_mp_alloc)) *
    undef_data_at(&(r->_mp_size)) *
    undef_data_at(&(r->_mp_d))
  Ensure
    store_Z(r, x0)
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

void mpz_add(mpz_ptr r, mpz_srcptr a, mpz_srcptr b)
/*@ r_eq_a
  With
    za zb
  Require
    r == a && store_Z(a, za) * store_Z(b, zb)
  Ensure
    store_Z(a, za + zb) * store_Z(b, zb)
*/;

void mpz_add_ui(mpz_t r, const mpz_t a, unsigned long b)
/*@ r_eq_a
  With za b0
  Require r == a && b == b0 && 0 <= b0 && store_Z(a, za)
  Ensure store_Z(a, za + b0)
*/
{
  mpz_ptr bb;
  bb = malloc_mpz_struct();
  mpz_init_set_ui(bb, b) /*@ where x0 = b0 */;
  mpz_add(r, a, bb) /*@ where (r_eq_a) za = za, zb = b0 */;
  mpz_clear(bb);
  free_mpz_struct(bb);
}
