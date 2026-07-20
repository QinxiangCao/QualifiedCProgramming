#include "fme_ge_gmp/gmp/gmp_def.h"

void mpz_init(mpz_t x)
/*@
  Require
    undef_data_at(&(x->_mp_alloc)) *
    undef_data_at(&(x->_mp_size)) *
    undef_data_at(&(x->_mp_d))
  Ensure
    store_Z(x, 0)
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

void mpz_init_set(mpz_t r, const mpz_t x)
/*@
  With z
  Require
    undef_data_at(&(r->_mp_alloc)) *
    undef_data_at(&(r->_mp_size)) *
    undef_data_at(&(r->_mp_d)) *
    store_Z(x, z)
  Ensure
    store_Z(r, z) * store_Z(x, z)
*/
{
  mpz_init(r);
  mpz_set(r, x) /*@ where (neq) old = 0, z = z */;
}
