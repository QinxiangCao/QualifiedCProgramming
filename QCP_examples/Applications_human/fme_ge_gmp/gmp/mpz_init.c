#include "fme_ge_gmp/gmp/gmp_def.h"

void mpz_init(mpz_t x)
/*@ dummy
  Require
    undef_data_at(&(x->_mp_alloc)) *
    undef_data_at(&(x->_mp_size)) *
    undef_data_at(&(x->_mp_d))
  Ensure
    store_Z_dummy(x, &mpz_dummy_limb)
*/;

void mpz_init(mpz_t x)
/*@ abs <= dummy
  Require
    undef_data_at(&(x->_mp_alloc)) *
    undef_data_at(&(x->_mp_size)) *
    undef_data_at(&(x->_mp_d))
  Ensure
    store_Z(x, 0)
*/;

void mpz_init(mpz_t x)
/*@ dummy */
{
  x->_mp_alloc = 0;
  x->_mp_size = 0;
  x->_mp_d = (unsigned int *) &mpz_dummy_limb;
}
