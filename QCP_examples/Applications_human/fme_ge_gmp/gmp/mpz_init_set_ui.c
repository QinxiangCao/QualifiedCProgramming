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

void mpz_set_ui(mpz_t r, unsigned long x)
/*@
  With old x0
  Require x == x0 && 0 <= x0 && store_Z(r, old)
  Ensure store_Z(r, x0)
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
*/
{
  mpz_init(r);
  mpz_set_ui(r, x) /*@ where old = 0, x0 = x0 */;
}
