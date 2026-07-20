#include "fme_ge_gmp/gmp/gmp_def.h"

static unsigned int *
gmp_alloc_limbs (int size)
/*@ pos
  Require
    size > 0
  Ensure
    __return != 0 &&
    UIntArray::undef_full(__return, size)
*/
/*@ nonneg
  Require
    size >= 0
  Ensure
    UIntArray::undef_full(__return, size)
*/;

void mpz_init2(mpz_ptr x, unsigned long long bits)
/*@
  With alloc
  Require
    bits == alloc * 32 &&
    alloc > 0 &&
    alloc <= INT_MAX &&
    undef_data_at(&(x->_mp_alloc)) *
    undef_data_at(&(x->_mp_size)) *
    undef_data_at(&(x->_mp_d))
  Ensure exists ptr,
    ptr != 0 &&
    x->_mp_alloc == alloc &&
    x->_mp_size == 0 &&
    x->_mp_d == ptr &&
    UIntArray::undef_full(ptr, alloc)
*/
{
  int rn;

  bits = bits - (bits != 0);
  rn = 1 + bits / 32;

  x->_mp_alloc = rn;
  x->_mp_size = 0;
  x->_mp_d = gmp_alloc_limbs(rn) /*@ where (pos) */;
}
