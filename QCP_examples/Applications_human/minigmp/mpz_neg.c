#include "mpz_neg.h"

/*@ Import Coq Require Import SimpleC.EE.Applications_human.minigmp.mpz_neg_lib */

void mpz_neg(mpz_t u, const mpz_t v)
/*@ With n m
    Require store_Z(u, n) * store_Z(v, m)
    Ensure store_Z(u, -m) * store_Z(v, m)
*/
{
  int size = v->_mp_size;
  int count = gmp_abs(size);
  gmp_free_limbs(u->_mp_d, u->_mp_alloc);
  unsigned int *digits = gmp_alloc_limbs(count);
  mpn_copyi(digits, v->_mp_d, count);
  u->_mp_d = digits;
  u->_mp_alloc = count;
  u->_mp_size = -size;
}
