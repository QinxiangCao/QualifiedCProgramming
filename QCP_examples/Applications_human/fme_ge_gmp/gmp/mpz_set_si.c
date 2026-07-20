#include "fme_ge_gmp/gmp/gmp_def.h"

void mpz_set_ui(mpz_t r, unsigned long x)
/*@
  With old x0
  Require x == x0 && 0 <= x0 && store_Z(r, old)
  Ensure store_Z(r, x0)
*/;

void mpz_neg(mpz_t rop, const mpz_t op)
/*@ eq
  With z
  Require rop == op && store_Z(op, z)
  Ensure rop == op && store_Z(op, -z)
*/;

unsigned int *mrz_realloc_if(mpz_t z, int n)
/*@ raw
  With
    ptr sz cap
  Require
    cap >= 0 && cap <= INT_MAX && n >= 0 && n <= INT_MAX &&
    Zabs(sz) <= Z::max(n, cap) &&
    UIntArray::undef_full(ptr, cap) &&
      z->_mp_size == sz &&
      z->_mp_alloc == cap &&
      z->_mp_d == ptr
  Ensure
    UIntArray::undef_full(__return, Z::max(n, cap)) &&
    z->_mp_size == sz &&
    z->_mp_alloc == Z::max(n, cap) &&
    z->_mp_d == __return
*/;

void mpz_set_si(mpz_t r, long x)
/*@
  With old x0
  Require x == x0 && store_Z(r, old)
  Ensure store_Z(r, x0)
*/
{
  unsigned int *rp;

  if (x >= 0)
    mpz_set_ui(r, x) /*@ where old = old, x0 = x0 */;
  else
    if (32 < 32)
      {
        mpz_set_ui(r, -x) /*@ where old = old, x0 = -x0 */;
        mpz_neg(r, r) /*@ where (eq) z = -x0 */;
      }
  else
    {
      r->_mp_size = -1;
      /*@ Assert
        exists ptr size cap,
        x@pre < 0 &&
        x@pre == x0 &&
        same_sign(old, size) &&
        Zabs(size) <= cap &&
        cap >= 0 &&
        cap <= INT_MAX &&
        Zabs(-1) <= Z::max(1, cap) &&
        store(&x, x@pre) *
        store(&r, r@pre) *
        has_permission(&rp) *
        store(&(r->_mp_size), -1) *
        store(&(r->_mp_alloc), cap) *
        store(&(r->_mp_d), unsigned int *, ptr) *
        UIntArray::undef_full(ptr, cap)
      */
      /*@ Given ptr size cap */
      rp = mrz_realloc_if(r, 1) /*@ where (raw) */;
      /*@ Assert
        exists cap_new,
        cap_new == Z::max(1, cap) &&
        x@pre < 0 &&
        x@pre == x0 &&
        cap_new >= 1 &&
        cap_new <= INT_MAX &&
        store(&x, x@pre) *
        store(&r, r@pre) *
        store(&rp, rp) *
        store(&(r->_mp_size), -1) *
        store(&(r->_mp_alloc), cap_new) *
        store(&(r->_mp_d), unsigned int *, rp) *
        UIntArray::undef_seg(rp, 0, 1) *
        UIntArray::undef_seg(rp, 1, cap_new)
      */
      rp[0] = (unsigned int)(-(x + 1)) + 1;
    }
}
