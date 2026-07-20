#include "fme_ge_gmp/gmp/gmp_def.h"

int gmp_abs(int x)
/*@
  Require INT_MIN < x && x <= INT_MAX
  Ensure __return == Zabs(x)
*/;

int gmp_max(int a, int b)
/*@
  Require emp
  Ensure __return == Z::max(a, b)
*/;

static unsigned int *
gmp_alloc_limbs(int size)
/*@
  Require
    size >= 0
  Ensure
    UIntArray::undef_full(__return, size)
*/;

static unsigned int *
gmp_realloc_limbs (unsigned int *old, int old_size, int size)
/*@
  With
    len n
  Require
    old_size >= 0 && size >= old_size &&
    mpd_store_Z_compact(UINT_MOD, old, n, len) *
    UIntArray::undef_seg(old, len, old_size)
  Ensure
    mpd_store_Z_compact(UINT_MOD,__return, n, len) *
    UIntArray::undef_seg(__return, len, size)
*/;

unsigned int *mpz_realloc(mpz_t r, int size)
/*@ raw
  With
    ptr sz cap
  Require
    size >= cap && size <= INT_MAX && cap >= 0 && cap <= INT_MAX &&
    Zabs(sz) <= Z::max(size, 1) &&
    UIntArray::undef_full(ptr, cap) &&
      r->_mp_size == sz &&
      r->_mp_alloc == cap &&
      r->_mp_d == ptr
  Ensure
    UIntArray::undef_full(__return, Z::max(size, 1)) &&
    r->_mp_size == sz &&
    r->_mp_alloc == Z::max(size, 1) &&
    r->_mp_d == __return
*/
{
  size = gmp_max(size, 1);

  if (r->_mp_alloc)
    {
      /*@
        UIntArray::undef_full(r->_mp_d, r->_mp_alloc)
        which implies
        mpd_store_Z_compact(UINT_MOD, r->_mp_d, 0, 0) *
        UIntArray::undef_seg(r->_mp_d, 0, r->_mp_alloc)
      */
    r->_mp_d = gmp_realloc_limbs(r->_mp_d, r->_mp_alloc, size);
      /*@
        mpd_store_Z_compact(UINT_MOD, r->_mp_d, 0, 0) *
        UIntArray::undef_seg(r->_mp_d, 0, size)
        which implies
        UIntArray::undef_full(r->_mp_d, size)
      */
    }
  else
    r->_mp_d = gmp_alloc_limbs(size);
  r->_mp_alloc = size;

  if (gmp_abs(r->_mp_size) > size)
    r->_mp_size = 0;

  return r->_mp_d;
}

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
*/
{
  if (n > z->_mp_alloc) return mpz_realloc(z, n) /*@ where (raw) */;
  return z->_mp_d;
}

void mpz_set_ui(mpz_t r, unsigned long x)
/*@
  With old x0
  Require x == x0 && 0 <= x0 && store_Z(r, old)
  Ensure store_Z(r, x0)
*/
{
  unsigned int *rp;
  int LOCAL_GMP_LIMB_BITS;

  if (x > 0)
    {
      r->_mp_size = 1;
      /*@ Assert
        exists ptr size cap,
        x@pre > 0 &&
        x@pre == x0 &&
        same_sign(old, size) &&
        Zabs(size) <= cap &&
        cap >= 0 &&
        cap <= INT_MAX &&
        Zabs(1) <= Z::max(1, cap) &&
        store(&x, x@pre) *
        store(&r, r@pre) *
        has_permission(&rp) *
        has_permission(&LOCAL_GMP_LIMB_BITS) *
        store(&(r->_mp_size), 1) *
        store(&(r->_mp_alloc), cap) *
        store(&(r->_mp_d), unsigned int *, ptr) *
        UIntArray::undef_full(ptr, cap)
      */
      /*@ Given ptr size cap */
      rp = mrz_realloc_if(r, 1) /*@ where (raw) */;
      /*@ Assert
        exists cap_new,
        cap_new == Z::max(1, cap) &&
        x@pre > 0 &&
        x@pre == x0 &&
        cap_new >= 1 &&
        cap_new <= INT_MAX &&
        store(&x, x@pre) *
        store(&r, r@pre) *
        store(&rp, rp) *
        has_permission(&LOCAL_GMP_LIMB_BITS) *
        store(&(r->_mp_size), 1) *
        store(&(r->_mp_alloc), cap_new) *
        store(&(r->_mp_d), unsigned int *, rp) *
        UIntArray::undef_seg(rp, 0, 1) *
        UIntArray::undef_seg(rp, 1, cap_new)
      */
      rp[0] = x;
      if (32 < 32)
        {
          LOCAL_GMP_LIMB_BITS = 32;
          x = x >> LOCAL_GMP_LIMB_BITS;
          while (x)
            {
              ++ r->_mp_size;
              rp = mrz_realloc_if(r, r->_mp_size) /*@ where (raw) */;
              rp[r->_mp_size - 1] = x;
              x = x >> LOCAL_GMP_LIMB_BITS;
            }
        }
    }
  else
    r->_mp_size = 0;
}
