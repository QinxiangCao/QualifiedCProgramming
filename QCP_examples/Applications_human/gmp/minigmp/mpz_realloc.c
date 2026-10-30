#include "gmp/minigmp/gmp_def.h"

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

unsigned int *
gmp_alloc_limbs(int size)
/*@
  Require
    size >= 0
  Ensure
    UIntArray::undef_full(__return, size)
*/;

unsigned int *
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

unsigned int *mpz_realloc(mpz_ptr r, int size)
/*@ preserving
  With
    ptr old cap n
  Require
    size >= cap && size <= INT_MAX && cap >= 0 && cap <= INT_MAX &&
    Zabs(old) <= cap && same_sign(n, old) &&
    mpd_store_Z_compact(UINT_MOD,ptr, Zabs(n), Zabs(old)) * UIntArray::undef_seg(ptr, Zabs(old), cap) &&
      r->_mp_size == old &&
      r->_mp_alloc == cap &&
      r->_mp_d == ptr
  Ensure
    same_sign(n, old) &&
    mpd_store_Z_compact(UINT_MOD,__return, Zabs(n), Zabs(old)) * UIntArray::undef_seg(__return, Zabs(old), Z::max(size,1)) &&
    r->_mp_size == old &&
    r->_mp_alloc == Z::max(size,1) &&
    r->_mp_d == __return
*/
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
        $ raw
        which implies
        mpd_store_Z_compact(UINT_MOD, r->_mp_d, 0, 0) *
        UIntArray::undef_seg(r->_mp_d, 0, r->_mp_alloc)
      */
    r->_mp_d = gmp_realloc_limbs(r->_mp_d, r->_mp_alloc, size);
      /*@
        mpd_store_Z_compact(UINT_MOD, r->_mp_d, 0, 0) *
        UIntArray::undef_seg(r->_mp_d, 0, size)
        $ raw
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
