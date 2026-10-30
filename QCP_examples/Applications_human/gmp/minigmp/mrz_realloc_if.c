#include "gmp/minigmp/gmp_def.h"

unsigned int *mpz_realloc(mpz_ptr r, int size)
/*@ preserving
  With
    ptr old cap n
  Require
    size >= cap && size <= INT_MAX && cap >= 0 && cap <= INT_MAX &&
    Zabs(old) <= cap && same_sign(n, old) &&
    mpd_store_Z_compact(UINT_MOD,ptr, Zabs(n), Zabs(old)) * UIntArray::undef_seg(ptr, Zabs(old), cap) &&
      r -> _mp_size == old &&
      r -> _mp_alloc == cap &&
      r -> _mp_d == ptr
  Ensure 
    same_sign(n, old) &&
    mpd_store_Z_compact(UINT_MOD,__return, Zabs(n), Zabs(old)) * UIntArray::undef_seg(__return, Zabs(old), Z::max(size,1)) &&
    r -> _mp_size == old &&
    r -> _mp_alloc == Z::max(size,1) &&
    r -> _mp_d == __return
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
*/;

unsigned int *mrz_realloc_if(mpz_ptr z, int n)
/*@ preserving
  With
    ptr old cap m
  Require
    cap >= 0 && cap <= INT_MAX && n >= 0 && n <= INT_MAX &&
    Zabs(old) <= cap && same_sign(m, old) &&
    mpd_store_Z_compact(UINT_MOD,ptr, Zabs(m), Zabs(old)) * UIntArray::undef_seg(ptr, Zabs(old), cap) &&
      z -> _mp_size == old &&
      z -> _mp_alloc == cap &&
      z -> _mp_d == ptr
  Ensure
    same_sign(m, old) &&
    mpd_store_Z_compact(UINT_MOD,__return, Zabs(m), Zabs(old)) * UIntArray::undef_seg(__return, Zabs(old), Z::max(n,cap)) &&
    z -> _mp_size == old &&
    z -> _mp_alloc == Z::max(n,cap) &&
    z -> _mp_d == __return
*/
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
  if (n > z->_mp_alloc) return mpz_realloc(z, n) /*@ where (preserving) $ preserving
                                                        where (raw) $ raw */;
  return z->_mp_d;
}
