#include "fme_ge_gmp/gmp/gmp_def.h"

int mpn_cmp(unsigned int *ap, unsigned int *bp, int n)
/*@
  With val1 val2
  Require
    0 <= n &&
    mpd_store_Z_compact(UINT_MOD, ap, val1, n) *
    mpd_store_Z_compact(UINT_MOD, bp, val2, n)  
  Ensure
    (val1 > val2 && __return == 1 ||
    val1 == val2 && __return == 0 ||
    val1 < val2 && __return == -1) &&
    mpd_store_Z_compact(UINT_MOD, ap, val1, n) *
    mpd_store_Z_compact(UINT_MOD, bp, val2, n)
*/;

int mpz_cmp(const mpz_t a, const mpz_t b)
/*@ neq
  With za zb
  Require store_Z(a, za) * store_Z(b, zb)
  Ensure
    (za > zb && __return == 1 ||
     za == zb && __return == 0 ||
     za < zb && __return == -1) &&
    store_Z(a, za) * store_Z(b, zb)
*/;

int mpz_cmp(const mpz_t a, const mpz_t b)
/*@ neq */
{
  int asize = a->_mp_size;
  int bsize = b->_mp_size;

  /*@ Assert
      exists aptr a_size acap bptr b_size bcap,
        asize == a_size &&
        bsize == b_size &&
        a == a@pre &&
        b == b@pre &&
        same_sign(za, a_size) &&
        Zabs(a_size) <= acap &&
        same_sign(zb, b_size) &&
        Zabs(b_size) <= bcap &&
        store(&(a->_mp_d), aptr) *
        store(&(a->_mp_size), a_size) *
        store(&(a->_mp_alloc), acap) *
        mpd_store_Z_compact(UINT_MOD, aptr, Zabs(za), Zabs(a_size)) *
        UIntArray::undef_seg(aptr, Zabs(a_size), acap) *
        store(&(b->_mp_d), bptr) *
        store(&(b->_mp_size), b_size) *
        store(&(b->_mp_alloc), bcap) *
        mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb), Zabs(b_size)) *
        UIntArray::undef_seg(bptr, Zabs(b_size), bcap)
  */
  if (asize != bsize)
    return (asize < bsize) ? -1 : 1;
  else if (asize >= 0) {
    /*@ Assert
        exists aptr acap bptr bcap,
          asize == bsize &&
          0 <= asize &&
          a == a@pre &&
          b == b@pre &&
          same_sign(za, asize) &&
          Zabs(asize) <= acap &&
          same_sign(zb, bsize) &&
          Zabs(bsize) <= bcap &&
          store(&(a->_mp_d), aptr) *
          store(&(a->_mp_size), asize) *
          store(&(a->_mp_alloc), acap) *
          mpd_store_Z_compact(UINT_MOD, aptr, Zabs(za), asize) *
          UIntArray::undef_seg(aptr, asize, acap) *
          store(&(b->_mp_d), bptr) *
          store(&(b->_mp_size), bsize) *
          store(&(b->_mp_alloc), bcap) *
          mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb), asize) *
          UIntArray::undef_seg(bptr, asize, bcap)
    */
    return mpn_cmp(a->_mp_d, b->_mp_d, asize)
      /*@ where val1 = Zabs(za), val2 = Zabs(zb) */;
  } else {
    /*@ Assert
        exists aptr acap bptr bcap,
          asize == bsize &&
          asize < 0 &&
          a == a@pre &&
          b == b@pre &&
          same_sign(za, asize) &&
          Zabs(asize) <= acap &&
          same_sign(zb, bsize) &&
          Zabs(bsize) <= bcap &&
          store(&(a->_mp_d), aptr) *
          store(&(a->_mp_size), asize) *
          store(&(a->_mp_alloc), acap) *
          mpd_store_Z_compact(UINT_MOD, aptr, Zabs(za), -asize) *
          UIntArray::undef_seg(aptr, -asize, acap) *
          store(&(b->_mp_d), bptr) *
          store(&(b->_mp_size), bsize) *
          store(&(b->_mp_alloc), bcap) *
          mpd_store_Z_compact(UINT_MOD, bptr, Zabs(zb), -asize) *
          UIntArray::undef_seg(bptr, -asize, bcap)
    */
    return mpn_cmp(b->_mp_d, a->_mp_d, -asize)
      /*@ where val1 = Zabs(zb), val2 = Zabs(za) */;
  }
}
