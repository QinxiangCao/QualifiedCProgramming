#include "fme_ge_gmp/gmp/gmp_def.h"

unsigned int gmp_ctz(unsigned int x)
/*@
  Require 0 < x && x <= UINT_MAX
  Ensure exists odd,
          0 <= __return && __return < 32 &&
          odd > 0 && odd % 2 == 1 &&
          x == odd * Z::pow(2, __return)
*/;

void mpz_tdiv_q_2exp(mpz_ptr r, mpz_srcptr u, unsigned long long cnt)
/*@ eq
  With z
  Require
	    r == u &&
	    cnt >= 0 &&
	    cnt / 32 <= INT_MAX &&
	    store_Z(r, z)
  Ensure
    r == u &&
    store_Z(r, Z::quot(z, Z::pow(2, cnt)))
*/;

static unsigned long long
mpn_common_scan (unsigned int limb, int i, unsigned int *up, int un,
                 unsigned int ux)
/*@ found
  With l n pos
  Require
    n >= 0 && n <= INT_MAX &&
    Zlength(l) == n &&
    list_within_bound(UINT_MOD, l) &&
    mpn_common_scan_target(l, limb, i, un, ux, pos) &&
    UIntArray::full(up, n, l)
  Ensure
    mpn_common_scan_result(l, limb, i, un, ux, pos, __return) &&
    UIntArray::full(up, n, l)
*/
{
  unsigned int cnt;

  /*@ Inv Assert
        up == up@pre &&
        un == un@pre &&
        ux == ux@pre &&
        Zlength(l) == n &&
        n >= 0 &&
        n <= INT_MAX &&
        list_within_bound(UINT_MOD, l) &&
        mpn_common_scan_target(l, limb@pre, i@pre, un@pre, ux@pre, pos) &&
        mpn_common_scan_target(l, limb, i, un, ux, pos) &&
        ((i == i@pre && limb == limb@pre) ||
         (i@pre < i && limb == gmp_scan_limb(ux, Znth(i, l, 0)))) &&
        undef_data_at(&cnt, unsigned int) *
        UIntArray::full(up, n, l)
  */
  while (limb == 0)
    {
      i++;
      /*@ Assert
            up == up@pre &&
            un == un@pre &&
            ux == ux@pre &&
            limb == 0 &&
            i != un &&
            i@pre < i &&
            0 <= i &&
            i < n &&
            Zlength(l) == n &&
            n >= 0 &&
            n <= INT_MAX &&
            list_within_bound(UINT_MOD, l) &&
            mpn_common_scan_target(l, limb@pre, i@pre, un@pre, ux@pre, pos) &&
            mpn_common_scan_target(l, limb, i - 1, un, ux, pos) &&
            undef_data_at(&cnt, unsigned int) *
            UIntArray::full(up, n, l)
      */
      if (i == un)
        return (ux == 0 ? ~(unsigned long long) 0 : ((unsigned long long) un) * ((unsigned long long) 32));
      limb = ux ^ up[i];
      /*@ Assert
            up == up@pre &&
            un == un@pre &&
            ux == ux@pre &&
            Zlength(l) == n &&
            n >= 0 &&
            n <= INT_MAX &&
            list_within_bound(UINT_MOD, l) &&
            mpn_common_scan_target(l, limb@pre, i@pre, un@pre, ux@pre, pos) &&
            mpn_common_scan_target(l, limb, i, un, ux, pos) &&
            i@pre < i &&
            limb == gmp_scan_limb(ux, Znth(i, l, 0)) &&
            undef_data_at(&cnt, unsigned int) *
            UIntArray::full(up, n, l)
      */
    }
  cnt = gmp_ctz(limb);
  /*@ Assert
        exists odd,
          up == up@pre &&
          un == un@pre &&
          ux == ux@pre &&
          0 <= cnt && cnt < 32 &&
          odd > 0 &&
          odd % 2 == 1 &&
          limb == odd * Z::pow(2, cnt) &&
          Zlength(l) == n &&
          n >= 0 &&
          n <= INT_MAX &&
          list_within_bound(UINT_MOD, l) &&
          mpn_common_scan_target(l, limb@pre, i@pre, un@pre, ux@pre, pos) &&
          mpn_common_scan_target(l, limb, i, un, ux, pos) &&
          ((i == i@pre && limb == limb@pre) ||
           (i@pre < i && limb == gmp_scan_limb(ux, Znth(i, l, 0)))) &&
          UIntArray::full(up, n, l)
  */
  return ((unsigned long long) i) * ((unsigned long long) 32) + cnt;
}

unsigned long long
mpn_scan1 (unsigned int *ptr, unsigned long long bit)
/*@
  With l n
  Require
    n > 0 &&
    n <= INT_MAX &&
    bit >= 0 &&
    bit / 32 < n &&
    Zlength(l) == n &&
    list_within_bound(UINT_MOD, l) &&
    mpn_scan1_target(l, bit) &&
    UIntArray::full(ptr, n, l)
  Ensure
    mpn_scan1_result(l, bit, __return) &&
    UIntArray::full(ptr, n, l)
*/
{
  int i;
  i = bit / 32;
  /*@ Assert
        exists pos,
          ptr == ptr@pre &&
          bit == bit@pre &&
          i == bit / 32 &&
          0 <= i &&
          i < n &&
          n > 0 &&
          n <= INT_MAX &&
          bit >= 0 &&
          Zlength(l) == n &&
          list_within_bound(UINT_MOD, l) &&
          mpn_common_scan_target(
            l,
            Znth(i, l, 0) & unsigned_last_nbits(4294967295 * Z::pow(2, bit % 32), 32),
            i, i, 0, pos) &&
          UIntArray::full(ptr, n, l)
  */
  /*@ Given pos */
  return mpn_common_scan ( ptr[i] & (((unsigned int) 4294967295) << (bit % 32)),
                          i, ptr, i, 0)
                          /*@ where (found) l = l, n = n, pos = pos */;
}

static unsigned long long
mpz_make_odd (mpz_ptr r)
/*@
  With z
  Require
    z > 0 &&
    store_Z(r, z)
  Ensure exists odd,
    0 <= __return &&
    odd > 0 &&
    odd % 2 == 1 &&
    z == odd * Z::pow(2, __return) &&
    store_Z(r, odd)
*/
{
  unsigned long long shift;

      /*@ Assert
        exists ptr size cap l,
          z > 0 &&
          r == r@pre &&
          size > 0 &&
          size <= cap &&
          cap >= 0 &&
          Zlength(l) == size &&
          list_to_Z(UINT_MOD, l) == z &&
          list_within_bound(UINT_MOD, l) &&
          last(l, 1) >= 1 &&
          same_sign(z, size) &&
          r->_mp_size == size &&
          r->_mp_alloc == cap &&
          r->_mp_d == ptr &&
          mpn_scan1_target(l, 0) &&
          has_permission(&shift) *
          UIntArray::full(ptr, size, l) *
          UIntArray::undef_seg(ptr, size, cap)
  */
  /*@ Given ptr size cap l */
  shift = mpn_scan1 (r->_mp_d, 0) /*@ where l = l, n = size */;
      /*@ Assert
        exists ptr size cap l,
          z > 0 &&
          r == r@pre &&
          shift >= 0 &&
          size > 0 &&
          size <= cap &&
          cap >= 0 &&
          Zlength(l) == size &&
          list_to_Z(UINT_MOD, l) == z &&
          list_within_bound(UINT_MOD, l) &&
          last(l, 1) >= 1 &&
          same_sign(z, size) &&
          r->_mp_size == size &&
          r->_mp_alloc == cap &&
          r->_mp_d == ptr &&
          mpn_scan1_result(l, 0, shift) &&
          UIntArray::full(ptr, size, l) *
          UIntArray::undef_seg(ptr, size, cap)
  */
      /*@ Assert
        exists odd,
          odd == Z::quot(z, Z::pow(2, shift)) &&
          r == r@pre &&
          0 <= shift &&
          odd > 0 &&
          odd % 2 == 1 &&
          z == odd * Z::pow(2, shift) &&
          store_Z(r, z)
  */
  /*@ Given odd */
  mpz_tdiv_q_2exp (r, r, shift) /*@ where (eq) z = z */;
  /*@ Assert
        odd == Z::quot(z, Z::pow(2, shift)) &&
        r == r@pre &&
        0 <= shift &&
        odd > 0 &&
        odd % 2 == 1 &&
        z == odd * Z::pow(2, shift) &&
        store_Z(r, odd)
  */

  return shift;
}
