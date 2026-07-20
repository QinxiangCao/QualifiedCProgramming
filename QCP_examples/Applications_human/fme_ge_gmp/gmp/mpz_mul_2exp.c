#include "fme_ge_gmp/gmp/gmp_def.h"

int gmp_abs(int x)
/*@
  Require INT_MIN < x && x <= INT_MAX
  Ensure __return == Zabs(x)
*/;

unsigned int *mrz_realloc_if(mpz_t z, int n)
/*@
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
*/;

void
mpn_copyd(unsigned int *d, unsigned int *s, int n)
/*@ shifted
  With l off
  Require
    n >= 0 && off >= 0 && n + off <= INT_MAX &&
    d == s + off * sizeof(unsigned int) &&
    Zlength(l) == n &&
    list_within_bound(UINT_MOD, l) &&
    UIntArray::full(s, n, l) *
    UIntArray::undef_seg(s, n, n + off)
  Ensure
    d == s + off * sizeof(unsigned int) &&
    UIntArray::undef_seg(s, 0, off) *
    UIntArray::seg(d, 0, n, sublist(0, n, l))
*/
{
  /*@
    UIntArray::full(s, n, l) *
    UIntArray::undef_seg(s, n, n + off)
    which implies
    UIntArray::seg(s, 0, n, sublist(0, n, l)) *
    UIntArray::undef_seg(s, n, n + off)
  */
  /*@ Destruct with
        off_zero: off == 0;
        off_pos: off > 0
  */
  --n;
  /*@ Assert
        d == d@pre &&
        s == s@pre &&
        d == s &&
        d@pre == s@pre &&
        off == 0 &&
        n == n@pre - 1 &&
        n@pre >= 0 &&
        Zlength(l) == n@pre &&
        list_within_bound(UINT_MOD, l) &&
        UIntArray::seg(s@pre, 0, n@pre, sublist(0, n@pre, l)) $ off_zero
  */
  /*@ Assert exists k,
        d == d@pre &&
        s == s@pre &&
        off > 0 &&
        d == s + off * sizeof(unsigned int) &&
        n == n@pre - 1 &&
        n@pre >= 0 &&
        n@pre + off <= INT_MAX &&
        k == n@pre &&
        k <= n + 1 &&
        n + 1 <= k &&
        Zlength(l) == n@pre &&
        list_within_bound(UINT_MOD, l) &&
        UIntArray::seg(s@pre, 0, k, sublist(0, k, l)) *
        UIntArray::undef_seg(s@pre, k, off + k) *
        UIntArray::seg(d@pre, k, n@pre, sublist(k, n@pre, l)) $ off_pos
  */
  /*@ Branch name
        off_zero: off == 0;
        off_pos: off > 0
  */
  /*@ Inv
        off_zero:
          d == d@pre &&
          s == s@pre &&
          d == s &&
          d@pre == s@pre &&
          off == 0 &&
          -1 <= n &&
          n < n@pre &&
          n@pre >= 0 &&
          Zlength(l) == n@pre &&
          list_within_bound(UINT_MOD, l) &&
          UIntArray::seg(s@pre, 0, n@pre, sublist(0, n@pre, l));
        off_pos: exists k,
          d == d@pre &&
          s == s@pre &&
          off > 0 &&
          d == s + off * sizeof(unsigned int) &&
          -1 <= n &&
          n < n@pre &&
          n@pre >= 0 &&
          n@pre + off <= INT_MAX &&
          k <= n + 1 &&
          n + 1 <= k &&
          0 <= k &&
          k <= n@pre &&
          Zlength(l) == n@pre &&
          list_within_bound(UINT_MOD, l) &&
          UIntArray::seg(s@pre, 0, k, sublist(0, k, l)) *
          UIntArray::undef_seg(s@pre, k, off + k) *
          UIntArray::seg(d@pre, k, n@pre, sublist(k, n@pre, l))
        with
          off_zero ==> off_zero
          off_pos ==> off_pos
  */
  while (n >= 0)
    {
      /*@
        d == s &&
        s == s@pre &&
        d@pre == s@pre &&
        0 <= n &&
        n < n@pre &&
        UIntArray::seg(s@pre, 0, n@pre, sublist(0, n@pre, l))
        $ off_zero
        which implies
        d == s &&
        s == s@pre &&
        d@pre == s@pre &&
        UIntArray::seg(s@pre, 0, n, sublist(0, n, l)) *
        UIntArray::seg(s@pre, n, n + 1, sublist(n, n + 1, l)) *
        UIntArray::seg(s@pre, n + 1, n@pre, sublist(n + 1, n@pre, l))
      */
      /*@ Assert
        d == d@pre &&
        s == s@pre &&
        d == s + off * sizeof(unsigned int) &&
        off > 0 &&
        0 <= n &&
        n < n@pre &&
        n@pre >= 0 &&
        n@pre + off <= INT_MAX &&
        Zlength(l) == n@pre &&
        list_within_bound(UINT_MOD, l) &&
        UIntArray::seg(s@pre, 0, n + 1, sublist(0, n + 1, l)) *
        UIntArray::undef_seg(s@pre, n + 1, off + n + 1) *
        UIntArray::seg(d@pre, n + 1, n@pre, sublist(n + 1, n@pre, l))
        $ off_pos */
      /*@ Branch name
        off_zero: off == 0;
        off_pos: off > 0
      */
      /*@
        d == d@pre &&
        s == s@pre &&
        d == s + off * sizeof(unsigned int) &&
        off > 0 &&
        0 <= n &&
        n < n@pre &&
        n@pre >= 0 &&
        n@pre + off <= INT_MAX &&
        Zlength(l) == n@pre &&
        list_within_bound(UINT_MOD, l) &&
        UIntArray::seg(s@pre, 0, n + 1, sublist(0, n + 1, l)) *
        UIntArray::undef_seg(s@pre, n + 1, off + n + 1) *
        UIntArray::seg(d@pre, n + 1, n@pre, sublist(n + 1, n@pre, l))
        $ off_pos
        which implies
        d == d@pre &&
        s == s@pre &&
        d == s + off * sizeof(unsigned int) &&
        off > 0 &&
        0 <= n &&
        n < n@pre &&
        n@pre >= 0 &&
        n@pre + off <= INT_MAX &&
        Zlength(l) == n@pre &&
        list_within_bound(UINT_MOD, l) &&
        UIntArray::seg(s@pre, 0, n, sublist(0, n, l)) *
        UIntArray::seg(s@pre, n, n + 1, sublist(n, n + 1, l)) *
        UIntArray::undef_seg(s@pre, n + 1, off + n) *
        UIntArray::undef_seg(d@pre, n, n + 1) *
        UIntArray::seg(d@pre, n + 1, n@pre, sublist(n + 1, n@pre, l))
      */
      d[n] = s[n];
      --n;
      /*@ off_zero ==> off_zero */
      /*@ off_pos ==> off_pos */
    }
}

void
mpn_zero(unsigned int *rp, int n)
/*@
  Require
    n >= 0 && n <= INT_MAX &&
    UIntArray::undef_seg(rp, 0, n)
  Ensure exists l,
    Zlength(l) == n &&
    list_within_bound(UINT_MOD, l) &&
    list_to_Z(UINT_MOD, l) == 0 &&
    UIntArray::full(rp, n, l)
*/
{
  /*@
    UIntArray::undef_seg(rp, 0, n)
    which implies
    UIntArray::undef_seg(rp, 0, n)
  */
  --n;
  /*@ Inv Assert exists l_done,
        rp == rp@pre &&
        -1 <= n &&
        n < n@pre &&
        n@pre >= 0 &&
        Zlength(l_done) == n@pre - (n + 1) &&
        list_within_bound(UINT_MOD, l_done) &&
        list_to_Z(UINT_MOD, l_done) == 0 &&
        UIntArray::undef_seg(rp@pre, 0, n + 1) *
        UIntArray::seg(rp@pre, n + 1, n@pre, l_done)
  */
  while (n >= 0)
    {
      /*@
        rp == rp@pre &&
        0 <= n &&
        n < n@pre &&
        UIntArray::undef_seg(rp@pre, 0, n + 1)
        which implies
        rp == rp@pre &&
        UIntArray::undef_seg(rp@pre, 0, n) *
        UIntArray::undef_seg(rp@pre, n, n + 1)
      */
      rp[n] = 0;
      --n;
    }
}

unsigned int
mpn_lshift(unsigned int *rp, unsigned int *up, int n, unsigned int cnt)
/*@ shifted
  With l_up off
  Require
    n > 0 && off >= 0 && n + off <= INT_MAX &&
    1 <= cnt && cnt < 32 &&
    rp == up + off * sizeof(unsigned int) &&
    Zlength(l_up) == n &&
    list_within_bound(UINT_MOD, l_up) &&
    UIntArray::full(up, n, l_up) *
    UIntArray::undef_seg(up, n, n + off)
  Ensure exists l_out,
    Zlength(l_out) == n &&
    list_within_bound(UINT_MOD, l_out) &&
    list_to_Z(UINT_MOD, l_out) + __return * Z::pow(UINT_MOD, n) ==
      list_to_Z(UINT_MOD, l_up) * Z::pow(2, cnt) &&
    UIntArray::undef_seg(up, 0, off) *
    UIntArray::seg(rp, 0, n, l_out)
*/
{
  /*@
    UIntArray::full(up, n, l_up) *
    UIntArray::undef_seg(up, n, n + off)
    which implies
    UIntArray::seg(up, 0, n, sublist(0, n, l_up)) *
    UIntArray::undef_seg(up, n, n + off)
  */
  /*@ Destruct with
        off_zero: off == 0;
        off_pos: off > 0
  */
  unsigned int high_limb;
  unsigned int low_limb;
  unsigned int tnc;
  unsigned int retval;
  int i;

  tnc = 32 - cnt;
  i = n - 1;
  low_limb = up[i];
  retval = low_limb >> tnc;
  high_limb = low_limb << cnt;

  /*@ Assert exists l_done,
        rp == rp@pre &&
        up == up@pre &&
        n == n@pre &&
        cnt == cnt@pre &&
        off == 0 &&
        rp == up &&
        tnc == 32 - cnt@pre &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        i == n@pre - 1 &&
        0 <= i &&
        i < n@pre &&
        Zlength(l_up) == n@pre &&
        l_done == nil &&
        Zlength(l_done) == n@pre - (i + 1) &&
        list_within_bound(UINT_MOD, l_up) &&
        list_within_bound(UINT_MOD, l_done) &&
        low_limb == Znth(i, l_up, 0) &&
        retval == Znth(n@pre - 1, l_up, 0) / Z::pow(2, tnc) &&
        high_limb == unsigned_last_nbits(Znth(i, l_up, 0) * Z::pow(2, cnt@pre), 32) &&
        high_limb + list_to_Z(UINT_MOD, l_done) * UINT_MOD +
          retval * Z::pow(UINT_MOD, n@pre - i) ==
          list_to_Z(UINT_MOD, sublist(i, n@pre, l_up)) * Z::pow(2, cnt@pre) &&
        UIntArray::seg(up@pre, 0, i + 1, sublist(0, i + 1, l_up)) *
        UIntArray::seg(rp@pre, i + 1, n@pre, l_done)
      $ off_zero */
  /*@ Assert exists l_done,
        rp == rp@pre &&
        up == up@pre &&
        n == n@pre &&
        cnt == cnt@pre &&
        off > 0 &&
        rp == up + off * sizeof(unsigned int) &&
        n@pre + off <= INT_MAX &&
        tnc == 32 - cnt@pre &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        i == n@pre - 1 &&
        0 <= i &&
        i < n@pre &&
        Zlength(l_up) == n@pre &&
        l_done == nil &&
        Zlength(l_done) == n@pre - (i + 1) &&
        list_within_bound(UINT_MOD, l_up) &&
        list_within_bound(UINT_MOD, l_done) &&
        low_limb == Znth(i, l_up, 0) &&
        retval == Znth(n@pre - 1, l_up, 0) / Z::pow(2, tnc) &&
        high_limb == unsigned_last_nbits(Znth(i, l_up, 0) * Z::pow(2, cnt@pre), 32) &&
        high_limb + list_to_Z(UINT_MOD, l_done) * UINT_MOD +
          retval * Z::pow(UINT_MOD, n@pre - i) ==
          list_to_Z(UINT_MOD, sublist(i, n@pre, l_up)) * Z::pow(2, cnt@pre) &&
        UIntArray::seg(up@pre, 0, i + 1, sublist(0, i + 1, l_up)) *
        UIntArray::undef_seg(up@pre, i + 1, off + i + 1) *
        UIntArray::seg(rp@pre, i + 1, n@pre, l_done)
      $ off_pos */
  /*@ Branch name
      off_zero: off == 0;
      off_pos: off > 0
  */

  /*@ Inv
        off_zero_inv: exists l_done,
          rp == rp@pre &&
          up == up@pre &&
          n == n@pre &&
          cnt == cnt@pre &&
          off == 0 &&
          rp == up &&
          tnc == 32 - cnt@pre &&
          1 <= cnt@pre &&
          cnt@pre < 32 &&
          0 <= i &&
          i < n@pre &&
          Zlength(l_up) == n@pre &&
          Zlength(l_done) == n@pre - (i + 1) &&
          list_within_bound(UINT_MOD, l_up) &&
          list_within_bound(UINT_MOD, l_done) &&
          low_limb == Znth(i, l_up, 0) &&
          retval == Znth(n@pre - 1, l_up, 0) / Z::pow(2, tnc) &&
          high_limb == unsigned_last_nbits(Znth(i, l_up, 0) * Z::pow(2, cnt@pre), 32) &&
          high_limb + list_to_Z(UINT_MOD, l_done) * UINT_MOD +
            retval * Z::pow(UINT_MOD, n@pre - i) ==
            list_to_Z(UINT_MOD, sublist(i, n@pre, l_up)) * Z::pow(2, cnt@pre) &&
          UIntArray::seg(up@pre, 0, i + 1, sublist(0, i + 1, l_up)) *
          UIntArray::seg(rp@pre, i + 1, n@pre, l_done);
        off_pos_inv: exists l_done,
          rp == rp@pre &&
          up == up@pre &&
          n == n@pre &&
          cnt == cnt@pre &&
          off > 0 &&
          rp == up + off * sizeof(unsigned int) &&
          n@pre + off <= INT_MAX &&
          tnc == 32 - cnt@pre &&
          1 <= cnt@pre &&
          cnt@pre < 32 &&
          0 <= i &&
          i < n@pre &&
          Zlength(l_up) == n@pre &&
          Zlength(l_done) == n@pre - (i + 1) &&
          list_within_bound(UINT_MOD, l_up) &&
          list_within_bound(UINT_MOD, l_done) &&
          low_limb == Znth(i, l_up, 0) &&
          retval == Znth(n@pre - 1, l_up, 0) / Z::pow(2, tnc) &&
          high_limb == unsigned_last_nbits(Znth(i, l_up, 0) * Z::pow(2, cnt@pre), 32) &&
          high_limb + list_to_Z(UINT_MOD, l_done) * UINT_MOD +
            retval * Z::pow(UINT_MOD, n@pre - i) ==
            list_to_Z(UINT_MOD, sublist(i, n@pre, l_up)) * Z::pow(2, cnt@pre) &&
          UIntArray::seg(up@pre, 0, i + 1, sublist(0, i + 1, l_up)) *
          UIntArray::undef_seg(up@pre, i + 1, off + i + 1) *
          UIntArray::seg(rp@pre, i + 1, n@pre, l_done)
        with
          off_zero ==> off_zero_inv
          off_pos ==> off_pos_inv
  */
  while (i > 0) {
    i = i - 1;
    low_limb = up[i];
    /*@ Assert exists l_done,
        rp == rp@pre &&
        up == up@pre &&
        n == n@pre &&
        cnt == cnt@pre &&
        off == 0 &&
        rp == up &&
        tnc == 32 - cnt@pre &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        0 <= low_limb &&
        low_limb <= UINT_MAX &&
        low_limb == Znth(i, l_up, 0) &&
        0 <= i &&
        i + 1 < n@pre &&
        Zlength(l_up) == n@pre &&
        Zlength(l_done) == n@pre - (i + 2) &&
        list_within_bound(UINT_MOD, l_up) &&
        list_within_bound(UINT_MOD, l_done) &&
        retval == Znth(n@pre - 1, l_up, 0) / Z::pow(2, tnc) &&
        high_limb == unsigned_last_nbits(Znth(i + 1, l_up, 0) * Z::pow(2, cnt@pre), 32) &&
        high_limb + list_to_Z(UINT_MOD, l_done) * UINT_MOD +
          retval * Z::pow(UINT_MOD, n@pre - (i + 1)) ==
          list_to_Z(UINT_MOD, sublist(i + 1, n@pre, l_up)) * Z::pow(2, cnt@pre) &&
        UIntArray::seg(up@pre, 0, i + 2, sublist(0, i + 2, l_up)) *
        UIntArray::seg(rp@pre, i + 2, n@pre, l_done) $ off_zero_inv */
    /*@ Assert exists l_done,
        rp == rp@pre &&
        up == up@pre &&
        n == n@pre &&
        cnt == cnt@pre &&
        off > 0 &&
        rp == up + off * sizeof(unsigned int) &&
        n@pre + off <= INT_MAX &&
        tnc == 32 - cnt@pre &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        0 <= low_limb &&
        low_limb <= UINT_MAX &&
        low_limb == Znth(i, l_up, 0) &&
        0 <= i &&
        i + 1 < n@pre &&
        Zlength(l_up) == n@pre &&
        Zlength(l_done) == n@pre - (i + 2) &&
        list_within_bound(UINT_MOD, l_up) &&
        list_within_bound(UINT_MOD, l_done) &&
        retval == Znth(n@pre - 1, l_up, 0) / Z::pow(2, tnc) &&
        high_limb == unsigned_last_nbits(Znth(i + 1, l_up, 0) * Z::pow(2, cnt@pre), 32) &&
        high_limb + list_to_Z(UINT_MOD, l_done) * UINT_MOD +
          retval * Z::pow(UINT_MOD, n@pre - (i + 1)) ==
          list_to_Z(UINT_MOD, sublist(i + 1, n@pre, l_up)) * Z::pow(2, cnt@pre) &&
        UIntArray::seg(up@pre, 0, i + 2, sublist(0, i + 2, l_up)) *
        UIntArray::undef_seg(up@pre, i + 2, off + i + 2) *
        UIntArray::seg(rp@pre, i + 2, n@pre, l_done) $ off_pos_inv */
    /*@ Branch name
        off_zero_inv: off == 0;
        off_pos_inv: off > 0
    */
    /*@
      rp == up &&
      up == up@pre &&
      0 <= i &&
      i + 1 < n@pre &&
      UIntArray::seg(up@pre, 0, i + 2, sublist(0, i + 2, l_up))
      $ off_zero_inv
      which implies
      rp == up &&
      up == up@pre &&
      UIntArray::seg(up@pre, 0, i + 1, sublist(0, i + 1, l_up)) *
      UIntArray::seg(up@pre, i + 1, i + 2, sublist(i + 1, i + 2, l_up))
    */
    /*@
      rp == rp@pre &&
      up == up@pre &&
      rp == up + off * sizeof(unsigned int) &&
      off > 0 &&
      0 <= i &&
      i + 1 < n@pre &&
      UIntArray::undef_seg(up@pre, i + 2, off + i + 2)
      $ off_pos_inv
      which implies
      rp == rp@pre &&
      up == up@pre &&
      rp == up + off * sizeof(unsigned int) &&
      UIntArray::undef_seg(up@pre, i + 2, off + i + 1) *
      UIntArray::undef_seg(rp@pre, i + 1, i + 2)
    */
    rp[i + 1] = high_limb | (low_limb >> tnc);
    high_limb = low_limb << cnt;
    /*@ off_zero_inv ==> off_zero_inv */
    /*@ off_pos_inv ==> off_pos_inv */
  }
  /*@ Assert exists l_done,
        rp == rp@pre &&
        up == up@pre &&
        n == n@pre &&
        cnt == cnt@pre &&
        off == 0 &&
        rp == up &&
        tnc == 32 - cnt@pre &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        0 <= low_limb &&
        low_limb <= UINT_MAX &&
        i == 0 &&
        Zlength(l_up) == n@pre &&
        Zlength(l_done) == n@pre - 1 &&
        list_within_bound(UINT_MOD, l_up) &&
        list_within_bound(UINT_MOD, l_done) &&
        retval == Znth(n@pre - 1, l_up, 0) / Z::pow(2, tnc) &&
        high_limb + list_to_Z(UINT_MOD, l_done) * UINT_MOD +
          retval * Z::pow(UINT_MOD, n@pre) ==
          list_to_Z(UINT_MOD, l_up) * Z::pow(2, cnt@pre) &&
        UIntArray::seg(up@pre, 0, 1, sublist(0, 1, l_up)) *
        UIntArray::seg(rp@pre, 1, n@pre, l_done) $ off_zero_inv */
  /*@ Assert exists l_done,
        rp == rp@pre &&
        up == up@pre &&
        n == n@pre &&
        cnt == cnt@pre &&
        off > 0 &&
        rp == up + off * sizeof(unsigned int) &&
        n@pre + off <= INT_MAX &&
        tnc == 32 - cnt@pre &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        0 <= low_limb &&
        low_limb <= UINT_MAX &&
        i == 0 &&
        Zlength(l_up) == n@pre &&
        Zlength(l_done) == n@pre - 1 &&
        list_within_bound(UINT_MOD, l_up) &&
        list_within_bound(UINT_MOD, l_done) &&
        retval == Znth(n@pre - 1, l_up, 0) / Z::pow(2, tnc) &&
        high_limb + list_to_Z(UINT_MOD, l_done) * UINT_MOD +
          retval * Z::pow(UINT_MOD, n@pre) ==
          list_to_Z(UINT_MOD, l_up) * Z::pow(2, cnt@pre) &&
        UIntArray::seg(up@pre, 0, 1, sublist(0, 1, l_up)) *
        UIntArray::undef_seg(up@pre, 1, off + 1) *
        UIntArray::seg(rp@pre, 1, n@pre, l_done) $ off_pos_inv */
  /*@ Branch name
      off_zero_inv: off == 0;
      off_pos_inv: off > 0
  */
  /*@
    rp == up &&
    up == up@pre &&
    i == 0 &&
    UIntArray::seg(up@pre, 0, 1, sublist(0, 1, l_up))
    $ off_zero_inv
    which implies
    rp == up &&
    up == up@pre &&
    i == 0 &&
    UIntArray::seg(rp, 0, 1, sublist(0, 1, l_up))
  */
  /*@
    rp == rp@pre &&
    up == up@pre &&
    rp == up + off * sizeof(unsigned int) &&
    off > 0 &&
    i == 0 &&
    UIntArray::undef_seg(up@pre, 1, off + 1)
    $ off_pos_inv
    which implies
    rp == rp@pre &&
    up == up@pre &&
    rp == up + off * sizeof(unsigned int) &&
    i == 0 &&
    UIntArray::undef_seg(up@pre, 1, off) *
    UIntArray::undef_seg(rp@pre, 0, 1)
  */
  rp[0] = high_limb;
  return retval;
}

void
mpz_mul_2exp(mpz_ptr r, mpz_srcptr u, unsigned long long bits)
/*@ eq
  With z
  Require
    r == u &&
    bits >= 0 &&
    mpz_mul_2exp_fits(z, bits) &&
    store_Z(r, z)
  Ensure
    r == u &&
    store_Z(r, z * Z::pow(2, bits))
*/
{
  int un, rn;
  int limbs;
  unsigned int shift;
  unsigned int *rp;

  /*@ Assert exists ptr size cap,
        r == u &&
        r == r@pre &&
        u == u@pre &&
        bits == bits@pre &&
        bits >= 0 &&
        mpz_mul_2exp_fits(z_eq, bits) &&
        same_sign(z_eq, size) &&
        Zabs(size) <= cap &&
        has_permission(&un) *
        has_permission(&rn) *
        has_permission(&limbs) *
        has_permission(&shift) *
        has_permission(&rp) *
        store(&(u->_mp_d), ptr) *
        store(&(u->_mp_size), size) *
        store(&(u->_mp_alloc), cap) *
        mpd_store_Z_compact(UINT_MOD, ptr, Zabs(z_eq), Zabs(size)) *
        UIntArray::undef_seg(ptr, Zabs(size), cap)
  */
  un = gmp_abs(u->_mp_size);
  if (un == 0)
    {
      r->_mp_size = 0;
      return;
    }

  limbs = bits / 32;
  shift = bits % 32;

  rn = un + limbs + (shift > 0);
  rp = mrz_realloc_if(r, rn);
  if (shift > 0)
    {
      /*@ Assert exists l size cap,
            r == r@pre &&
            u == u@pre &&
            r == u &&
            bits == bits@pre &&
            bits >= 0 &&
            mpz_mul_2exp_fits(z_eq, bits) &&
            same_sign(z_eq, size) &&
            Zabs(size) <= cap &&
            un == Zabs(size) &&
            un > 0 &&
            limbs == bits / 32 &&
            limbs >= 0 &&
            shift == bits % 32 &&
            shift > 0 &&
            1 <= shift &&
            shift < 32 &&
            rn == un + limbs + 1 &&
            rn <= INT_MAX &&
            un + limbs <= INT_MAX &&
            Zlength(l) == un &&
            list_within_bound(UINT_MOD, l) &&
            list_to_Z(UINT_MOD, l) == Zabs(z_eq) &&
            last(l, 1) >= 1 &&
            u->_mp_size == size &&
            u->_mp_alloc == Z::max(rn, cap) &&
            u->_mp_d == rp &&
            rp == u->_mp_d &&
            UIntArray::full(u->_mp_d, un, l) *
            UIntArray::undef_seg(u->_mp_d, un, un + limbs) *
            UIntArray::undef_seg(u->_mp_d, un + limbs, Z::max(rn, cap))
      */
      /*@ Given l size cap */
      unsigned int cy = mpn_lshift(rp + limbs, u->_mp_d, un, shift)
        /*@ where (shifted) l_up = l, off = limbs */;
      /*@ Assert exists l_in l_out size cap cy_val,
            r == r@pre &&
            u == u@pre &&
            r == u &&
            bits == bits@pre &&
            bits >= 0 &&
            mpz_mul_2exp_fits(z_eq, bits) &&
            same_sign(z_eq, size) &&
            Zabs(size) <= cap &&
            un == Zabs(size) &&
            un > 0 &&
            limbs == bits / 32 &&
            limbs >= 0 &&
            shift == bits % 32 &&
            shift > 0 &&
            1 <= shift &&
            shift < 32 &&
            rn == un + limbs + 1 &&
            rn <= INT_MAX &&
            un + limbs <= INT_MAX &&
            cy == cy_val &&
            Zlength(l_in) == un &&
            list_within_bound(UINT_MOD, l_in) &&
            list_to_Z(UINT_MOD, l_in) == Zabs(z_eq) &&
            last(l_in, 1) >= 1 &&
            Zlength(l_out) == un &&
            list_within_bound(UINT_MOD, l_out) &&
            list_to_Z(UINT_MOD, l_out) + cy_val * Z::pow(UINT_MOD, un) ==
              Zabs(z_eq) * Z::pow(2, shift) &&
            u->_mp_size == size &&
            u->_mp_alloc == Z::max(rn, cap) &&
            u->_mp_d == rp &&
            rp == u->_mp_d &&
            UIntArray::undef_seg(rp, 0, limbs) *
            UIntArray::seg(rp + limbs * sizeof(unsigned int), 0, un, l_out) *
            UIntArray::undef_seg(rp, un + limbs, rn) *
            UIntArray::undef_seg(rp, rn, Z::max(rn, cap))
      */
      rp[rn - 1] = cy;
      rn -= (cy == 0);
    }
  else
    {
      /*@ Assert exists l size cap,
            r == r@pre &&
            u == u@pre &&
            r == u &&
            bits == bits@pre &&
            bits >= 0 &&
            mpz_mul_2exp_fits(z_eq, bits) &&
            same_sign(z_eq, size) &&
            Zabs(size) <= cap &&
            un == Zabs(size) &&
            un > 0 &&
            limbs == bits / 32 &&
            limbs >= 0 &&
            shift == bits % 32 &&
            shift == 0 &&
            rn == un + limbs &&
            rn <= INT_MAX &&
            un + limbs <= INT_MAX &&
            Zlength(l) == un &&
            list_within_bound(UINT_MOD, l) &&
            list_to_Z(UINT_MOD, l) == Zabs(z_eq) &&
            last(l, 1) >= 1 &&
            u->_mp_size == size &&
            u->_mp_alloc == Z::max(rn, cap) &&
            u->_mp_d == rp &&
            rp == u->_mp_d &&
            UIntArray::full(u->_mp_d, un, l) *
            UIntArray::undef_seg(u->_mp_d, un, un + limbs) *
            UIntArray::undef_seg(u->_mp_d, un + limbs, Z::max(rn, cap))
      */
      /*@ Given l size cap */
      mpn_copyd(rp + limbs, u->_mp_d, un)
        /*@ where (shifted) l = l, off = limbs */;
      /*@ Assert exists l size cap,
            r == r@pre &&
            u == u@pre &&
            r == u &&
            bits == bits@pre &&
            bits >= 0 &&
            mpz_mul_2exp_fits(z_eq, bits) &&
            same_sign(z_eq, size) &&
            Zabs(size) <= cap &&
            un == Zabs(size) &&
            un > 0 &&
            limbs == bits / 32 &&
            limbs >= 0 &&
            shift == bits % 32 &&
            shift == 0 &&
            rn == un + limbs &&
            rn <= INT_MAX &&
            un + limbs <= INT_MAX &&
            Zlength(l) == un &&
            list_within_bound(UINT_MOD, l) &&
            list_to_Z(UINT_MOD, l) == Zabs(z_eq) &&
            last(l, 1) >= 1 &&
            u->_mp_size == size &&
            u->_mp_alloc == Z::max(rn, cap) &&
            u->_mp_d == rp &&
            rp == u->_mp_d &&
            UIntArray::undef_seg(rp, 0, limbs) *
            UIntArray::seg(rp + limbs * sizeof(unsigned int), 0, un, sublist(0, un, l)) *
            UIntArray::undef_seg(rp, un + limbs, Z::max(rn, cap))
      */
    }

  mpn_zero(rp, limbs);

  r->_mp_size = (u->_mp_size < 0) ? - rn : rn;
}
