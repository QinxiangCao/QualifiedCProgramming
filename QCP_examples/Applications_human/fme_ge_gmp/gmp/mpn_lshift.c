#include "fme_ge_gmp/gmp/gmp_def.h"

unsigned int mpn_lshift(unsigned int *rp, unsigned int *up,
                        int n, unsigned int cnt)
/*@ nonalias
  With l_up
  Require rp != up &&
          n > 0 && n <= INT_MAX &&
          1 <= cnt && cnt < 32 &&
          Zlength(l_up) == n &&
          list_within_bound(UINT_MOD, l_up) &&
          UIntArray::undef_full(rp, n) *
          UIntArray::full(up, n, l_up)
  Ensure exists l_out,
          Zlength(l_out) == n &&
          list_within_bound(UINT_MOD, l_out) &&
          list_to_Z(UINT_MOD, l_out) + __return * Z::pow(UINT_MOD, n) ==
            list_to_Z(UINT_MOD, l_up) * Z::pow(2, cnt) &&
          UIntArray::full(rp, n, l_out) *
          UIntArray::full(up, n, l_up)
*/
/*@ inplace
  With l_up
  Require rp == up &&
          n > 0 && n <= INT_MAX &&
          1 <= cnt && cnt < 32 &&
          Zlength(l_up) == n &&
          list_within_bound(UINT_MOD, l_up) &&
          UIntArray::full(up, n, l_up)
  Ensure exists l_out,
          Zlength(l_out) == n &&
          list_within_bound(UINT_MOD, l_out) &&
          list_to_Z(UINT_MOD, l_out) + __return * Z::pow(UINT_MOD, n) ==
            list_to_Z(UINT_MOD, l_up) * Z::pow(2, cnt) &&
          UIntArray::full(rp, n, l_out)
*/
/*@ nonalias */
/*@ inplace */
{
  /*@ Assert rp == rp@pre && up == up@pre && n == n@pre && cnt == cnt@pre &&
              rp != up &&
              n > 0 && n <= INT_MAX &&
              1 <= cnt && cnt < 32 &&
              Zlength(l_up_nonalias) == n &&
              list_within_bound(UINT_MOD, l_up_nonalias) &&
              UIntArray::undef_full(rp, n) *
              UIntArray::full(up, n, l_up_nonalias) $ nonalias */
  /*@ Assert rp == rp@pre && up == up@pre && n == n@pre && cnt == cnt@pre &&
              rp == up &&
              n > 0 && n <= INT_MAX &&
              1 <= cnt && cnt < 32 &&
              Zlength(l_up_inplace) == n &&
              list_within_bound(UINT_MOD, l_up_inplace) &&
              UIntArray::full(up, n, l_up_inplace) $ inplace */
  /*@ Branch name
      nonalias: rp != up;
      inplace: rp == up
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

  /*@
    rp == rp@pre &&
    up == up@pre &&
    n == n@pre &&
    cnt == cnt@pre &&
    rp != up &&
    n > 0 &&
    Zlength(l_up_nonalias) == n &&
    UIntArray::undef_full(rp, n) *
    UIntArray::full(up, n, l_up_nonalias)
    $ nonalias
    which implies
    rp == rp@pre &&
    up == up@pre &&
    n == n@pre &&
    cnt == cnt@pre &&
    rp != up &&
    n > 0 &&
    Zlength(l_up_nonalias) == n &&
    UIntArray::undef_seg(rp, 0, n) *
    UIntArray::seg(rp, n, n, nil) *
    UIntArray::full(up, n, l_up_nonalias)
  */
  /*@
    rp == rp@pre &&
    up == up@pre &&
    n == n@pre &&
    cnt == cnt@pre &&
    rp == up &&
    n > 0 &&
    Zlength(l_up_inplace) == n &&
    UIntArray::full(up, n, l_up_inplace)
    $ inplace
    which implies
    rp == rp@pre &&
    up == up@pre &&
    n == n@pre &&
    cnt == cnt@pre &&
    rp == up &&
    n > 0 &&
    Zlength(l_up_inplace) == n &&
    UIntArray::seg(up, 0, n, sublist(0, n, l_up_inplace)) *
    UIntArray::seg(up, n, n, nil)
  */
  /*@ Assert exists l_done,
        rp == rp@pre &&
        up == up@pre &&
        n == n@pre &&
        cnt == cnt@pre &&
        tnc == 32 - cnt@pre &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        0 <= low_limb &&
        low_limb <= UINT_MAX &&
        i == n@pre - 1 &&
        low_limb == Znth(i, l_up_nonalias, 0) &&
        0 <= i &&
        i < n@pre &&
        Zlength(l_up_nonalias) == n@pre &&
        l_done == nil &&
        Zlength(l_done) == n@pre - (i + 1) &&
        list_within_bound(UINT_MOD, l_up_nonalias) &&
        list_within_bound(UINT_MOD, l_done) &&
        retval == Znth(n@pre - 1, l_up_nonalias, 0) / Z::pow(2, tnc) &&
        high_limb == unsigned_last_nbits(Znth(i, l_up_nonalias, 0) * Z::pow(2, cnt@pre), 32) &&
        high_limb + list_to_Z(UINT_MOD, l_done) * UINT_MOD +
          retval * Z::pow(UINT_MOD, n@pre - i) ==
          list_to_Z(UINT_MOD, sublist(i, n@pre, l_up_nonalias)) * Z::pow(2, cnt@pre) &&
        rp@pre != up@pre &&
        UIntArray::undef_seg(rp@pre, 0, i + 1) *
        UIntArray::seg(rp@pre, i + 1, n@pre, l_done) *
        UIntArray::full(up@pre, n@pre, l_up_nonalias) $ nonalias */
  /*@ Assert exists l_done,
        rp == rp@pre &&
        up == up@pre &&
        n == n@pre &&
        cnt == cnt@pre &&
        tnc == 32 - cnt@pre &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        0 <= low_limb &&
        low_limb <= UINT_MAX &&
        i == n@pre - 1 &&
        low_limb == Znth(i, l_up_inplace, 0) &&
        0 <= i &&
        i < n@pre &&
        Zlength(l_up_inplace) == n@pre &&
        l_done == nil &&
        Zlength(l_done) == n@pre - (i + 1) &&
        list_within_bound(UINT_MOD, l_up_inplace) &&
        list_within_bound(UINT_MOD, l_done) &&
        retval == Znth(n@pre - 1, l_up_inplace, 0) / Z::pow(2, tnc) &&
        high_limb == unsigned_last_nbits(Znth(i, l_up_inplace, 0) * Z::pow(2, cnt@pre), 32) &&
        high_limb + list_to_Z(UINT_MOD, l_done) * UINT_MOD +
          retval * Z::pow(UINT_MOD, n@pre - i) ==
          list_to_Z(UINT_MOD, sublist(i, n@pre, l_up_inplace)) * Z::pow(2, cnt@pre) &&
        rp@pre == up@pre &&
        UIntArray::seg(up@pre, 0, i + 1, sublist(0, i + 1, l_up_inplace)) *
        UIntArray::seg(up@pre, i + 1, n@pre, l_done) $ inplace */
  /*@ Branch name
      nonalias: rp != up;
      inplace: rp == up
  */

  /*@ Inv
        nonalias_inv: exists l_done,
          rp == rp@pre &&
          up == up@pre &&
          n == n@pre &&
          cnt == cnt@pre &&
          tnc == 32 - cnt@pre &&
          1 <= cnt@pre &&
          cnt@pre < 32 &&
          0 <= low_limb &&
          low_limb <= UINT_MAX &&
          low_limb == Znth(i, l_up_nonalias, 0) &&
          0 <= i &&
          i < n@pre &&
          Zlength(l_up_nonalias) == n@pre &&
          Zlength(l_done) == n@pre - (i + 1) &&
          list_within_bound(UINT_MOD, l_up_nonalias) &&
          list_within_bound(UINT_MOD, l_done) &&
          retval == Znth(n@pre - 1, l_up_nonalias, 0) / Z::pow(2, tnc) &&
          high_limb == unsigned_last_nbits(Znth(i, l_up_nonalias, 0) * Z::pow(2, cnt@pre), 32) &&
          high_limb + list_to_Z(UINT_MOD, l_done) * UINT_MOD +
            retval * Z::pow(UINT_MOD, n@pre - i) ==
            list_to_Z(UINT_MOD, sublist(i, n@pre, l_up_nonalias)) * Z::pow(2, cnt@pre) &&
          rp@pre != up@pre &&
          UIntArray::undef_seg(rp@pre, 0, i + 1) *
          UIntArray::seg(rp@pre, i + 1, n@pre, l_done) *
          UIntArray::full(up@pre, n@pre, l_up_nonalias);
        inplace_inv: exists l_done,
          rp == rp@pre &&
          up == up@pre &&
          n == n@pre &&
          cnt == cnt@pre &&
          tnc == 32 - cnt@pre &&
          1 <= cnt@pre &&
          cnt@pre < 32 &&
          0 <= low_limb &&
          low_limb <= UINT_MAX &&
          low_limb == Znth(i, l_up_inplace, 0) &&
          0 <= i &&
          i < n@pre &&
          Zlength(l_up_inplace) == n@pre &&
          Zlength(l_done) == n@pre - (i + 1) &&
          list_within_bound(UINT_MOD, l_up_inplace) &&
          list_within_bound(UINT_MOD, l_done) &&
          retval == Znth(n@pre - 1, l_up_inplace, 0) / Z::pow(2, tnc) &&
          high_limb == unsigned_last_nbits(Znth(i, l_up_inplace, 0) * Z::pow(2, cnt@pre), 32) &&
          high_limb + list_to_Z(UINT_MOD, l_done) * UINT_MOD +
            retval * Z::pow(UINT_MOD, n@pre - i) ==
            list_to_Z(UINT_MOD, sublist(i, n@pre, l_up_inplace)) * Z::pow(2, cnt@pre) &&
          rp@pre == up@pre &&
          UIntArray::seg(up@pre, 0, i + 1, sublist(0, i + 1, l_up_inplace)) *
          UIntArray::seg(up@pre, i + 1, n@pre, l_done)
        with
          nonalias ==> nonalias_inv
          inplace ==> inplace_inv
  */
  while (i > 0) {
    i = i - 1;
    low_limb = up[i];
    /*@ Assert exists l_done,
        rp == rp@pre &&
        up == up@pre &&
        n == n@pre &&
        cnt == cnt@pre &&
        tnc == 32 - cnt@pre &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        0 <= low_limb &&
        low_limb <= UINT_MAX &&
        low_limb == Znth(i, l_up_nonalias, 0) &&
        0 <= i &&
        i + 1 < n@pre &&
        Zlength(l_up_nonalias) == n@pre &&
        Zlength(l_done) == n@pre - (i + 2) &&
        list_within_bound(UINT_MOD, l_up_nonalias) &&
        list_within_bound(UINT_MOD, l_done) &&
        retval == Znth(n@pre - 1, l_up_nonalias, 0) / Z::pow(2, tnc) &&
        high_limb == unsigned_last_nbits(Znth(i + 1, l_up_nonalias, 0) * Z::pow(2, cnt@pre), 32) &&
        high_limb + list_to_Z(UINT_MOD, l_done) * UINT_MOD +
          retval * Z::pow(UINT_MOD, n@pre - (i + 1)) ==
          list_to_Z(UINT_MOD, sublist(i + 1, n@pre, l_up_nonalias)) * Z::pow(2, cnt@pre) &&
        rp@pre != up@pre &&
        UIntArray::undef_seg(rp@pre, 0, i + 2) *
        UIntArray::seg(rp@pre, i + 2, n@pre, l_done) *
        UIntArray::full(up@pre, n@pre, l_up_nonalias) $ nonalias_inv */
    /*@ Assert exists l_done,
        rp == rp@pre &&
        up == up@pre &&
        n == n@pre &&
        cnt == cnt@pre &&
        tnc == 32 - cnt@pre &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        0 <= low_limb &&
        low_limb <= UINT_MAX &&
        low_limb == Znth(i, l_up_inplace, 0) &&
        0 <= i &&
        i + 1 < n@pre &&
        Zlength(l_up_inplace) == n@pre &&
        Zlength(l_done) == n@pre - (i + 2) &&
        list_within_bound(UINT_MOD, l_up_inplace) &&
        list_within_bound(UINT_MOD, l_done) &&
        retval == Znth(n@pre - 1, l_up_inplace, 0) / Z::pow(2, tnc) &&
        high_limb == unsigned_last_nbits(Znth(i + 1, l_up_inplace, 0) * Z::pow(2, cnt@pre), 32) &&
        high_limb + list_to_Z(UINT_MOD, l_done) * UINT_MOD +
          retval * Z::pow(UINT_MOD, n@pre - (i + 1)) ==
          list_to_Z(UINT_MOD, sublist(i + 1, n@pre, l_up_inplace)) * Z::pow(2, cnt@pre) &&
        rp@pre == up@pre &&
        UIntArray::seg(up@pre, 0, i + 2, sublist(0, i + 2, l_up_inplace)) *
        UIntArray::seg(up@pre, i + 2, n@pre, l_done) $ inplace_inv */
    /*@ Branch name
        nonalias_inv: rp != up;
        inplace_inv: rp == up
    */
    /*@
      rp == rp@pre &&
      i + 1 >= 0 &&
      i + 2 <= n@pre &&
      UIntArray::undef_seg(rp@pre, 0, i + 2)
      $ nonalias_inv
      which implies
      rp == rp@pre &&
      UIntArray::undef_seg(rp@pre, 0, i + 1) *
      UIntArray::undef_seg(rp@pre, i + 1, i + 2)
    */
    /*@
      rp == up &&
      up == up@pre &&
      i + 1 >= 0 &&
      i + 2 <= n@pre &&
      UIntArray::seg(up@pre, 0, i + 2, sublist(0, i + 2, l_up_inplace))
      $ inplace_inv
      which implies
      rp == up &&
      up == up@pre &&
      UIntArray::seg(up@pre, 0, i + 1, sublist(0, i + 1, l_up_inplace)) *
      UIntArray::seg(up@pre, i + 1, i + 2, sublist(i + 1, i + 2, l_up_inplace))
    */
    rp[i + 1] = high_limb | (low_limb >> tnc);
	    high_limb = low_limb << cnt;
	    /*@ nonalias_inv ==> nonalias_inv */
	    /*@ inplace_inv ==> inplace_inv */
	  }
  /*@ Assert exists l_done,
        rp == rp@pre &&
        up == up@pre &&
        n == n@pre &&
        cnt == cnt@pre &&
        tnc == 32 - cnt@pre &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        0 <= low_limb &&
        low_limb <= UINT_MAX &&
        i == 0 &&
        Zlength(l_up_nonalias) == n@pre &&
        Zlength(l_done) == n@pre - 1 &&
        list_within_bound(UINT_MOD, l_up_nonalias) &&
        list_within_bound(UINT_MOD, l_done) &&
        retval == Znth(n@pre - 1, l_up_nonalias, 0) / Z::pow(2, tnc) &&
        high_limb + list_to_Z(UINT_MOD, l_done) * UINT_MOD +
          retval * Z::pow(UINT_MOD, n@pre) ==
          list_to_Z(UINT_MOD, l_up_nonalias) * Z::pow(2, cnt@pre) &&
        rp@pre != up@pre &&
        UIntArray::undef_seg(rp@pre, 0, 1) *
        UIntArray::seg(rp@pre, 1, n@pre, l_done) *
        UIntArray::full(up@pre, n@pre, l_up_nonalias) $ nonalias_inv */
  /*@ Assert exists l_done,
        rp == rp@pre &&
        up == up@pre &&
        n == n@pre &&
        cnt == cnt@pre &&
        tnc == 32 - cnt@pre &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        0 <= low_limb &&
        low_limb <= UINT_MAX &&
        i == 0 &&
        Zlength(l_up_inplace) == n@pre &&
        Zlength(l_done) == n@pre - 1 &&
        list_within_bound(UINT_MOD, l_up_inplace) &&
        list_within_bound(UINT_MOD, l_done) &&
        retval == Znth(n@pre - 1, l_up_inplace, 0) / Z::pow(2, tnc) &&
        high_limb + list_to_Z(UINT_MOD, l_done) * UINT_MOD +
          retval * Z::pow(UINT_MOD, n@pre) ==
          list_to_Z(UINT_MOD, l_up_inplace) * Z::pow(2, cnt@pre) &&
        rp@pre == up@pre &&
        UIntArray::seg(up@pre, 0, 1, sublist(0, 1, l_up_inplace)) *
        UIntArray::seg(up@pre, 1, n@pre, l_done) $ inplace_inv */
  /*@ Branch name
      nonalias_inv: rp != up;
      inplace_inv: rp == up
  */
  /*@
    rp == rp@pre &&
    i == 0 &&
    UIntArray::undef_seg(rp@pre, 0, 1)
    $ nonalias_inv
    which implies
    rp == rp@pre &&
    i == 0 &&
    UIntArray::undef_seg(rp, 0, 1)
  */
  /*@
    rp == up &&
    up == up@pre &&
    i == 0 &&
    UIntArray::seg(up@pre, 0, 1, sublist(0, 1, l_up_inplace))
    $ inplace_inv
    which implies
    rp == up &&
    up == up@pre &&
    i == 0 &&
    UIntArray::seg(rp, 0, 1, sublist(0, 1, l_up_inplace))
  */
	  rp[0] = high_limb;
  return retval;
}
