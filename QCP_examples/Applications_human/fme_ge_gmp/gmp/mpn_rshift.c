#include "fme_ge_gmp/gmp/gmp_def.h"

unsigned int mpn_rshift(unsigned int *rp, unsigned int *up,
                        int n, unsigned int cnt)
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
          __return == unsigned_last_nbits(Znth(0, l_up, 0) * Z::pow(2, 32 - cnt), 32) &&
          list_to_Z(UINT_MOD, l_up) ==
            list_to_Z(UINT_MOD, l_out) * Z::pow(2, cnt) +
            __return / Z::pow(2, 32 - cnt) &&
          UIntArray::full(rp, n, l_out)
*/
/*@ inplace */
{
  /*@ Assert rp == rp@pre && up == up@pre && n == n@pre && cnt == cnt@pre &&
              rp == up &&
              n > 0 && n <= INT_MAX &&
              1 <= cnt && cnt < 32 &&
              Zlength(l_up) == n &&
              list_within_bound(UINT_MOD, l_up) &&
              UIntArray::full(up, n, l_up) */
  unsigned int high_limb;
  unsigned int low_limb;
  unsigned int tnc;
  unsigned int retval;
  int i;

  tnc = 32 - cnt;
  i = 0;
  high_limb = up[i];
  retval = high_limb << tnc;
  low_limb = high_limb >> cnt;

  /*@
    rp == up &&
    up == up@pre &&
    i == 0 &&
    n == n@pre &&
    n > 0 &&
    Zlength(l_up) == n &&
    UIntArray::full(up, n, l_up)
    which implies
    rp == up &&
    up == up@pre &&
    i == 0 &&
    n == n@pre &&
    n > 0 &&
    Zlength(l_up) == n &&
    UIntArray::seg(up, 0, 0, nil) *
    UIntArray::seg(up, 0, n, sublist(0, n, l_up))
  */
  /*@ Assert exists l_done,
        rp == rp@pre &&
        up == up@pre &&
        n == n@pre &&
        cnt == cnt@pre &&
        tnc == 32 - cnt@pre &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        i == 0 &&
        0 <= i &&
        i < n@pre &&
        Zlength(l_up) == n@pre &&
        l_done == nil &&
        Zlength(l_done) == i &&
        list_within_bound(UINT_MOD, l_up) &&
        list_within_bound(UINT_MOD, l_done) &&
        high_limb == Znth(i, l_up, 0) &&
        low_limb == Znth(i, l_up, 0) / Z::pow(2, cnt@pre) &&
        retval == unsigned_last_nbits(Znth(0, l_up, 0) * Z::pow(2, tnc), 32) &&
        list_to_Z(UINT_MOD, sublist(0, i + 1, l_up)) ==
          (list_to_Z(UINT_MOD, l_done) + low_limb * Z::pow(UINT_MOD, i)) *
            Z::pow(2, cnt@pre) +
          retval / Z::pow(2, tnc) &&
        rp@pre == up@pre &&
        UIntArray::seg(up@pre, 0, i, l_done) *
        UIntArray::seg(up@pre, i, n@pre, sublist(i, n@pre, l_up)) */

  /*@ Inv Assert
        exists l_done,
          rp == rp@pre &&
          up == up@pre &&
          n == n@pre &&
          cnt == cnt@pre &&
          tnc == 32 - cnt@pre &&
          1 <= cnt@pre &&
          cnt@pre < 32 &&
          0 <= i &&
          i < n@pre &&
          Zlength(l_up) == n@pre &&
          Zlength(l_done) == i &&
          list_within_bound(UINT_MOD, l_up) &&
          list_within_bound(UINT_MOD, l_done) &&
          high_limb == Znth(i, l_up, 0) &&
          low_limb == Znth(i, l_up, 0) / Z::pow(2, cnt@pre) &&
          retval == unsigned_last_nbits(Znth(0, l_up, 0) * Z::pow(2, tnc), 32) &&
          list_to_Z(UINT_MOD, sublist(0, i + 1, l_up)) ==
            (list_to_Z(UINT_MOD, l_done) + low_limb * Z::pow(UINT_MOD, i)) *
              Z::pow(2, cnt@pre) +
          retval / Z::pow(2, tnc) &&
          rp@pre == up@pre &&
          UIntArray::seg(up@pre, 0, i, l_done) *
          UIntArray::seg(up@pre, i, n@pre, sublist(i, n@pre, l_up))
  */
  while (i < n - 1) {
    i = i + 1;
    high_limb = up[i];
    /*@ Assert exists l_done,
        rp == rp@pre &&
        up == up@pre &&
        n == n@pre &&
        cnt == cnt@pre &&
        tnc == 32 - cnt@pre &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        1 <= i &&
        i < n@pre &&
        Zlength(l_up) == n@pre &&
        Zlength(l_done) == i - 1 &&
        list_within_bound(UINT_MOD, l_up) &&
        list_within_bound(UINT_MOD, l_done) &&
        high_limb == Znth(i, l_up, 0) &&
        low_limb == Znth(i - 1, l_up, 0) / Z::pow(2, cnt@pre) &&
        retval == unsigned_last_nbits(Znth(0, l_up, 0) * Z::pow(2, tnc), 32) &&
        list_to_Z(UINT_MOD, sublist(0, i, l_up)) ==
          (list_to_Z(UINT_MOD, l_done) + low_limb * Z::pow(UINT_MOD, i - 1)) *
            Z::pow(2, cnt@pre) +
          retval / Z::pow(2, tnc) &&
        rp@pre == up@pre &&
        UIntArray::seg(up@pre, 0, i - 1, l_done) *
        UIntArray::seg(up@pre, i - 1, n@pre, sublist(i - 1, n@pre, l_up)) */
    /*@
      rp == up &&
      up == up@pre &&
      1 <= i &&
      i < n@pre &&
      Zlength(l_up) == n@pre &&
      UIntArray::seg(up@pre, i - 1, n@pre, sublist(i - 1, n@pre, l_up))
      which implies
      rp == up &&
      up == up@pre &&
      Zlength(l_up) == n@pre &&
      UIntArray::seg(up@pre, i - 1, i, sublist(i - 1, i, l_up)) *
      UIntArray::seg(up@pre, i, n@pre, sublist(i, n@pre, l_up))
    */
    rp[i - 1] = low_limb | (high_limb << tnc);
    low_limb = high_limb >> cnt;
  }

  /*@ Assert exists l_done,
        rp == rp@pre &&
        up == up@pre &&
        n == n@pre &&
        cnt == cnt@pre &&
        tnc == 32 - cnt@pre &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        i == n@pre - 1 &&
        0 <= i &&
        i < n@pre &&
        Zlength(l_up) == n@pre &&
        Zlength(l_done) == n@pre - 1 &&
        list_within_bound(UINT_MOD, l_up) &&
        list_within_bound(UINT_MOD, l_done) &&
        high_limb == Znth(i, l_up, 0) &&
        low_limb == Znth(i, l_up, 0) / Z::pow(2, cnt@pre) &&
        retval == unsigned_last_nbits(Znth(0, l_up, 0) * Z::pow(2, tnc), 32) &&
        list_to_Z(UINT_MOD, sublist(0, n@pre, l_up)) ==
          (list_to_Z(UINT_MOD, l_done) + low_limb * Z::pow(UINT_MOD, i)) *
            Z::pow(2, cnt@pre) +
          retval / Z::pow(2, tnc) &&
        rp@pre == up@pre &&
        UIntArray::seg(up@pre, 0, i, l_done) *
        UIntArray::seg(up@pre, i, n@pre, sublist(i, n@pre, l_up)) */
  /*@
    rp == up &&
    up == up@pre &&
    0 <= i &&
    i < n@pre &&
    Zlength(l_up) == n@pre &&
    UIntArray::seg(up@pre, i, n@pre, sublist(i, n@pre, l_up))
    which implies
    rp == up &&
    up == up@pre &&
    Zlength(l_up) == n@pre &&
    UIntArray::seg(up@pre, i, i + 1, sublist(i, i + 1, l_up)) *
    UIntArray::seg(up@pre, i + 1, n@pre, sublist(i + 1, n@pre, l_up))
  */
  rp[i] = low_limb;
  return retval;
}
