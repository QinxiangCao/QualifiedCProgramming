#include "gmp/minigmp/gmp_def.h"

unsigned int mpn_rshift(unsigned int *rp, unsigned int *up,
                        int n, unsigned int cnt)
/*@ inplace <= shifted
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
*/;

unsigned int
mpn_rshift(unsigned int *rp, unsigned int *up, int n, unsigned int cnt)
/*@ shifted
  With l_up off
  Require
    n > 0 && n + off <= INT_MAX && off >= 0 &&
    1 <= cnt && cnt < 32 &&
    up == rp + off * sizeof(unsigned int) &&
    Zlength(l_up) == n + off &&
    list_within_bound(UINT_MOD, l_up) &&
    UIntArray::full(rp, n + off, l_up)
  Ensure exists l_out,
    Zlength(l_out) == n &&
    list_within_bound(UINT_MOD, l_out) &&
    __return == unsigned_last_nbits(Znth(off, l_up, 0) * Z::pow(2, 32 - cnt), 32) &&
    list_to_Z(UINT_MOD, sublist(off, off + n, l_up)) ==
      list_to_Z(UINT_MOD, l_out) * Z::pow(2, cnt) +
      __return / Z::pow(2, 32 - cnt) &&
    UIntArray::seg(rp, 0, n, l_out) *
    UIntArray::seg(rp, n, n + off, sublist(n, n + off, l_up))
*/
{
  unsigned int high_limb;
  unsigned int low_limb;
  unsigned int tnc;
  unsigned int retval;

  tnc = 32 - cnt;
  /*@
    rp == rp@pre &&
    up == up@pre &&
    n == n@pre &&
    cnt == cnt@pre &&
    off >= 0 &&
    n > 0 &&
    n + off <= INT_MAX &&
    up == rp + off * sizeof(unsigned int) &&
    Zlength(l_up) == n + off &&
    UIntArray::full(rp, n + off, l_up)
    which implies
    rp == rp@pre &&
    up == up@pre &&
    n == n@pre &&
    cnt == cnt@pre &&
    up == rp + off * sizeof(unsigned int) &&
    UIntArray::seg(rp, 0, off, sublist(0, off, l_up)) *
    UIntArray::seg(up, 0, 1, sublist(off, off + 1, l_up)) *
    UIntArray::seg(rp, off + 1, n + off, sublist(off + 1, n + off, l_up))
  */
  high_limb = up[0];
  up++;
  retval = high_limb << tnc;
  low_limb = high_limb >> cnt;
  --n;

  /*@ Assert exists i l_done,
        rp == rp@pre &&
        up == up@pre + (i + 1) * sizeof(unsigned int) &&
        n == n@pre - i - 1 &&
        cnt == cnt@pre &&
        off >= 0 &&
        n@pre > 0 &&
        n@pre + off <= INT_MAX &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        tnc == 32 - cnt@pre &&
        up@pre == rp@pre + off * sizeof(unsigned int) &&
        i == 0 &&
        0 <= i &&
        i < n@pre &&
        Zlength(l_up) == n@pre + off &&
        l_done == nil &&
        Zlength(l_done) == i &&
        list_within_bound(UINT_MOD, l_up) &&
        list_within_bound(UINT_MOD, l_done) &&
        high_limb == Znth(off + i, l_up, 0) &&
        low_limb == Znth(off + i, l_up, 0) / Z::pow(2, cnt@pre) &&
        retval == unsigned_last_nbits(Znth(off, l_up, 0) * Z::pow(2, tnc), 32) &&
        list_to_Z(UINT_MOD, sublist(off, off + i + 1, l_up)) ==
          (list_to_Z(UINT_MOD, l_done) + low_limb * Z::pow(UINT_MOD, i)) *
            Z::pow(2, cnt@pre) +
          retval / Z::pow(2, tnc) &&
        UIntArray::seg(rp@pre, 0, i, l_done) *
        UIntArray::seg(rp@pre, i, n@pre + off, sublist(i, n@pre + off, l_up)) */

  /*@ Inv Assert
        exists i l_done,
          rp == rp@pre + i * sizeof(unsigned int) &&
          up == up@pre + (i + 1) * sizeof(unsigned int) &&
          n == n@pre - i - 1 &&
          cnt == cnt@pre &&
          off >= 0 &&
          n@pre > 0 &&
          n@pre + off <= INT_MAX &&
          1 <= cnt@pre &&
          cnt@pre < 32 &&
          tnc == 32 - cnt@pre &&
          up@pre == rp@pre + off * sizeof(unsigned int) &&
          0 <= i &&
          i < n@pre &&
          Zlength(l_up) == n@pre + off &&
          Zlength(l_done) == i &&
          list_within_bound(UINT_MOD, l_up) &&
          list_within_bound(UINT_MOD, l_done) &&
          high_limb == Znth(off + i, l_up, 0) &&
          low_limb == Znth(off + i, l_up, 0) / Z::pow(2, cnt@pre) &&
          retval == unsigned_last_nbits(Znth(off, l_up, 0) * Z::pow(2, tnc), 32) &&
          list_to_Z(UINT_MOD, sublist(off, off + i + 1, l_up)) ==
            (list_to_Z(UINT_MOD, l_done) + low_limb * Z::pow(UINT_MOD, i)) *
              Z::pow(2, cnt@pre) +
            retval / Z::pow(2, tnc) &&
          UIntArray::seg(rp@pre, 0, i, l_done) *
          UIntArray::seg(rp@pre, i, n@pre + off, sublist(i, n@pre + off, l_up))
  */
  while (n != 0)
    {
      /*@ Assert exists i l_done,
        rp == rp@pre + i * sizeof(unsigned int) &&
        up == up@pre + (i + 1) * sizeof(unsigned int) &&
        up@pre == rp@pre + off * sizeof(unsigned int) &&
        n == n@pre - i - 1 &&
        n != 0 &&
        off >= 0 &&
        n@pre > 0 &&
        n@pre + off <= INT_MAX &&
        cnt == cnt@pre &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        tnc == 32 - cnt@pre &&
        0 <= i &&
        i + 1 < n@pre &&
        Zlength(l_up) == n@pre + off &&
        Zlength(l_done) == i &&
        list_within_bound(UINT_MOD, l_up) &&
        list_within_bound(UINT_MOD, l_done) &&
        high_limb == Znth(off + i, l_up, 0) &&
        low_limb == Znth(off + i, l_up, 0) / Z::pow(2, cnt@pre) &&
        retval == unsigned_last_nbits(Znth(off, l_up, 0) * Z::pow(2, tnc), 32) &&
        list_to_Z(UINT_MOD, sublist(off, off + i + 1, l_up)) ==
          (list_to_Z(UINT_MOD, l_done) + low_limb * Z::pow(UINT_MOD, i)) *
            Z::pow(2, cnt@pre) +
          retval / Z::pow(2, tnc) &&
        UIntArray::seg(rp@pre, 0, i, l_done) *
        UIntArray::seg(rp, 0, 1, sublist(i, i + 1, l_up)) *
        UIntArray::seg(rp@pre, i + 1, off + i + 1, sublist(i + 1, off + i + 1, l_up)) *
        UIntArray::seg(up, 0, 1, sublist(off + i + 1, off + i + 2, l_up)) *
        UIntArray::seg(rp@pre, off + i + 2, n@pre + off, sublist(off + i + 2, n@pre + off, l_up))
      */
      high_limb = up[0];
      up++;
      rp[0] = low_limb | (high_limb << tnc);
      rp++;
      low_limb = high_limb >> cnt;
      --n;
      /*@ Assert exists i l_done,
        rp == rp@pre + i * sizeof(unsigned int) &&
        up == up@pre + (i + 1) * sizeof(unsigned int) &&
        n == n@pre - i - 1 &&
        cnt == cnt@pre &&
        off >= 0 &&
        n@pre > 0 &&
        n@pre + off <= INT_MAX &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        tnc == 32 - cnt@pre &&
        up@pre == rp@pre + off * sizeof(unsigned int) &&
        0 <= i &&
        i < n@pre &&
        Zlength(l_up) == n@pre + off &&
        Zlength(l_done) == i &&
        list_within_bound(UINT_MOD, l_up) &&
        list_within_bound(UINT_MOD, l_done) &&
        high_limb == Znth(off + i, l_up, 0) &&
        low_limb == Znth(off + i, l_up, 0) / Z::pow(2, cnt@pre) &&
        retval == unsigned_last_nbits(Znth(off, l_up, 0) * Z::pow(2, tnc), 32) &&
        list_to_Z(UINT_MOD, sublist(off, off + i + 1, l_up)) ==
          (list_to_Z(UINT_MOD, l_done) + low_limb * Z::pow(UINT_MOD, i)) *
            Z::pow(2, cnt@pre) +
          retval / Z::pow(2, tnc) &&
        UIntArray::seg(rp@pre, 0, i, l_done) *
        UIntArray::seg(rp@pre, i, n@pre + off, sublist(i, n@pre + off, l_up)) */
    }
  /*@ Assert exists i l_done,
      rp == rp@pre + i * sizeof(unsigned int) &&
      up == up@pre + (i + 1) * sizeof(unsigned int) &&
      n == 0 &&
      n == n@pre - i - 1 &&
      cnt == cnt@pre &&
      off >= 0 &&
      n@pre > 0 &&
      n@pre + off <= INT_MAX &&
      1 <= cnt@pre &&
      cnt@pre < 32 &&
      tnc == 32 - cnt@pre &&
      up@pre == rp@pre + off * sizeof(unsigned int) &&
      0 <= i &&
      i < n@pre &&
      Zlength(l_up) == n@pre + off &&
      Zlength(l_done) == i &&
      list_within_bound(UINT_MOD, l_up) &&
      list_within_bound(UINT_MOD, l_done) &&
      high_limb == Znth(off + i, l_up, 0) &&
      low_limb == Znth(off + i, l_up, 0) / Z::pow(2, cnt@pre) &&
      retval == unsigned_last_nbits(Znth(off, l_up, 0) * Z::pow(2, tnc), 32) &&
      list_to_Z(UINT_MOD, sublist(off, off + i + 1, l_up)) ==
        (list_to_Z(UINT_MOD, l_done) + low_limb * Z::pow(UINT_MOD, i)) *
          Z::pow(2, cnt@pre) +
        retval / Z::pow(2, tnc) &&
      UIntArray::seg(rp@pre, 0, i, l_done) *
      UIntArray::seg(rp, 0, 1, sublist(i, i + 1, l_up)) *
      UIntArray::seg(rp@pre, i + 1, n@pre + off, sublist(i + 1, n@pre + off, l_up))
  */
  rp[0] = low_limb;
  /*@ Assert exists l_out,
        rp == rp@pre + (n@pre - 1) * sizeof(unsigned int) &&
        up == up@pre + n@pre * sizeof(unsigned int) &&
        n == 0 &&
        cnt == cnt@pre &&
        off >= 0 &&
        n@pre > 0 &&
        n@pre + off <= INT_MAX &&
        1 <= cnt@pre &&
        cnt@pre < 32 &&
        tnc == 32 - cnt@pre &&
        up@pre == rp@pre + off * sizeof(unsigned int) &&
        Zlength(l_up) == n@pre + off &&
        Zlength(l_out) == n@pre &&
        list_within_bound(UINT_MOD, l_up) &&
        list_within_bound(UINT_MOD, l_out) &&
        retval == unsigned_last_nbits(Znth(off, l_up, 0) * Z::pow(2, tnc), 32) &&
        list_to_Z(UINT_MOD, sublist(off, off + n@pre, l_up)) ==
          list_to_Z(UINT_MOD, l_out) * Z::pow(2, cnt@pre) +
          retval / Z::pow(2, tnc) &&
        has_permission(&high_limb) *
        has_permission(&low_limb) *
        UIntArray::seg(rp@pre, 0, n@pre, l_out) *
        UIntArray::seg(rp@pre, n@pre, n@pre + off, sublist(n@pre, n@pre + off, l_up)) */

  return retval;
}
