#include "gmp/minigmp/gmp_def.h"

void
mpn_copyi(unsigned int *d, unsigned int *s, int n)
/*@ shifted
  With l off
  Require
    n >= 0 && n + off <= INT_MAX && off >= 0 &&
    s == d + off * sizeof(unsigned int) &&
    Zlength(l) == n + off &&
    list_within_bound(UINT_MOD, l) &&
    UIntArray::full(d, n + off, l)
  Ensure
    UIntArray::seg(d, 0, n, sublist(off, off + n, l)) *
    UIntArray::seg(d, n, n + off, sublist(n, n + off, l))
*/
/*@ non_alias
  With val
  Require
    mpd_store_Z(UINT_MOD, s, val, n) *
    UIntArray::undef_full(d, n)
  Ensure
    mpd_store_Z(UINT_MOD, s, val, n) *
    mpd_store_Z(UINT_MOD, d, val, n)
*/
{
  /*@
    mpd_store_Z(UINT_MOD, s, val_non_alias, n) $ non_alias
    which implies
    exists l,
      Zlength(l) == n &&
      list_to_Z(UINT_MOD, l) == val_non_alias &&
      list_within_bound(UINT_MOD, l) &&
      UIntArray::full(s, n, l)
  */
  /*@ Given l $ non_alias */
  int i;
  /*@ Destruct $ shifted with
        off_zero: off_shifted == 0;
        off_pos: off_shifted > 0
  */
  /*@ Assert
        d == d@pre &&
        s == s@pre &&
        n == n@pre &&
        off_shifted == 0 &&
        n >= 0 &&
        n + off_shifted <= INT_MAX &&
        s == d + off_shifted * sizeof(unsigned int) &&
        Zlength(l_shifted) == n + off_shifted &&
        list_within_bound(UINT_MOD, l_shifted) &&
        has_permission(&i) *
        UIntArray::seg(d, 0, 0, nil) *
        UIntArray::seg(d, 0, n, sublist(0, n, l_shifted)) $ off_zero
  */
  /*@ Assert
        d == d@pre &&
        s == s@pre &&
        n == n@pre &&
        off_shifted > 0 &&
        n >= 0 &&
        n + off_shifted <= INT_MAX &&
        s == d + off_shifted * sizeof(unsigned int) &&
        Zlength(l_shifted) == n + off_shifted &&
        list_within_bound(UINT_MOD, l_shifted) &&
        has_permission(&i) *
        UIntArray::seg(d, 0, 0, nil) *
        UIntArray::seg(d, 0, n + off_shifted, sublist(0, n + off_shifted, l_shifted)) $ off_pos
  */
  /*@ Inv
        non_alias:
          0 <= i && i <= n@pre &&
          UIntArray::full(d@pre, i, sublist(0, i, l)) *
          UIntArray::undef_seg(d@pre, i, n@pre);
        off_zero:
          d == d@pre &&
          s == s@pre &&
          n == n@pre &&
          off_shifted == 0 &&
          n >= 0 &&
          s == d &&
          0 <= i &&
          i <= n@pre &&
          Zlength(l_shifted) == n@pre &&
          list_within_bound(UINT_MOD, l_shifted) &&
          UIntArray::seg(d@pre, 0, i, sublist(0, i, l_shifted)) *
          UIntArray::seg(d@pre, i, n@pre, sublist(i, n@pre, l_shifted));
        off_pos:
          d == d@pre &&
          s == s@pre &&
          n == n@pre &&
          off_shifted > 0 &&
          n >= 0 &&
          n + off_shifted <= INT_MAX &&
          s == d + off_shifted * sizeof(unsigned int) &&
          0 <= i &&
          i <= n@pre &&
          Zlength(l_shifted) == n@pre + off_shifted &&
          list_within_bound(UINT_MOD, l_shifted) &&
          UIntArray::seg(d@pre, 0, i, sublist(off_shifted, off_shifted + i, l_shifted)) *
          UIntArray::seg(d@pre, i, n@pre + off_shifted, sublist(i, n@pre + off_shifted, l_shifted))
  */
  for (i = 0; i < n; i++) {
    /*@
      d == d@pre &&
      s == d &&
      0 <= i &&
      i < n@pre &&
      Zlength(l_shifted) == n@pre &&
      UIntArray::seg(d@pre, i, n@pre, sublist(i, n@pre, l_shifted))
      $ off_zero
      which implies
      d == d@pre &&
      s == d &&
      UIntArray::seg(d@pre, i, i + 1, sublist(i, i + 1, l_shifted)) *
      UIntArray::seg(d@pre, i + 1, n@pre, sublist(i + 1, n@pre, l_shifted))
    */
    /*@
      d == d@pre &&
      s == s@pre &&
      s == d + off_shifted * sizeof(unsigned int) &&
      off_shifted > 0 &&
      0 <= i &&
      i < n@pre &&
      Zlength(l_shifted) == n@pre + off_shifted &&
      UIntArray::seg(d@pre, i, n@pre + off_shifted, sublist(i, n@pre + off_shifted, l_shifted))
      $ off_pos
      which implies
      d == d@pre &&
      s == s@pre &&
      s == d + off_shifted * sizeof(unsigned int) &&
      UIntArray::seg(d@pre, i, i + 1, sublist(i, i + 1, l_shifted)) *
      UIntArray::seg(d@pre, i + 1, off_shifted + i, sublist(i + 1, off_shifted + i, l_shifted)) *
      UIntArray::seg(s@pre, i, i + 1, sublist(off_shifted + i, off_shifted + i + 1, l_shifted)) *
      UIntArray::seg(d@pre, off_shifted + i + 1, n@pre + off_shifted, sublist(off_shifted + i + 1, n@pre + off_shifted, l_shifted))
    */
    d[i] = s[i];
    /*@ off_zero ==> off_zero */
    /*@ off_pos ==> off_pos */
  }
}
