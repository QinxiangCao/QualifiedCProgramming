#include "gmp/minigmp/gmp_def.h"

int
mpn_normalized_size(unsigned int *xp, int n)
/*@ plain
  With val
  Require
    0 <= n &&
    mpd_store_Z(UINT_MOD, xp, val, n)
  Ensure
    0 <= __return && __return <= n &&
    mpd_store_Z_compact(UINT_MOD, xp, val, __return) *
    UIntArray::undef_seg(xp, __return, n)
*/
/*@ read0
  With val
  Require
    n > 0 &&
    mpd_store_Z(UINT_MOD, xp, val, n)
  Ensure
    0 <= __return && __return <= n &&
    mpd_store_Z_compact_read0(xp, val, __return) *
    UIntArray::undef_seg(xp, Zmax(__return, 1), n)
*/
{
  /*@
    mpd_store_Z(UINT_MOD, xp, val_plain, n) $ plain
    which implies
    exists lp,
      list_to_Z(UINT_MOD, lp) == val_plain &&
      list_within_bound(UINT_MOD, lp) &&
      Zlength(lp) == n &&
      UIntArray::full(xp, n, lp)
  */
  /*@ Given lp $ plain */
  /*@ n <= INT_MAX by local */
  /*@
    mpd_store_Z(UINT_MOD, xp, val_read0, n) $ read0
    which implies
    exists l,
      list_to_Z(UINT_MOD, l) == val_read0 &&
      list_within_bound(UINT_MOD, l) &&
      Zlength(l) == n &&
      UIntArray::full(xp, n, l)
  */
  /*@ Given l $ read0 */
  /*@ Inv
    plain:
      n >= 0 && n <= n@pre &&
      list_to_Z(UINT_MOD, sublist(0, n, lp)) == val_plain &&
      UIntArray::full(xp@pre, n, sublist(0, n, lp)) *
      UIntArray::undef_seg(xp@pre, n, n@pre);
    read0:
      xp == xp@pre &&
      n@pre > 0 &&
      n >= 0 &&
      n <= n@pre &&
      normalized_size_read0_guard(n, l) &&
      list_to_Z(UINT_MOD, sublist(0, n, l)) == val_read0 &&
      list_within_bound(UINT_MOD, l) &&
      Zlength(l) == n@pre &&
      UIntArray::full(xp@pre, n@pre, l)
    with
      plain ==> plain
      read0 ==> read0
  */
  while (n > 0 && xp[n-1] == 0)
    --n;

  /*@ Assert
      xp == xp@pre &&
      n@pre > 0 &&
      n >= 0 &&
      n <= n@pre &&
      normalized_size_read0_guard(n, l) &&
      list_to_Z(UINT_MOD, sublist(0, n, l)) == val_read0 &&
      list_within_bound(UINT_MOD, l) &&
      Zlength(l) == n@pre &&
      last(sublist(0, n, l), 1) >= 1 &&
      UIntArray::full(xp@pre, n@pre, l)
      $ read0
  */
  return n;
}
