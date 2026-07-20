#include "verification_stdlib.h"
#include "verification_list.h"
#include "array2_def.h"

/*@ include strategies "undef_uint_array.strategies" */

/*@ Extern Coq
      (sum : list Z -> Z)
      (sublist : {A} -> Z -> Z -> list A -> list A)
      (StoneMassesBounded : list Z -> Z -> Prop)
      (StoneMinimumCost : list Z -> Z -> Z -> Prop)
      (StonePrefixProgress : list Z -> list Z -> Z -> Z -> Prop)
      (StonePrefixDone : list Z -> list Z -> Z -> Prop)
      (StoneTableShape : list (list Z) -> Z -> Prop)
      (StoneZeroRows : list (list Z) -> Z -> Z -> Prop)
      (StoneZeroProgress : list (list Z) -> Z -> Z -> Z -> Prop)
      (StoneLenDone : list Z -> list (list Z) -> Z -> Z -> Prop)
      (StoneLeftProgress : list Z -> list (list Z) -> Z -> Z -> Z -> Prop)
      (StoneSplitCandidate : list Z -> list (list Z) -> Z -> Z -> Z -> Z -> Prop)
      (StoneSplitProgress : list Z -> list (list Z) -> Z -> Z -> Z -> Z -> Z -> Prop)
      (StoneIntervalMin : list Z -> Z -> Z -> Z -> Prop)
      (StoneUpdatedCell : list Z -> list (list Z) -> list (list Z) -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_lib */

/*
 * Minimum cost of merging adjacent stone piles by interval dynamic
 * programming.  The verified range is deliberately limited to n <= 8.
 */
int mergingStones(int *stones, int n, int *prefix, int *dp)
/*@ With (stones_l : list Z) (dp_init : list (list Z))
    Require
      1 <= n && n <= 8 &&
      Zlength(stones_l) == n &&
      StoneMassesBounded(stones_l, n) &&
      StoneTableShape(dp_init, n) &&
      IntArray::full(stones, n, stones_l) *
      IntArray::undef_full(prefix, n + 1) *
      IntArray2::full(dp, n, n, dp_init)
    Ensure
      exists prefix_l dp_l,
      StonePrefixDone(stones_l, prefix_l, n) &&
      StoneLenDone(stones_l, dp_l, n, n + 1) &&
      StoneMinimumCost(stones_l, n, __return) &&
      0 <= __return && __return <= 56000 &&
      IntArray::full(stones, n, stones_l) *
      IntArray::full(prefix, n + 1, prefix_l) *
      IntArray2::full(dp, n, n, dp_l)
 */
{
  int width = n;

  prefix[0] = 0;
  /*@ Assert
      stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
      n == n@pre && width == n@pre &&
      1 <= n@pre && n@pre <= 8 &&
      Zlength(stones_l) == n@pre &&
      StoneMassesBounded(stones_l, n@pre) &&
      StoneTableShape(dp_init, n@pre) &&
      StonePrefixProgress(stones_l, cons(0, nil), n@pre, 0) &&
      IntArray::full(stones, n@pre, stones_l) *
      IntArray::seg(prefix, 0, 1, cons(0, nil)) *
      IntArray::undef_seg(prefix, 1, n@pre + 1) *
      IntArray2::full(dp, n@pre, n@pre, dp_init)
   */
  /*@ Inv Assert
      exists prefix_l,
      stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
      n == n@pre && width == n@pre &&
      1 <= n@pre && n@pre <= 8 &&
      Zlength(stones_l) == n@pre &&
      0 <= i && i <= n@pre &&
      StoneMassesBounded(stones_l, n@pre) &&
      StoneTableShape(dp_init, n@pre) &&
      StonePrefixProgress(stones_l, prefix_l, n@pre, i) &&
      IntArray::full(stones, n@pre, stones_l) *
      IntArray::seg(prefix, 0, i + 1, prefix_l) *
      IntArray::undef_seg(prefix, i + 1, n@pre + 1) *
      IntArray2::full(dp, n@pre, n@pre, dp_init)
   */
  for (int i = 0; i < n; ++i) {
    /*@ Assert
        exists prefix_l,
        stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
        n == n@pre && width == n@pre &&
        1 <= n@pre && n@pre <= 8 &&
        0 <= i && i < n@pre &&
        Zlength(stones_l) == n@pre &&
        StoneMassesBounded(stones_l, n@pre) &&
        StoneTableShape(dp_init, n@pre) &&
        StonePrefixProgress(stones_l, prefix_l, n@pre, i) &&
        0 <= prefix_l[i] && prefix_l[i] <= 8000 &&
        1 <= stones_l[i] && stones_l[i] <= 1000 &&
        IntArray::full(stones, n@pre, stones_l) *
        IntArray::seg(prefix, 0, i + 1, prefix_l) *
        IntArray::undef_seg(prefix, i + 1, n@pre + 1) *
        IntArray2::full(dp, n@pre, n@pre, dp_init)
     */
    prefix[i + 1] = prefix[i] + stones[i];
  }

  /*@ Assert
      exists prefix_l,
      stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
      n == n@pre && width == n@pre &&
      1 <= n@pre && n@pre <= 8 &&
      Zlength(stones_l) == n@pre &&
      Zlength(prefix_l) == n@pre + 1 &&
      StoneMassesBounded(stones_l, n@pre) &&
      StonePrefixDone(stones_l, prefix_l, n@pre) &&
      StoneTableShape(dp_init, n@pre) &&
      IntArray::full(stones, n@pre, stones_l) *
      IntArray::full(prefix, n@pre + 1, prefix_l) *
      IntArray2::full(dp, n@pre, n@pre, dp_init)
   */
  /*@ Inv Assert
      exists prefix_l dp_l,
      stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
      n == n@pre && width == n@pre &&
      1 <= n@pre && n@pre <= 8 &&
      Zlength(stones_l) == n@pre &&
      Zlength(prefix_l) == n@pre + 1 &&
      0 <= row && row <= n@pre &&
      StoneMassesBounded(stones_l, n@pre) &&
      StonePrefixDone(stones_l, prefix_l, n@pre) &&
      StoneZeroRows(dp_l, n@pre, row) &&
      IntArray::full(stones, n@pre, stones_l) *
      IntArray::full(prefix, n@pre + 1, prefix_l) *
      IntArray2::full(dp, n@pre, n@pre, dp_l)
   */
  for (int row = 0; row < n; ++row) {
    /*@ Inv Assert
        exists prefix_l dp_l,
        stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
        n == n@pre && width == n@pre &&
        1 <= n@pre && n@pre <= 8 &&
        Zlength(stones_l) == n@pre &&
        Zlength(prefix_l) == n@pre + 1 &&
        0 <= row && row < n@pre &&
        0 <= col && col <= n@pre &&
        StoneMassesBounded(stones_l, n@pre) &&
        StonePrefixDone(stones_l, prefix_l, n@pre) &&
        StoneZeroProgress(dp_l, n@pre, row, col) &&
        IntArray::full(stones, n@pre, stones_l) *
        IntArray::full(prefix, n@pre + 1, prefix_l) *
        IntArray2::full(dp, n@pre, n@pre, dp_l)
     */
    for (int col = 0; col < n; ++col) {
      *(dp + row * width + col) = 0;
    }
    /*@ Assert
        exists prefix_l dp_l,
        stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
        n == n@pre && width == n@pre &&
        1 <= n@pre && n@pre <= 8 &&
        0 <= row && row < n@pre &&
        Zlength(stones_l) == n@pre &&
        Zlength(prefix_l) == n@pre + 1 &&
        StoneMassesBounded(stones_l, n@pre) &&
        StonePrefixDone(stones_l, prefix_l, n@pre) &&
        StoneZeroRows(dp_l, n@pre, row + 1) &&
        IntArray::full(stones, n@pre, stones_l) *
        IntArray::full(prefix, n@pre + 1, prefix_l) *
        IntArray2::full(dp, n@pre, n@pre, dp_l)
     */
  }

  /*@ Assert
      exists prefix_l dp_l,
      stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
      n == n@pre && width == n@pre &&
      1 <= n@pre && n@pre <= 8 &&
      Zlength(stones_l) == n@pre &&
      Zlength(prefix_l) == n@pre + 1 &&
      StoneMassesBounded(stones_l, n@pre) &&
      StonePrefixDone(stones_l, prefix_l, n@pre) &&
      StoneZeroRows(dp_l, n@pre, n@pre) &&
      StoneLenDone(stones_l, dp_l, n@pre, 2) &&
      IntArray::full(stones, n@pre, stones_l) *
      IntArray::full(prefix, n@pre + 1, prefix_l) *
      IntArray2::full(dp, n@pre, n@pre, dp_l)
   */
  /*@ Inv Assert
      exists prefix_l dp_l,
      stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
      n == n@pre && width == n@pre &&
      1 <= n@pre && n@pre <= 8 &&
      2 <= len && len <= n@pre + 1 &&
      Zlength(stones_l) == n@pre &&
      Zlength(prefix_l) == n@pre + 1 &&
      StoneMassesBounded(stones_l, n@pre) &&
      StonePrefixDone(stones_l, prefix_l, n@pre) &&
      StoneLenDone(stones_l, dp_l, n@pre, len) &&
      IntArray::full(stones, n@pre, stones_l) *
      IntArray::full(prefix, n@pre + 1, prefix_l) *
      IntArray2::full(dp, n@pre, n@pre, dp_l)
   */
  for (int len = 2; len <= n; ++len) {
    /*@ Inv Assert
        exists prefix_l dp_l,
        stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
        n == n@pre && width == n@pre &&
        1 <= n@pre && n@pre <= 8 &&
        2 <= len && len <= n@pre &&
        0 <= left && left <= n@pre - len + 1 &&
        Zlength(stones_l) == n@pre &&
        Zlength(prefix_l) == n@pre + 1 &&
        StoneMassesBounded(stones_l, n@pre) &&
        StonePrefixDone(stones_l, prefix_l, n@pre) &&
        StoneLeftProgress(stones_l, dp_l, n@pre, len, left) &&
        IntArray::full(stones, n@pre, stones_l) *
        IntArray::full(prefix, n@pre + 1, prefix_l) *
        IntArray2::full(dp, n@pre, n@pre, dp_l)
     */
    for (int left = 0; left + len <= n; ++left) {
      int right = left + len - 1;
      int interval_sum = prefix[right + 1] - prefix[left];
      int best = 1000000;

      /*@ Assert
          exists prefix_l dp_l,
          stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
          n == n@pre && width == n@pre &&
          1 <= n@pre && n@pre <= 8 &&
          2 <= len && len <= n@pre &&
          0 <= left && left + len <= n@pre &&
          right == left + len - 1 &&
          left < right && right < n@pre &&
          interval_sum == sum(sublist(left, right + 1, stones_l)) &&
          2 <= interval_sum && interval_sum <= 8000 &&
          best == 1000000 &&
          Zlength(stones_l) == n@pre &&
          Zlength(prefix_l) == n@pre + 1 &&
          StoneMassesBounded(stones_l, n@pre) &&
          StonePrefixDone(stones_l, prefix_l, n@pre) &&
          StoneSplitProgress(stones_l, dp_l, n@pre, len, left, left, best) &&
          IntArray::full(stones, n@pre, stones_l) *
          IntArray::full(prefix, n@pre + 1, prefix_l) *
          IntArray2::full(dp, n@pre, n@pre, dp_l)
       */
      /*@ Inv Assert
          exists prefix_l dp_l,
          stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
          n == n@pre && width == n@pre &&
          1 <= n@pre && n@pre <= 8 &&
          2 <= len && len <= n@pre &&
          0 <= left && left + len <= n@pre &&
          right == left + len - 1 &&
          left < right && right < n@pre &&
          left <= split && split <= right &&
          interval_sum == sum(sublist(left, right + 1, stones_l)) &&
          2 <= interval_sum && interval_sum <= 8000 &&
          0 <= best && best <= 1000000 &&
          Zlength(stones_l) == n@pre &&
          Zlength(prefix_l) == n@pre + 1 &&
          StoneMassesBounded(stones_l, n@pre) &&
          StonePrefixDone(stones_l, prefix_l, n@pre) &&
          StoneSplitProgress(stones_l, dp_l, n@pre, len, left, split, best) &&
          IntArray::full(stones, n@pre, stones_l) *
          IntArray::full(prefix, n@pre + 1, prefix_l) *
          IntArray2::full(dp, n@pre, n@pre, dp_l)
       */
      for (int split = left; split < right; ++split) {
        /*@ Assert
            exists prefix_l dp_l,
            stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
            n == n@pre && width == n@pre &&
            1 <= n@pre && n@pre <= 8 &&
            2 <= len && len <= n@pre &&
            0 <= left && left + len <= n@pre &&
            right == left + len - 1 &&
            left <= split && split < right && right < n@pre &&
            interval_sum == sum(sublist(left, right + 1, stones_l)) &&
            2 <= interval_sum && interval_sum <= 8000 &&
            0 <= dp_l[left][split] && dp_l[left][split] <= 56000 &&
            0 <= dp_l[split + 1][right] && dp_l[split + 1][right] <= 56000 &&
            StoneMassesBounded(stones_l, n@pre) &&
            StonePrefixDone(stones_l, prefix_l, n@pre) &&
            StoneSplitProgress(stones_l, dp_l, n@pre, len, left, split, best) &&
            IntArray::full(stones, n@pre, stones_l) *
            IntArray::full(prefix, n@pre + 1, prefix_l) *
            IntArray2::full(dp, n@pre, n@pre, dp_l)
        */
        int left_value = *(dp + left * width + split);
        /*@ Assert
            exists prefix_l dp_l,
            stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
            n == n@pre && width == n@pre &&
            1 <= n@pre && n@pre <= 8 &&
            2 <= len && len <= n@pre &&
            0 <= left && left + len <= n@pre &&
            right == left + len - 1 &&
            left <= split && split < right && right < n@pre &&
            left_value == dp_l[left][split] &&
            interval_sum == sum(sublist(left, right + 1, stones_l)) &&
            2 <= interval_sum && interval_sum <= 8000 &&
            0 <= dp_l[left][split] && dp_l[left][split] <= 56000 &&
            0 <= dp_l[split + 1][right] && dp_l[split + 1][right] <= 56000 &&
            StoneMassesBounded(stones_l, n@pre) &&
            StonePrefixDone(stones_l, prefix_l, n@pre) &&
            StoneSplitProgress(stones_l, dp_l, n@pre, len, left, split, best) &&
            IntArray::full(stones, n@pre, stones_l) *
            IntArray::full(prefix, n@pre + 1, prefix_l) *
            IntArray2::full(dp, n@pre, n@pre, dp_l)
         */
        int right_value = *(dp + (split + 1) * width + right);
        int candidate = left_value + right_value + interval_sum;

        /*@ Assert
            exists prefix_l dp_l,
            stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
            n == n@pre && width == n@pre &&
            1 <= n@pre && n@pre <= 8 &&
            2 <= len && len <= n@pre &&
            0 <= left && left + len <= n@pre &&
            right == left + len - 1 &&
            left <= split && split < right && right < n@pre &&
            left_value == dp_l[left][split] &&
            right_value == dp_l[split + 1][right] &&
            interval_sum == sum(sublist(left, right + 1, stones_l)) &&
            candidate == left_value + right_value + interval_sum &&
            0 <= candidate && candidate <= 56000 &&
            StoneSplitCandidate(stones_l, dp_l, left, right, split, candidate) &&
            StoneMassesBounded(stones_l, n@pre) &&
            StonePrefixDone(stones_l, prefix_l, n@pre) &&
            StoneSplitProgress(stones_l, dp_l, n@pre, len, left, split, best) &&
            IntArray::full(stones, n@pre, stones_l) *
            IntArray::full(prefix, n@pre + 1, prefix_l) *
            IntArray2::full(dp, n@pre, n@pre, dp_l)
         */
        if (candidate < best) {
          best = candidate;
        }
        /*@ Assert
            exists prefix_l dp_l,
            stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
            n == n@pre && width == n@pre &&
            1 <= n@pre && n@pre <= 8 &&
            2 <= len && len <= n@pre &&
            0 <= left && left + len <= n@pre &&
            right == left + len - 1 &&
            left <= split && split < right && right < n@pre &&
            left_value == dp_l[left][split] &&
            right_value == dp_l[split + 1][right] &&
            interval_sum == sum(sublist(left, right + 1, stones_l)) &&
            candidate == left_value + right_value + interval_sum &&
            0 <= candidate && candidate <= 56000 &&
            0 <= best && best <= 1000000 &&
            StoneSplitCandidate(stones_l, dp_l, left, right, split, candidate) &&
            StoneMassesBounded(stones_l, n@pre) &&
            StonePrefixDone(stones_l, prefix_l, n@pre) &&
            StoneSplitProgress(stones_l, dp_l, n@pre, len, left, split + 1, best) &&
            IntArray::full(stones, n@pre, stones_l) *
            IntArray::full(prefix, n@pre + 1, prefix_l) *
            IntArray2::full(dp, n@pre, n@pre, dp_l)
         */
      }

      /*@ Assert
          exists prefix_l dp_l,
          stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
          n == n@pre && width == n@pre &&
          1 <= n@pre && n@pre <= 8 &&
          2 <= len && len <= n@pre &&
          0 <= left && left + len <= n@pre &&
          right == left + len - 1 &&
          left < right && right < n@pre &&
          interval_sum == sum(sublist(left, right + 1, stones_l)) &&
          2 <= interval_sum && interval_sum <= 8000 &&
          0 <= best && best <= 56000 &&
          StoneMassesBounded(stones_l, n@pre) &&
          StonePrefixDone(stones_l, prefix_l, n@pre) &&
          StoneSplitProgress(stones_l, dp_l, n@pre, len, left, right, best) &&
          StoneIntervalMin(stones_l, left, right, best) &&
          IntArray::full(stones, n@pre, stones_l) *
          IntArray::full(prefix, n@pre + 1, prefix_l) *
          IntArray2::full(dp, n@pre, n@pre, dp_l)
       */
      *(dp + left * width + right) = best;
      /*@ Assert
          exists prefix_l dp_old dp_new,
          stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
          n == n@pre && width == n@pre &&
          1 <= n@pre && n@pre <= 8 &&
          2 <= len && len <= n@pre &&
          0 <= left && left + len <= n@pre &&
          right == left + len - 1 &&
          interval_sum == sum(sublist(left, right + 1, stones_l)) &&
          2 <= interval_sum && interval_sum <= 8000 &&
          0 <= best && best <= 56000 &&
          StoneMassesBounded(stones_l, n@pre) &&
          StonePrefixDone(stones_l, prefix_l, n@pre) &&
          StoneUpdatedCell(stones_l, dp_old, dp_new, left, right, best) &&
          StoneLeftProgress(stones_l, dp_new, n@pre, len, left + 1) &&
          IntArray::full(stones, n@pre, stones_l) *
          IntArray::full(prefix, n@pre + 1, prefix_l) *
          IntArray2::full(dp, n@pre, n@pre, dp_new)
       */
    }
    /*@ Assert
        exists prefix_l dp_l,
        stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
        n == n@pre && width == n@pre &&
        1 <= n@pre && n@pre <= 8 &&
        2 <= len && len <= n@pre &&
        StoneMassesBounded(stones_l, n@pre) &&
        StonePrefixDone(stones_l, prefix_l, n@pre) &&
        StoneLenDone(stones_l, dp_l, n@pre, len + 1) &&
        IntArray::full(stones, n@pre, stones_l) *
        IntArray::full(prefix, n@pre + 1, prefix_l) *
        IntArray2::full(dp, n@pre, n@pre, dp_l)
     */
  }

  /*@ Assert
      exists prefix_l dp_l,
      stones == stones@pre && prefix == prefix@pre && dp == dp@pre &&
      n == n@pre && width == n@pre &&
      1 <= n@pre && n@pre <= 8 &&
      StoneMassesBounded(stones_l, n@pre) &&
      StonePrefixDone(stones_l, prefix_l, n@pre) &&
      StoneLenDone(stones_l, dp_l, n@pre, n@pre + 1) &&
      StoneMinimumCost(stones_l, n@pre, dp_l[0][n@pre - 1]) &&
      0 <= dp_l[0][n@pre - 1] && dp_l[0][n@pre - 1] <= 56000 &&
      IntArray::full(stones, n@pre, stones_l) *
      IntArray::full(prefix, n@pre + 1, prefix_l) *
      IntArray2::full(dp, n@pre, n@pre, dp_l)
   */
  return *(dp + 0 * width + (n - 1));
}
