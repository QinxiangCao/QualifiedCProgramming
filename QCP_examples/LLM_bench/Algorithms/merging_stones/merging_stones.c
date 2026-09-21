#include "array2_def.h"

/*@ include strategies "undef_uint_array.strategies" */
/*@ Extern Coq
      (sum : list Z -> Z)
      (sublist : {A} -> Z -> Z -> list A -> list A)
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (map : {A B} -> (A -> B) -> list A -> list B)
      (eq : {A} -> A -> A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (StoneMinimumCost : list Z -> Z -> Prop)
      (StonePrefixProgress : list Z -> list Z -> Z -> Prop)
      (StonePrefixDone : list Z -> list Z -> Z -> Prop)
      (StoneZeroRows : list (list Z) -> Z -> Prop)
      (StoneZeroProgress : list (list Z) -> Z -> Z -> Prop)
      (StoneLenDone : list Z -> list (list Z) -> Z -> Z -> Prop)
      (StoneLeftProgress : list Z -> list (list Z) -> Z -> Z -> Z -> Prop)
      (StoneSplitProgress : list Z -> list (list Z) -> Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.merging_stones.merging_stones_lib */

/* Merge adjacent piles into one with the least possible total cost.
 * The verified implementation accepts 1 <= n <= 8 and masses in [1,1000]. */
int mergingStones(int *stones, int n)
/*@ With (stones_l : list Z) 
    Require
      1 <= n && n <= 8 &&
      Zlength(stones_l) == n &&
      Forall(Z::le(1), stones_l) && Forall(Z::ge(1000), stones_l) &&
      IntArray::full(stones, n, stones_l)
    Ensure
      StoneMinimumCost(stones_l, __return) &&
      IntArray::full(stones, n, stones_l)
 */
{
  int prefix[9];
  int dp[64];
  /*@ Inv Assert
      exists dp_flat,
      stones == stones@pre && n == n@pre &&
      0 <= k && k <= n@pre * n@pre &&
      1 <= n@pre && n@pre <= 8 &&
      Zlength(stones_l) == n@pre &&
      Forall(Z::le(1), stones_l) && Forall(Z::ge(1000), stones_l) &&
      IntArray::full(stones@pre, n@pre, stones_l) *
      IntArray::undef_full(prefix, 9) *
      IntArray::seg(dp, 0, k, dp_flat) *
      IntArray::undef_seg(dp, k, 64)
   */
  for (int k = 0; k < n * n; ++k) {
    dp[k] = 0;
  }



  int width = n;
  prefix[0] = 0;
  /*@ Inv Assert
      exists prefix_l dp_init,
      stones == stones@pre &&  
      n == n@pre && width == n@pre &&
      1 <= n@pre && n@pre <= 8 &&
      Forall(Z::le(1), stones_l) && Forall(Z::ge(1000), stones_l) &&
      Forall(eq(n@pre), map(Zlength, dp_init)) &&
      0 <= i && i <= n@pre &&
      StonePrefixProgress(stones_l, prefix_l, i) &&
      IntArray::full(stones, n@pre, stones_l) *
      IntArray::seg(prefix, 0, i + 1, prefix_l) *
      IntArray::undef_seg(prefix, i + 1, n@pre + 1) *
      IntArray2::full(dp, n@pre, n@pre, dp_init) *
      IntArray::undef_seg(prefix, n@pre + 1, 9) *
      IntArray::undef_seg(dp, n@pre * n@pre, 64)
   */
  for (int i = 0; i < n; ++i) {
    prefix[i + 1] = prefix[i] + stones[i];
  }

  /*@ Inv Assert
      exists prefix_l dp_l,
      stones == stones@pre &&  
      n == n@pre && width == n@pre &&
      1 <= n@pre && n@pre <= 8 &&
      Forall(Z::le(1), stones_l) && Forall(Z::ge(1000), stones_l) &&
      Forall(eq(n@pre), map(Zlength, dp_l)) &&
      StonePrefixDone(stones_l, prefix_l, n@pre) &&
      0 <= row && row <= n@pre &&
      StoneZeroRows(dp_l, row) &&
      IntArray::full(stones, n@pre, stones_l) *
      IntArray::full(prefix, n@pre + 1, prefix_l) *
      IntArray2::full(dp, n@pre, n@pre, dp_l) *
      IntArray::undef_seg(prefix, n@pre + 1, 9) *
      IntArray::undef_seg(dp, n@pre * n@pre, 64)
   */
  for (int row = 0; row < n; ++row) {
    /*@ Inv Assert
        exists prefix_l dp_l,
        stones == stones@pre &&  
        n == n@pre && width == n@pre &&
        1 <= n@pre && n@pre <= 8 &&
        Forall(Z::le(1), stones_l) && Forall(Z::ge(1000), stones_l) &&
        Forall(eq(n@pre), map(Zlength, dp_l)) &&
        StonePrefixDone(stones_l, prefix_l, n@pre) &&
        0 <= row && row < n@pre &&
        0 <= col && col <= n@pre &&
        StoneZeroProgress(dp_l, row, col) &&
        IntArray::full(stones, n@pre, stones_l) *
        IntArray::full(prefix, n@pre + 1, prefix_l) *
        IntArray2::full(dp, n@pre, n@pre, dp_l) *
      IntArray::undef_seg(prefix, n@pre + 1, 9) *
      IntArray::undef_seg(dp, n@pre * n@pre, 64)
   */
    for (int col = 0; col < n; ++col) {
      *(dp + row * width + col) = 0;
    }
  }

  /*@ Inv Assert
      exists prefix_l dp_l,
      stones == stones@pre &&  
      n == n@pre && width == n@pre &&
      1 <= n@pre && n@pre <= 8 &&
      Forall(Z::le(1), stones_l) && Forall(Z::ge(1000), stones_l) &&
      Forall(eq(n@pre), map(Zlength, dp_l)) &&
      StonePrefixDone(stones_l, prefix_l, n@pre) &&
      2 <= len && len <= n@pre + 1 &&
      StoneLenDone(stones_l, dp_l, n@pre, len) &&
      IntArray::full(stones, n@pre, stones_l) *
      IntArray::full(prefix, n@pre + 1, prefix_l) *
      IntArray2::full(dp, n@pre, n@pre, dp_l) *
      IntArray::undef_seg(prefix, n@pre + 1, 9) *
      IntArray::undef_seg(dp, n@pre * n@pre, 64)
   */
  for (int len = 2; len <= n; ++len) {
    /*@ Inv Assert
        exists prefix_l dp_l,
        stones == stones@pre &&  
        n == n@pre && width == n@pre &&
        1 <= n@pre && n@pre <= 8 &&
        Forall(Z::le(1), stones_l) && Forall(Z::ge(1000), stones_l) &&
        Forall(eq(n@pre), map(Zlength, dp_l)) &&
        StonePrefixDone(stones_l, prefix_l, n@pre) &&
        2 <= len && len <= n@pre &&
        0 <= left && left <= n@pre - len + 1 &&
        StoneLeftProgress(stones_l, dp_l, n@pre, len, left) &&
        IntArray::full(stones, n@pre, stones_l) *
        IntArray::full(prefix, n@pre + 1, prefix_l) *
        IntArray2::full(dp, n@pre, n@pre, dp_l) *
      IntArray::undef_seg(prefix, n@pre + 1, 9) *
      IntArray::undef_seg(dp, n@pre * n@pre, 64)
   */
    for (int left = 0; left + len <= n; ++left) {
      int right = left + len - 1;
      int interval_sum = prefix[right + 1] - prefix[left];
      int best = 1000000;

      /*@ Inv Assert
          exists prefix_l dp_l,
          stones == stones@pre &&  
          n == n@pre && width == n@pre &&
          1 <= n@pre && n@pre <= 8 &&
          Forall(Z::le(1), stones_l) && Forall(Z::ge(1000), stones_l) &&
          Forall(eq(n@pre), map(Zlength, dp_l)) &&
          StonePrefixDone(stones_l, prefix_l, n@pre) &&
          2 <= len && len <= n@pre &&
          0 <= left && left + len <= n@pre &&
          right == left + len - 1 &&
          left <= split && split <= right &&
          interval_sum == sum(sublist(left, right + 1, stones_l)) &&
          2 <= interval_sum && interval_sum <= 8000 &&
          0 <= best && best <= 1000000 &&
          StoneSplitProgress(stones_l, dp_l, n@pre, len, left, split, best) &&
          IntArray::full(stones, n@pre, stones_l) *
          IntArray::full(prefix, n@pre + 1, prefix_l) *
          IntArray2::full(dp, n@pre, n@pre, dp_l) *
      IntArray::undef_seg(prefix, n@pre + 1, 9) *
      IntArray::undef_seg(dp, n@pre * n@pre, 64)
   */
      for (int split = left; split < right; ++split) {
        int left_value = *(dp + left * width + split);
        /*@ Assert
            exists prefix_l dp_l,
            stones == stones@pre &&  
            n == n@pre && width == n@pre &&
            1 <= n@pre && n@pre <= 8 &&
            Forall(Z::le(1), stones_l) && Forall(Z::ge(1000), stones_l) &&
            Forall(eq(n@pre), map(Zlength, dp_l)) &&
            StonePrefixDone(stones_l, prefix_l, n@pre) &&
            2 <= len && len <= n@pre &&
            0 <= left && left + len <= n@pre &&
            right == left + len - 1 &&
            left <= split && split <= right &&
            interval_sum == sum(sublist(left, right + 1, stones_l)) &&
            2 <= interval_sum && interval_sum <= 8000 &&
            0 <= best && best <= 1000000 &&
            StoneSplitProgress(stones_l, dp_l, n@pre, len, left, split, best) &&
            split < right &&
            left_value == dp_l[left][split] &&
            IntArray::full(stones, n@pre, stones_l) *
            IntArray::full(prefix, n@pre + 1, prefix_l) *
            IntArray2::full(dp, n@pre, n@pre, dp_l) *
      IntArray::undef_seg(prefix, n@pre + 1, 9) *
      IntArray::undef_seg(dp, n@pre * n@pre, 64)
   */
        int right_value = *(dp + (split + 1) * width + right);
        int candidate = left_value + right_value + interval_sum;
        if (candidate < best) {
          best = candidate;
        }
      }
      *(dp + left * width + right) = best;
    }
  }
  int result = *(dp + 0 * width + (n - 1));
  /*@ Assert
      stones == stones@pre && n == n@pre &&
      StoneMinimumCost(stones_l, result) &&
      IntArray::full(stones, n@pre, stones_l) *
      IntArray::undef_full(prefix, 9) *
      IntArray::undef_full(dp, 64) *
      has_int_permission(&width)
   */
  return result;
}
