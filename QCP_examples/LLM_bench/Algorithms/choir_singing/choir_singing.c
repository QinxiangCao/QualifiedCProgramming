/*@ Extern Coq
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (eq : {A} -> A -> A -> Prop)
      (ChoirDPLeftPrefix : list Z -> list Z -> Z -> Prop)
      (ChoirLeftInnerProgress : list Z -> list Z -> Z -> Z -> Prop)
      (ChoirDPRightSuffix : list Z -> list Z -> Z -> Prop)
      (ChoirRightInnerProgress : list Z -> list Z -> Z -> Z -> Prop)
      (ChoirBestPrefix : list Z -> Z -> Z -> Prop)
      (ChoirMinimumRemovals : list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.choir_singing.choir_singing_lib */

int choir_singing(int *nums, int numsSize)
/*@ With (heights : list Z)
    Require
      2 <= numsSize && numsSize <= 100 &&
      Zlength(heights) == numsSize &&
      Forall(Z::le(130), heights) && Forall(Z::ge(230), heights) &&
      IntArray::full(nums, numsSize, heights)
    Ensure
      ChoirMinimumRemovals(heights, __return) &&
      IntArray::full(nums, numsSize, heights)
 */
{
  int dp_left[100];
  int dp_right[100];

  /*@ Inv Assert
      exists left_written right_written,
      nums == nums@pre && numsSize == numsSize@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100 &&
      Zlength(heights) == numsSize@pre &&
      0 <= i && i <= numsSize@pre &&
      Forall(eq(1), left_written) &&
      Forall(eq(1), right_written) &&
      IntArray::full(nums, numsSize@pre, heights) *
      IntArray::seg(dp_left, 0, i, left_written) *
      IntArray::undef_seg(dp_left, i, numsSize@pre) *
      IntArray::undef_seg(dp_left, numsSize@pre, 100) *
      IntArray::seg(dp_right, 0, i, right_written) *
      IntArray::undef_seg(dp_right, i, numsSize@pre) *
      IntArray::undef_seg(dp_right, numsSize@pre, 100)
   */
  for (int i = 0; i < numsSize; ++i) {
    dp_left[i] = 1;
    dp_right[i] = 1;
  }

  /*@ Inv Assert
      exists left_values right_values,
      nums == nums@pre && numsSize == numsSize@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100 &&
      Zlength(heights) == numsSize@pre &&
      0 <= i && i <= numsSize@pre &&
      ChoirDPLeftPrefix(heights, left_values, i) &&
      Forall(eq(1), right_values) &&
      IntArray::full(nums, numsSize@pre, heights) *
      IntArray::full(dp_left, numsSize@pre, left_values) *
      IntArray::undef_seg(dp_left, numsSize@pre, 100) *
      IntArray::full(dp_right, numsSize@pre, right_values) *
      IntArray::undef_seg(dp_right, numsSize@pre, 100)
   */
  for (int i = 0; i < numsSize; ++i) {
    /*@ Inv Assert
        exists left_values right_values,
        nums == nums@pre && numsSize == numsSize@pre &&
        1 <= numsSize@pre && numsSize@pre <= 100 &&
        Zlength(heights) == numsSize@pre &&
        0 <= i && i < numsSize@pre &&
        -1 <= j && j < i &&
        ChoirLeftInnerProgress(heights, left_values, i, j + 1) &&
        Forall(eq(1), right_values) &&
        IntArray::full(nums, numsSize@pre, heights) *
        IntArray::full(dp_left, numsSize@pre, left_values) *
      IntArray::undef_seg(dp_left, numsSize@pre, 100) *
        IntArray::full(dp_right, numsSize@pre, right_values) *
      IntArray::undef_seg(dp_right, numsSize@pre, 100)
     */
    for (int j = i - 1; j >= 0; --j) {
      if (nums[j] < nums[i] && dp_left[j] + 1 > dp_left[i]) {
        dp_left[i] = dp_left[j] + 1;
      }
    }
  }

  /*@ Inv Assert
      exists left_values right_values,
      nums == nums@pre && numsSize == numsSize@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100 &&
      Zlength(heights) == numsSize@pre &&
      0 <= i + 1 && i + 1 <= numsSize@pre &&
      ChoirDPLeftPrefix(heights, left_values, numsSize@pre) &&
      ChoirDPRightSuffix(heights, right_values, i + 1) &&
      IntArray::full(nums, numsSize@pre, heights) *
      IntArray::full(dp_left, numsSize@pre, left_values) *
      IntArray::undef_seg(dp_left, numsSize@pre, 100) *
      IntArray::full(dp_right, numsSize@pre, right_values) *
      IntArray::undef_seg(dp_right, numsSize@pre, 100)
   */
  for (int i = numsSize - 1; i >= 0; --i) {
    /*@ Inv Assert
        exists left_values right_values,
        nums == nums@pre && numsSize == numsSize@pre &&
        1 <= numsSize@pre && numsSize@pre <= 100 &&
        Zlength(heights) == numsSize@pre &&
        0 <= i && i < numsSize@pre &&
        i + 1 <= j && j <= numsSize@pre &&
        ChoirDPLeftPrefix(heights, left_values, numsSize@pre) &&
        ChoirRightInnerProgress(heights, right_values, i, j) &&
        IntArray::full(nums, numsSize@pre, heights) *
        IntArray::full(dp_left, numsSize@pre, left_values) *
      IntArray::undef_seg(dp_left, numsSize@pre, 100) *
        IntArray::full(dp_right, numsSize@pre, right_values) *
      IntArray::undef_seg(dp_right, numsSize@pre, 100)
     */
    for (int j = i + 1; j < numsSize; ++j) {
      if (nums[j] < nums[i] && dp_right[j] + 1 > dp_right[i]) {
        dp_right[i] = dp_right[j] + 1;
      }
    }
  }

  int max_choir = 0;
  /*@ Inv Assert
      exists left_values right_values,
      nums == nums@pre && numsSize == numsSize@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100 &&
      Zlength(heights) == numsSize@pre &&
      0 <= k && k <= numsSize@pre &&
      0 <= max_choir && max_choir <= numsSize@pre &&
      ChoirDPLeftPrefix(heights, left_values, numsSize@pre) &&
      ChoirDPRightSuffix(heights, right_values, 0) &&
      ChoirBestPrefix(heights, k, max_choir) &&
      IntArray::full(nums, numsSize@pre, heights) *
      IntArray::full(dp_left, numsSize@pre, left_values) *
      IntArray::undef_seg(dp_left, numsSize@pre, 100) *
      IntArray::full(dp_right, numsSize@pre, right_values) *
      IntArray::undef_seg(dp_right, numsSize@pre, 100)
   */
  for (int k = 0; k < numsSize; ++k) {
    if (dp_left[k] + dp_right[k] > max_choir) {
      max_choir = dp_left[k] + dp_right[k] - 1;
    }
  }

  /*@ Assert
      nums == nums@pre && numsSize == numsSize@pre &&
      1 <= numsSize && numsSize <= 100 &&
      0 <= max_choir && max_choir <= numsSize &&
      ChoirMinimumRemovals(heights, numsSize - max_choir) &&
      IntArray::full(nums, numsSize@pre, heights) *
      IntArray::undef_full(dp_left, 100) *
      IntArray::undef_full(dp_right, 100)
   */
  return numsSize - max_choir;
}
