



/*@ Extern Coq
      (ChoirOnesPrefix : list Z -> Z -> Prop)
      (ChoirOnesFull : list Z -> Z -> Prop)
      (ChoirDPLeftPrefix : list Z -> list Z -> Z -> Prop)
      (ChoirLeftInnerProgress : list Z -> list Z -> Z -> Z -> Prop)
      (ChoirDPRightSuffix : list Z -> list Z -> Z -> Prop)
      (ChoirRightInnerProgress : list Z -> list Z -> Z -> Z -> Prop)
      (ChoirBestPrefix : list Z -> Z -> Z -> Prop)
      (ChoirMinimumRemovals : list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.choir_singing.choir_singing_lib */

int choir_singing(int *nums, int numsSize, int *dp_left, int *dp_right)
/*@ With (heights : list Z)
    Require
      1 <= numsSize && numsSize <= 100 &&
      Zlength(heights) == numsSize &&
      IntArray::full(nums, numsSize, heights) *
      IntArray::undef_full(dp_left, numsSize) *
      IntArray::undef_full(dp_right, numsSize)
    Ensure
      exists left_values right_values,
      ChoirMinimumRemovals(heights, __return) &&
      0 <= __return && __return < numsSize &&
      ChoirDPLeftPrefix(heights, left_values, numsSize) &&
      ChoirDPRightSuffix(heights, right_values, 0) &&
      IntArray::full(nums, numsSize, heights) *
      IntArray::full(dp_left, numsSize, left_values) *
      IntArray::full(dp_right, numsSize, right_values)
 */
{
  /*@ Inv Assert
      exists left_written right_written,
      nums == nums@pre && numsSize == numsSize@pre &&
      dp_left == dp_left@pre && dp_right == dp_right@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100 &&
      Zlength(heights) == numsSize@pre &&
      0 <= i && i <= numsSize@pre &&
      ChoirOnesPrefix(left_written, i) &&
      ChoirOnesPrefix(right_written, i) &&
      IntArray::full(nums, numsSize@pre, heights) *
      IntArray::seg(dp_left, 0, i, left_written) *
      IntArray::undef_seg(dp_left, i, numsSize@pre) *
      IntArray::seg(dp_right, 0, i, right_written) *
      IntArray::undef_seg(dp_right, i, numsSize@pre)
   */
  for (int i = 0; i < numsSize; ++i) {
    dp_left[i] = 1;
    dp_right[i] = 1;
  }

  /*@ Assert
      exists left_values right_values,
      nums == nums@pre && numsSize == numsSize@pre &&
      dp_left == dp_left@pre && dp_right == dp_right@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100 &&
      Zlength(heights) == numsSize@pre &&
      ChoirOnesFull(left_values, numsSize@pre) &&
      ChoirOnesFull(right_values, numsSize@pre) &&
      IntArray::full(nums, numsSize@pre, heights) *
      IntArray::full(dp_left, numsSize@pre, left_values) *
      IntArray::full(dp_right, numsSize@pre, right_values)
   */

  /*@ Inv Assert
      exists left_values right_values,
      nums == nums@pre && numsSize == numsSize@pre &&
      dp_left == dp_left@pre && dp_right == dp_right@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100 &&
      Zlength(heights) == numsSize@pre &&
      0 <= i && i <= numsSize@pre &&
      ChoirDPLeftPrefix(heights, left_values, i) &&
      ChoirOnesFull(right_values, numsSize@pre) &&
      IntArray::full(nums, numsSize@pre, heights) *
      IntArray::full(dp_left, numsSize@pre, left_values) *
      IntArray::full(dp_right, numsSize@pre, right_values)
   */
  for (int i = 0; i < numsSize; ++i) {
    /*@ Inv Assert
        exists left_values right_values,
        nums == nums@pre && numsSize == numsSize@pre &&
        dp_left == dp_left@pre && dp_right == dp_right@pre &&
        1 <= numsSize@pre && numsSize@pre <= 100 &&
        Zlength(heights) == numsSize@pre &&
        0 <= i && i < numsSize@pre &&
        -1 <= j && j < i &&
        ChoirLeftInnerProgress(heights, left_values, i, j + 1) &&
        ChoirOnesFull(right_values, numsSize@pre) &&
        IntArray::full(nums, numsSize@pre, heights) *
        IntArray::full(dp_left, numsSize@pre, left_values) *
        IntArray::full(dp_right, numsSize@pre, right_values)
     */
    for (int j = i - 1; j >= 0; --j) {
      if (nums[j] < nums[i] && dp_left[j] + 1 > dp_left[i]) {
        dp_left[i] = dp_left[j] + 1;
      }
    }
    /*@ Assert
        exists left_values right_values,
        nums == nums@pre && numsSize == numsSize@pre &&
        dp_left == dp_left@pre && dp_right == dp_right@pre &&
        1 <= numsSize@pre && numsSize@pre <= 100 &&
        Zlength(heights) == numsSize@pre &&
        0 <= i && i < numsSize@pre &&
        ChoirDPLeftPrefix(heights, left_values, i + 1) &&
        ChoirOnesFull(right_values, numsSize@pre) &&
        IntArray::full(nums, numsSize@pre, heights) *
        IntArray::full(dp_left, numsSize@pre, left_values) *
        IntArray::full(dp_right, numsSize@pre, right_values)
     */
  }

  /*@ Assert
      exists left_values right_values,
      nums == nums@pre && numsSize == numsSize@pre &&
      dp_left == dp_left@pre && dp_right == dp_right@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100 &&
      Zlength(heights) == numsSize@pre &&
      ChoirDPLeftPrefix(heights, left_values, numsSize@pre) &&
      ChoirOnesFull(right_values, numsSize@pre) &&
      IntArray::full(nums, numsSize@pre, heights) *
      IntArray::full(dp_left, numsSize@pre, left_values) *
      IntArray::full(dp_right, numsSize@pre, right_values)
   */

  /*@ Inv Assert
      exists left_values right_values,
      nums == nums@pre && numsSize == numsSize@pre &&
      dp_left == dp_left@pre && dp_right == dp_right@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100 &&
      Zlength(heights) == numsSize@pre &&
      0 <= i + 1 && i + 1 <= numsSize@pre &&
      ChoirDPLeftPrefix(heights, left_values, numsSize@pre) &&
      ChoirDPRightSuffix(heights, right_values, i + 1) &&
      IntArray::full(nums, numsSize@pre, heights) *
      IntArray::full(dp_left, numsSize@pre, left_values) *
      IntArray::full(dp_right, numsSize@pre, right_values)
   */
  for (int i = numsSize - 1; i >= 0; --i) {
    /*@ Inv Assert
        exists left_values right_values,
        nums == nums@pre && numsSize == numsSize@pre &&
        dp_left == dp_left@pre && dp_right == dp_right@pre &&
        1 <= numsSize@pre && numsSize@pre <= 100 &&
        Zlength(heights) == numsSize@pre &&
        0 <= i && i < numsSize@pre &&
        i + 1 <= j && j <= numsSize@pre &&
        ChoirDPLeftPrefix(heights, left_values, numsSize@pre) &&
        ChoirRightInnerProgress(heights, right_values, i, j) &&
        IntArray::full(nums, numsSize@pre, heights) *
        IntArray::full(dp_left, numsSize@pre, left_values) *
        IntArray::full(dp_right, numsSize@pre, right_values)
     */
    for (int j = i + 1; j < numsSize; ++j) {
      if (nums[j] < nums[i] && dp_right[j] + 1 > dp_right[i]) {
        dp_right[i] = dp_right[j] + 1;
      }
    }
    /*@ Assert
        exists left_values right_values,
        nums == nums@pre && numsSize == numsSize@pre &&
        dp_left == dp_left@pre && dp_right == dp_right@pre &&
        1 <= numsSize@pre && numsSize@pre <= 100 &&
        Zlength(heights) == numsSize@pre &&
        0 <= i && i < numsSize@pre &&
        ChoirDPLeftPrefix(heights, left_values, numsSize@pre) &&
        ChoirDPRightSuffix(heights, right_values, i) &&
        IntArray::full(nums, numsSize@pre, heights) *
        IntArray::full(dp_left, numsSize@pre, left_values) *
        IntArray::full(dp_right, numsSize@pre, right_values)
     */
  }

  /*@ Assert
      exists left_values right_values,
      nums == nums@pre && numsSize == numsSize@pre &&
      dp_left == dp_left@pre && dp_right == dp_right@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100 &&
      Zlength(heights) == numsSize@pre &&
      ChoirDPLeftPrefix(heights, left_values, numsSize@pre) &&
      ChoirDPRightSuffix(heights, right_values, 0) &&
      IntArray::full(nums, numsSize@pre, heights) *
      IntArray::full(dp_left, numsSize@pre, left_values) *
      IntArray::full(dp_right, numsSize@pre, right_values)
   */

  int max_choir = 0;
  /*@ Inv Assert
      exists left_values right_values,
      nums == nums@pre && numsSize == numsSize@pre &&
      dp_left == dp_left@pre && dp_right == dp_right@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100 &&
      Zlength(heights) == numsSize@pre &&
      0 <= k && k <= numsSize@pre &&
      0 <= max_choir && max_choir <= numsSize@pre &&
      ChoirDPLeftPrefix(heights, left_values, numsSize@pre) &&
      ChoirDPRightSuffix(heights, right_values, 0) &&
      ChoirBestPrefix(heights, k, max_choir) &&
      IntArray::full(nums, numsSize@pre, heights) *
      IntArray::full(dp_left, numsSize@pre, left_values) *
      IntArray::full(dp_right, numsSize@pre, right_values)
   */
  for (int k = 0; k < numsSize; ++k) {
    if (dp_left[k] + dp_right[k] > max_choir) {
      max_choir = dp_left[k] + dp_right[k] - 1;
    }
  }

  /*@ Assert
      exists left_values right_values,
      nums == nums@pre && numsSize == numsSize@pre &&
      dp_left == dp_left@pre && dp_right == dp_right@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100 &&
      Zlength(heights) == numsSize@pre &&
      1 <= max_choir && max_choir <= numsSize@pre &&
      ChoirDPLeftPrefix(heights, left_values, numsSize@pre) &&
      ChoirDPRightSuffix(heights, right_values, 0) &&
      ChoirBestPrefix(heights, numsSize@pre, max_choir) &&
      IntArray::full(nums, numsSize@pre, heights) *
      IntArray::full(dp_left, numsSize@pre, left_values) *
      IntArray::full(dp_right, numsSize@pre, right_values)
   */
  return numsSize - max_choir;
}
