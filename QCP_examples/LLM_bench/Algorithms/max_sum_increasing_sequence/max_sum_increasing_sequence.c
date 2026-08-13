



/*@ Extern Coq
      (MSISMaximum : list Z -> Z -> Prop)
      (MSISDPTablePrefix : list Z -> list Z -> Z -> Prop)
      (MSISInnerProgress : list Z -> list Z -> Z -> Z -> Prop)
      (MSISBestSoFar : list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.max_sum_increasing_sequence.max_sum_increasing_sequence_lib */

int maxSumIncreasingSequence(int *nums, int numsSize, int *dp)
/*@ With (l : list Z)
    Require
      1 <= numsSize && numsSize <= 100000 &&
      Zlength(l) == numsSize &&
      (forall (k : Z),
        (0 <= k && k < numsSize) =>
        (1 <= l[k] && l[k] <= 10000)) &&
      IntArray::full(nums, numsSize, l) *
      IntArray::undef_full(dp, numsSize)
    Ensure
      exists d,
      MSISMaximum(l, __return) &&
      1 <= __return && __return <= INT_MAX &&
      MSISDPTablePrefix(l, d, numsSize) &&
      IntArray::full(nums, numsSize, l) *
      IntArray::full(dp, numsSize, d)
 */
{
  dp[0] = nums[0];
  int ans = nums[0];
  /*@ Inv Assert
      exists d,
      nums == nums@pre && numsSize == numsSize@pre && dp == dp@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100000 &&
      Zlength(l) == numsSize@pre &&
      1 <= i && i <= numsSize@pre &&
      1 <= ans && ans <= i * 10000 &&
      MSISDPTablePrefix(l, d, i) &&
      MSISBestSoFar(l, i, ans) &&
      (forall (k : Z),
        (0 <= k && k < numsSize@pre) =>
        (1 <= l[k] && l[k] <= 10000)) &&
      IntArray::full(nums, numsSize@pre, l) *
      IntArray::seg(dp, 0, i, d) *
      IntArray::undef_seg(dp, i, numsSize@pre)
   */
  for (int i = 1; i < numsSize; ++i) {
    dp[i] = nums[i];
    /*@ Inv Assert
        exists d,
        nums == nums@pre && numsSize == numsSize@pre && dp == dp@pre &&
        1 <= numsSize@pre && numsSize@pre <= 100000 &&
        Zlength(l) == numsSize@pre &&
        1 <= i && i < numsSize@pre &&
        0 <= j && j <= i &&
        1 <= ans && ans <= i * 10000 &&
        MSISBestSoFar(l, i, ans) &&
        MSISInnerProgress(l, d, i, j) &&
        (forall (k : Z),
          (0 <= k && k < numsSize@pre) =>
          (1 <= l[k] && l[k] <= 10000)) &&
        IntArray::full(nums, numsSize@pre, l) *
        IntArray::seg(dp, 0, i + 1, d) *
        IntArray::undef_seg(dp, i + 1, numsSize@pre)
     */
    for (int j = 0; j < i; ++j) {
      if (nums[j] < nums[i]) {
        int candidate = dp[j] + nums[i];
        if (candidate > dp[i]) {
          dp[i] = candidate;
        }
      }
    }
    /*@ Assert
        exists d,
        nums == nums@pre && numsSize == numsSize@pre && dp == dp@pre &&
        1 <= numsSize@pre && numsSize@pre <= 100000 &&
        Zlength(l) == numsSize@pre &&
        1 <= i && i < numsSize@pre &&
        1 <= ans && ans <= i * 10000 &&
        MSISBestSoFar(l, i, ans) &&
        MSISDPTablePrefix(l, d, i + 1) &&
        (forall (k : Z),
          (0 <= k && k < numsSize@pre) =>
          (1 <= l[k] && l[k] <= 10000)) &&
        IntArray::full(nums, numsSize@pre, l) *
        IntArray::seg(dp, 0, i + 1, d) *
        IntArray::undef_seg(dp, i + 1, numsSize@pre)
     */
    if (dp[i] > ans) {
      ans = dp[i];
    }
  }
  return ans;
}
