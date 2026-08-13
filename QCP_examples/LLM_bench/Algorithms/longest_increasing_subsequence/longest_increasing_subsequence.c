



/*@ Extern Coq
      (LISLength : list Z -> Z -> Prop)
      (LISDPTablePrefix : list Z -> list Z -> Z -> Prop)
      (LISInnerProgress : list Z -> list Z -> Z -> Z -> Prop)
      (LISBestSoFar : list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.longest_increasing_subsequence.longest_increasing_subsequence_lib */

int lengthOfLIS(int *nums, int numsSize, int *dp)
/*@ With (l : list Z)
    Require
      1 <= numsSize && numsSize <= 100000 &&
      Zlength(l) == numsSize &&
      IntArray::full(nums, numsSize, l) *
      IntArray::undef_full(dp, numsSize)
    Ensure
      exists d,
      LISLength(l, __return) &&
      1 <= __return && __return <= numsSize &&
      LISDPTablePrefix(l, d, numsSize) &&
      IntArray::full(nums, numsSize, l) *
      IntArray::full(dp, numsSize, d)
 */
{
  int ans = 1;
  /*@ Inv Assert
      exists d,
      nums == nums@pre && numsSize == numsSize@pre && dp == dp@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100000 &&
      Zlength(l) == numsSize@pre &&
      0 <= i && i <= numsSize@pre &&
      1 <= ans && ans <= numsSize@pre &&
      LISDPTablePrefix(l, d, i) &&
      LISBestSoFar(l, i, ans) &&
      IntArray::full(nums, numsSize@pre, l) *
      IntArray::seg(dp, 0, i, d) *
      IntArray::undef_seg(dp, i, numsSize@pre)
   */
  for (int i = 0; i < numsSize; ++i) {
    dp[i] = 1;

    /*@ Inv Assert
        exists d,
        nums == nums@pre && numsSize == numsSize@pre && dp == dp@pre &&
        1 <= numsSize@pre && numsSize@pre <= 100000 &&
        Zlength(l) == numsSize@pre &&
        0 <= i && i < numsSize@pre &&
        0 <= j && j <= i &&
        1 <= ans && ans <= numsSize@pre &&
        LISBestSoFar(l, i, ans) &&
        LISInnerProgress(l, d, i, j) &&
        IntArray::full(nums, numsSize@pre, l) *
        IntArray::seg(dp, 0, i + 1, d) *
        IntArray::undef_seg(dp, i + 1, numsSize@pre)
     */
    for (int j = 0; j < i; ++j) {
      if (nums[j] < nums[i]) {
        int candidate = dp[j] + 1;
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
        0 <= i && i < numsSize@pre &&
        1 <= ans && ans <= numsSize@pre &&
        LISBestSoFar(l, i, ans) &&
        LISDPTablePrefix(l, d, i + 1) &&
        IntArray::full(nums, numsSize@pre, l) *
        IntArray::seg(dp, 0, i + 1, d) *
        IntArray::undef_seg(dp, i + 1, numsSize@pre)
     */
    if (dp[i] > ans) {
      ans = dp[i];
    }
    /*@ Assert
        exists d,
        nums == nums@pre && numsSize == numsSize@pre && dp == dp@pre &&
        1 <= numsSize@pre && numsSize@pre <= 100000 &&
        Zlength(l) == numsSize@pre &&
        0 <= i && i < numsSize@pre &&
        1 <= ans && ans <= numsSize@pre &&
        LISBestSoFar(l, i + 1, ans) &&
        LISDPTablePrefix(l, d, i + 1) &&
        IntArray::full(nums, numsSize@pre, l) *
        IntArray::seg(dp, 0, i + 1, d) *
        IntArray::undef_seg(dp, i + 1, numsSize@pre)
     */
  }

  /*@ Assert
      exists d,
      nums == nums@pre && numsSize == numsSize@pre && dp == dp@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100000 &&
      Zlength(l) == numsSize@pre &&
      1 <= ans && ans <= numsSize@pre &&
      LISLength(l, ans) &&
      LISDPTablePrefix(l, d, numsSize@pre) &&
      IntArray::full(nums, numsSize@pre, l) *
      IntArray::full(dp, numsSize@pre, d)
   */
  return ans;
}
