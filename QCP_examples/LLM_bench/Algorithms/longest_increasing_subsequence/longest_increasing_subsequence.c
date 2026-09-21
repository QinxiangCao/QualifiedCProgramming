



/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (LISLength : list Z -> Z -> Prop)
      (LISDPTablePrefix : list Z -> list Z -> Z -> Prop)
      (LISInnerProgress : list Z -> list Z -> Z -> Z -> Prop)
      (LISBestSoFar : list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.longest_increasing_subsequence.longest_increasing_subsequence_lib */

int lengthOfLIS(int *nums, int numsSize)
/*@ With (l : list Z)
    Require
      1 <= numsSize && numsSize <= 100000 &&
      Zlength(l) == numsSize &&
      Forall(Z::le(-10000), l) && Forall(Z::ge(10000), l) &&
      IntArray::full(nums, numsSize, l)
    Ensure
      LISLength(l, __return) &&
      IntArray::full(nums, numsSize, l)
 */
{
  int dp[100000];

  int ans = 1;
  /*@ Inv Assert
      exists d,
      nums == nums@pre && numsSize == numsSize@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100000 &&
      Zlength(l) == numsSize@pre &&
      0 <= i && i <= numsSize@pre &&
      1 <= ans && ans <= numsSize@pre &&
      Zlength(d) == i &&
      (forall (k : Z), (0 <= k && k < i) => (1 <= d[k] && d[k] <= k + 1)) &&
      LISDPTablePrefix(l, d, i) &&
      LISBestSoFar(l, i, ans) &&
      IntArray::full(nums, numsSize@pre, l) *
      IntArray::seg(dp, 0, i, d) *
      IntArray::undef_seg(dp, i, 100000)
   */
  for (int i = 0; i < numsSize; ++i) {
    dp[i] = 1;

    /*@ Inv Assert
        exists d,
        nums == nums@pre && numsSize == numsSize@pre &&
        1 <= numsSize@pre && numsSize@pre <= 100000 &&
        Zlength(l) == numsSize@pre &&
        0 <= i && i < numsSize@pre &&
        0 <= j && j <= i &&
        1 <= ans && ans <= numsSize@pre &&
        LISBestSoFar(l, i, ans) &&
        Zlength(d) == i + 1 &&
        (forall (k : Z), (0 <= k && k < i + 1) => (1 <= d[k] && d[k] <= k + 1)) &&
        LISInnerProgress(l, d, i, j) &&
        IntArray::full(nums, numsSize@pre, l) *
        IntArray::seg(dp, 0, i + 1, d) *
        IntArray::undef_seg(dp, i + 1, 100000)
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
        nums == nums@pre && numsSize == numsSize@pre &&
        1 <= numsSize@pre && numsSize@pre <= 100000 &&
        Zlength(l) == numsSize@pre &&
        0 <= i && i < numsSize@pre &&
        1 <= ans && ans <= numsSize@pre &&
        LISBestSoFar(l, i, ans) &&
        Zlength(d) == i + 1 &&
        (forall (k : Z), (0 <= k && k < i + 1) => (1 <= d[k] && d[k] <= k + 1)) &&
        LISDPTablePrefix(l, d, i + 1) &&
        IntArray::full(nums, numsSize@pre, l) *
        IntArray::seg(dp, 0, i + 1, d) *
        IntArray::undef_seg(dp, i + 1, 100000)
     */
    if (dp[i] > ans) {
      ans = dp[i];
    }
    
  }

  
  /*@ Assert
      nums == nums@pre && numsSize == numsSize@pre &&
      LISLength(l, ans) &&
      IntArray::full(nums, numsSize@pre, l) *
      IntArray::undef_full(dp, 100000)
   */
  return ans;
}
