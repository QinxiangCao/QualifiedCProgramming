



/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (MSISMaximum : list Z -> Z -> Prop)
      (MSISDPTablePrefix : list Z -> list Z -> Z -> Prop)
      (MSISInnerProgress : list Z -> list Z -> Z -> Z -> Prop)
      (MSISBestSoFar : list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.max_sum_increasing_sequence.max_sum_increasing_sequence_lib */

int maxSumIncreasingSequence(int *nums, int numsSize)
/*@ With (l : list Z)
    Require
      1 <= numsSize && numsSize <= 100000 &&
      Zlength(l) == numsSize &&
      Forall(Z::le(1), l) && Forall(Z::ge(10000), l) &&
      IntArray::full(nums, numsSize, l)
    Ensure
      MSISMaximum(l, __return) &&
      IntArray::full(nums, numsSize, l)
 */
{
  int dp[100000];

  dp[0] = nums[0];
  int ans = nums[0];
  /*@ Inv Assert
      exists d,
      nums == nums@pre && numsSize == numsSize@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100000 &&
      Zlength(l) == numsSize@pre &&
      1 <= i && i <= numsSize@pre &&
      1 <= ans && ans <= i * 10000 &&
      Zlength(d) == i &&
      (forall (k : Z), (0 <= k && k < i) => (1 <= d[k] && d[k] <= (k + 1) * 10000)) &&
      MSISDPTablePrefix(l, d, i) &&
      MSISBestSoFar(l, i, ans) &&
      Forall(Z::le(1), l) && Forall(Z::ge(10000), l) &&
      IntArray::full(nums, numsSize@pre, l) *
      IntArray::seg(dp, 0, i, d) *
      IntArray::undef_seg(dp, i, 100000)
   */
  for (int i = 1; i < numsSize; ++i) {
    dp[i] = nums[i];
    /*@ Inv Assert
        exists d,
        nums == nums@pre && numsSize == numsSize@pre &&
        1 <= numsSize@pre && numsSize@pre <= 100000 &&
        Zlength(l) == numsSize@pre &&
        1 <= i && i < numsSize@pre &&
        0 <= j && j <= i &&
        1 <= ans && ans <= i * 10000 &&
        MSISBestSoFar(l, i, ans) &&
        Zlength(d) == i + 1 &&
        (forall (k : Z), (0 <= k && k < i + 1) => (1 <= d[k] && d[k] <= (k + 1) * 10000)) &&
        MSISInnerProgress(l, d, i, j) &&
        Forall(Z::le(1), l) && Forall(Z::ge(10000), l) &&
        IntArray::full(nums, numsSize@pre, l) *
        IntArray::seg(dp, 0, i + 1, d) *
        IntArray::undef_seg(dp, i + 1, 100000)
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
        nums == nums@pre && numsSize == numsSize@pre &&
        1 <= numsSize@pre && numsSize@pre <= 100000 &&
        Zlength(l) == numsSize@pre &&
        1 <= i && i < numsSize@pre &&
        1 <= ans && ans <= i * 10000 &&
        MSISBestSoFar(l, i, ans) &&
        Zlength(d) == i + 1 &&
        (forall (k : Z), (0 <= k && k < i + 1) => (1 <= d[k] && d[k] <= (k + 1) * 10000)) &&
        MSISDPTablePrefix(l, d, i + 1) &&
        Forall(Z::le(1), l) && Forall(Z::ge(10000), l) &&
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
      MSISMaximum(l, ans) &&
      IntArray::full(nums, numsSize@pre, l) *
      IntArray::undef_full(dp, 100000)
   */
  return ans;
}
