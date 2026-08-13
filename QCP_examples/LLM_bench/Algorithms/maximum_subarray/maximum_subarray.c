



/*@ Extern Coq
      (max_Z : Z -> Z -> Z)
      (MaxSuffixSumPrefix : list Z -> Z -> Z -> Prop)
      (MaxSubarraySumPrefix : list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_lib */

int max(int a, int b)
/*@ Require emp
    Ensure __return == max_Z(a, b) && emp
 */
{
    return (a > b) ? a : b;
}

int max_sub_array(int *arr, int n)
/*@ With (l : list Z)
    Require
      1 <= n && n <= 100000 &&
      Zlength(l) == n &&
      IntArray::full(arr, n, l) &&
      (forall (k : Z), (0 <= k && k < n) => (-10000 <= l[k] && l[k] <= 10000))
    Ensure
      MaxSubarraySumPrefix(l, n, __return) &&
      IntArray::full(arr, n, l)
 */
{
    if (n == 0) {
        return 0;
    }

    int cur = arr[0]; 
    int res = arr[0];  

    /*@ Assert
      arr == arr@pre && n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      cur == l[0] && res == l[0] &&
      -10000 <= cur && cur <= 10000 &&
      -10000 <= res && res <= 10000 &&
      MaxSuffixSumPrefix(l, 1, cur) &&
      MaxSubarraySumPrefix(l, 1, res) &&
      IntArray::full(arr, n@pre, l) &&
      (forall (k : Z), (0 <= k && k < n@pre) => (-10000 <= l[k] && l[k] <= 10000))
     */

    /*@ Inv Assert
      arr == arr@pre && n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      1 <= i && i <= n@pre &&
      -10000 <= cur && cur <= 1000000000 &&
      -10000 <= res && res <= 1000000000 &&
      MaxSuffixSumPrefix(l, i, cur) &&
      MaxSubarraySumPrefix(l, i, res) &&
      IntArray::full(arr, n@pre, l) &&
      (forall (k : Z), (0 <= k && k < n@pre) => (-10000 <= l[k] && l[k] <= 10000))
     */
    for (int i = 1; i < n; i++) {
        /*@ Assert
          arr == arr@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          Zlength(l) == n@pre &&
          1 <= i && i < n@pre &&
          -10000 <= cur && cur <= 1000000000 &&
          -10000 <= res && res <= 1000000000 &&
          INT_MIN <= cur + l[i] && cur + l[i] <= INT_MAX &&
          MaxSuffixSumPrefix(l, i, cur) &&
          MaxSubarraySumPrefix(l, i, res) &&
          IntArray::full(arr, n@pre, l) &&
          (forall (k : Z), (0 <= k && k < n@pre) => (-10000 <= l[k] && l[k] <= 10000))
         */
        cur = max(arr[i], cur + arr[i]);
        /*@ Assert
          arr == arr@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          Zlength(l) == n@pre &&
          1 <= i && i < n@pre &&
          -10000 <= cur && cur <= 1000000000 &&
          -10000 <= res && res <= 1000000000 &&
          MaxSuffixSumPrefix(l, i + 1, cur) &&
          MaxSubarraySumPrefix(l, i, res) &&
          IntArray::full(arr, n@pre, l) &&
          (forall (k : Z), (0 <= k && k < n@pre) => (-10000 <= l[k] && l[k] <= 10000))
         */
        res = max(res, cur);
        /*@ Assert
          arr == arr@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          Zlength(l) == n@pre &&
          1 <= i && i < n@pre &&
          -10000 <= cur && cur <= 1000000000 &&
          -10000 <= res && res <= 1000000000 &&
          MaxSuffixSumPrefix(l, i + 1, cur) &&
          MaxSubarraySumPrefix(l, i + 1, res) &&
          IntArray::full(arr, n@pre, l) &&
          (forall (k : Z), (0 <= k && k < n@pre) => (-10000 <= l[k] && l[k] <= 10000))
         */
    }
    /*@ Assert
      arr == arr@pre && n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      -10000 <= cur && cur <= 1000000000 &&
      MaxSuffixSumPrefix(l, n@pre, cur) &&
      MaxSubarraySumPrefix(l, n@pre, res) &&
      IntArray::full(arr, n@pre, l)
     */
    return res;
}
