

/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
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
      Forall(Z::le(-10000), l) && Forall(Z::ge(10000), l)
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
      Forall(Z::le(-10000), l) && Forall(Z::ge(10000), l)
     */
    for (int i = 1; i < n; i++) {

        cur = max(arr[i], cur + arr[i]);

        res = max(res, cur);

    }

    return res;
}
