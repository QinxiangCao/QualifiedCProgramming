



/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (HouseRobberDPState : list Z -> Z -> Z -> Z -> Prop)
      (HouseRobberAnswer : list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib */

int rob(int *nums, int n)
/*@ With (l : list Z)
    Require
      0 <= n && n <= 100000 &&
      Zlength(l) == n &&
      Forall(Z::le(0), l) && Forall(Z::ge(10000), l) &&
      IntArray::full(nums, n, l)
    Ensure
      HouseRobberAnswer(l, __return) &&
      IntArray::full(nums, n, l)
 */
{
  int prev2 = 0;
  int prev1 = 0;
  /*@ Inv Assert
      nums == nums@pre && n == n@pre &&
      n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      Forall(Z::le(0), l) && Forall(Z::ge(10000), l) &&
      0 <= i && i <= n@pre &&
      HouseRobberDPState(l, i, prev2, prev1) &&
      IntArray::full(nums, n@pre, l)
   */
  for (int i = 0; i < n; ++i) {
    int take = prev2 + nums[i];
    int skip = prev1;
    int cur;
    if (take > skip) {
      cur = take;
    } else {
      cur = skip;
    }
    prev2 = prev1;
    prev1 = cur;
  }
  return prev1;
}
