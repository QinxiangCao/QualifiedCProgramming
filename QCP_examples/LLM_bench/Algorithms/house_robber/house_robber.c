



/*@ Extern Coq
      (RobPrefixValue : list Z -> Z -> Z -> Prop)
      (RobPrefixOpt : list Z -> Z -> Z -> Prop)
      (HouseRobberDPState : list Z -> Z -> Z -> Z -> Prop)
      (HouseRobberAnswer : list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib */

int rob(int *nums, int n)
/*@ With (l : list Z)
    Require
      0 <= n && n <= 100000 &&
      Zlength(l) == n &&
      IntArray::full(nums, n, l) &&
      (forall (k : Z), (0 <= k && k < n) => (0 <= l[k] && l[k] <= 10000))
    Ensure
      HouseRobberAnswer(l, __return) &&
      0 <= __return && __return <= 1000000000 &&
      IntArray::full(nums, n, l)
 */
{
  int prev2 = 0;
  int prev1 = 0;
  /*@ Inv Assert
      nums == nums@pre && n == n@pre &&
      0 <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      IntArray::full(nums, n@pre, l) &&
      (forall (k : Z), (0 <= k && k < n@pre) => (0 <= l[k] && l[k] <= 10000)) &&
      0 <= i && i <= n@pre &&
      0 <= prev2 && prev2 <= 1000000000 &&
      0 <= prev1 && prev1 <= 1000000000 &&
      HouseRobberDPState(l, i, prev2, prev1)
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
    /*@ Assert
      nums == nums@pre && n == n@pre &&
      0 <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      IntArray::full(nums, n@pre, l) &&
      (forall (k : Z), (0 <= k && k < n@pre) => (0 <= l[k] && l[k] <= 10000)) &&
      0 <= i && i < n@pre &&
      take == prev2 + l[i] &&
      skip == prev1 &&
      0 <= prev2 && prev2 <= 1000000000 &&
      0 <= prev1 && prev1 <= 1000000000 &&
      0 <= cur && cur <= 1000000000 &&
      HouseRobberDPState(l, i + 1, prev1, cur)
    */
    prev2 = prev1;
    prev1 = cur;
  }
  return prev1;
}
