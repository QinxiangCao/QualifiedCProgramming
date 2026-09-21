/*@ Extern Coq (ClimbingStairsCount : Z -> Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.climbing_stairs.climbing_stairs_lib */

int climbStairs(int n)
/*@ Require
      1 <= n && n <= 45 && emp
    Ensure
      ClimbingStairsCount(n, __return) && emp
 */
{
    int prev = 1;
    int curr = 1;
    int i = 2;

    /*@ Inv Assert
          n == n@pre &&
          1 <= n@pre && n@pre <= 45 &&
          2 <= i && i <= n@pre + 1 &&
          0 <= prev && 0 <= curr &&
          ClimbingStairsCount(i - 2, prev) &&
          ClimbingStairsCount(i - 1, curr)
     */
    while (i <= n) {
        int next = prev + curr;
        prev = curr;
        curr = next;
        i = i + 1;
    }

    return curr;
}
