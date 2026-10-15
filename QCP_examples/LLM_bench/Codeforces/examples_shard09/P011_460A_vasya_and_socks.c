/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_lib
*/

/*
 * Codeforces 460/A - Vasya and Socks  (rating 900, IMPLEMENTATION)
 *
 * Simulate day by day: each day uses one pair, and every m-th evening adds
 * one; n, m <= 100 so the loop is tiny.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P011_460A_vasya_and_socks_lib */

/* solver: pure.  Number of consecutive days until the socks run out. */
static int solver(int n, int m)
/* QCP_INSERT_BEGIN:shard09-P011-solver-contract */
/*@
    Require
      1 <= n && n <= 100 && 2 <= m && m <= 100 &&
      emp
    Ensure
      Spec(n@pre, m@pre, __return) &&
      emp
*/
/* QCP_INSERT_END:shard09-P011-solver-contract */
{
    int days = 0;
    /*@ Inv Assert
          1 <= n@pre && n@pre <= 100 &&
          2 <= m && m <= 100 && m == m@pre &&
          0 <= days && days <= 200 &&
          0 <= n && n <= 100 &&
          n == n@pre + days / m - days &&
          (forall (d : Z),
             (1 <= d && d <= days) =>
             n@pre + (d - 1) / m - (d - 1) > 0)
    */
    while (n > 0) {
        days++;
        n--;
        if (days % m == 0)
            n++;
    }
    return days;
}

// int main(void)
// {
//     int n, m;
//     if (scanf("%d %d", &n, &m) != 2)
//         return 0;
//     printf("%d\n", solver(n, m));
//     return 0;
// }
