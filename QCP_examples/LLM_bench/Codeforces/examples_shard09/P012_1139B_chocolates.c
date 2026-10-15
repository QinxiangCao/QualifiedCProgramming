/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_lib
*/

/*
 * Codeforces 1139/B - Chocolates  (rating 1000, GREEDY)
 *
 * Scan right to left keeping the count taken from the type to the right: the
 * best you may take of the current type is min(a_i, prev - 1), floored at 0.
 * Taking that maximum is never worse, since it only relaxes later (leftward)
 * constraints as little as possible while maximising this term.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (SuffixDominantState : list Z -> Z -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P012_1139B_chocolates_lib */

/* solver: pure.  Maximum number of chocolates buyable from a[0..n-1]. */
static long long solver(const int *a, int n)
/* QCP_INSERT_BEGIN:shard09-P012-solver-contract */
/*@ With (values : list Z)
    Require
      1 <= n && n <= 200000 && 
      (forall i, (0 <= i && i < n) => (1 <= values[i] && values[i] <= 1000000000)) &&
      n == Zlength(values) && IntArray::full(a, n, values)
    Ensure
      Spec(values, __return) &&
      IntArray::full(a, n, values)
*/
/* QCP_INSERT_END:shard09-P012-solver-contract */
{
    long long total = 0, prev = 0;            /* prev: taken from type i+1 */
    /*@ Inv Assert
          a == a@pre && n == n@pre &&
          1 <= n && n <= 200000 && n == Zlength(values) &&
          (forall k, (0 <= k && k < n) =>
             (1 <= values[k] && values[k] <= 1000000000)) &&
          -1 <= i && i < n &&
          0 <= total && total <= (n - i - 1) * 1000000000 &&
          0 <= prev && prev <= 1000000000 &&
          SuffixDominantState(values, i + 1, total, prev) &&
          IntArray::full(a, n, values)
     */
    for (int i = n - 1; i >= 0; i--) {
        long long take;
        if (i == n - 1)
            take = a[i];
        else {
            take = prev - 1;
            if (take > a[i])
                take = a[i];
            if (take < 0)
                take = 0;
        }
        total += take;
        prev = take;
    }
    return total;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static int a[200005];
//     for (int i = 0; i < n; i++)
//         scanf("%d", &a[i]);
//     printf("%lld\n", solver(a, n));
//     return 0;
// }
