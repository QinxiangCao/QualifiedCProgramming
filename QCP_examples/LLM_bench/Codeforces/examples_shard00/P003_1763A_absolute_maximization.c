/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib
*/

/* Codeforces 1763/A - Absolute Maximization */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P003_1763A_absolute_maximization.support */
/*@ Extern Coq
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (Spec : list Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P003_1763A_absolute_maximization_lib */
/*@ Extern Coq
      (BitwiseScanState : list Z -> Z -> Z -> Z -> Prop)
*/
/* QCP_INSERT_END:P003_1763A_absolute_maximization.support */
static int solver(const int *a, int n)
/* QCP_INSERT_BEGIN:P003_1763A_absolute_maximization.contract */
/*@ With (input : list Z)
    Require
      n == Zlength(input) &&
      3 <= Zlength(input) && Zlength(input) <= 512 &&
      (forall i, (0 <= i && i < Zlength(input)) =>
        (0 <= input[i] && input[i] < 1024)) &&
      IntArray::full(a, n, input) * IntArray::undef_seg(a, n, 512)
    Ensure
      Spec(input, __return) &&
      IntArray::full(a, n, input) * IntArray::undef_seg(a, n, 512)
*/
/* QCP_INSERT_END:P003_1763A_absolute_maximization.contract */

{
    int all_or = 0, all_and = a[0];
    /*@ Inv Assert
          a == a@pre && n == n@pre &&
          n == Zlength(input) &&
          3 <= n && n <= 512 &&
          0 <= i && i <= n &&
          (forall k, (0 <= k && k < n) =>
            (0 <= input[k] && input[k] < 1024)) &&
          0 <= all_or && all_or < 1024 &&
          0 <= all_and && all_and < 1024 &&
          BitwiseScanState(input, i, all_or, all_and) &&
          IntArray::full(a, n, input) * IntArray::undef_seg(a, n, 512)
    */
    for (int i = 0; i < n; ++i) {
        all_or |= a[i];
        all_and &= a[i];
    }
    return all_or - all_and;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1) return 0;
//     while (t--) {
//         int n, a[512]; scanf("%d", &n);
//         for (int i = 0; i < n; ++i) scanf("%d", &a[i]);
//         printf("%d\n", solver(a, n));
//     }
//     return 0;
// }
