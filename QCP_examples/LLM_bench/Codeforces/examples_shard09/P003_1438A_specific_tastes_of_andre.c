/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P003_1438A_specific_tastes_of_andre_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P003_1438A_specific_tastes_of_andre_lib
*/

/*
 * Codeforces 1438/A - Specific Tastes of Andre  (rating 800, CONSTRUCTIVE)
 *
 * If every element equals the same value v, a subarray of length L sums to
 * L*v, which is divisible by L.  So the constant array [1, 1, ..., 1] is
 * perfect and satisfies 1 <= a_i <= 100.
 */

// #include <stdio.h>
/*@ Extern Coq 
        (Spec : Z -> list Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P003_1438A_specific_tastes_of_andre_lib */

/* solver: pure.  Fills out[0..n-1] with a perfect array of length n. */
static void solver(int n, int *out)
/* QCP_INSERT_BEGIN:shard09-P003-solver-contract */
/*@
    Require
      1 <= n && n <= 100 &&
      IntArray::undef_full(out, n)
    Ensure
      exists (out_spec : list Z),
        Spec(n, out_spec) &&
        IntArray::full(out, n, out_spec)
*/
/* QCP_INSERT_END:shard09-P003-solver-contract */
{
    /*@ Inv Assert
      exists (written : list Z),
        n == n@pre && out == out@pre &&
        1 <= n@pre && n@pre <= 100 &&
        0 <= i && i <= n@pre &&
        Zlength(written) == i &&
        (forall (k : Z),
          (0 <= k && k < i) => written[k] == 1) &&
        IntArray::seg(out, 0, i, written) *
        IntArray::undef_seg(out, i, n@pre)
    */
    for (int i = 0; i < n; i++)
        out[i] = 1;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         int n;
//         static int out[105];
//         scanf("%d", &n);
//         solver(n, out);
//         for (int i = 0; i < n; i++)
//             printf("%d%c", out[i], i + 1 == n ? '\n' : ' ');
//     }
//     return 0;
// }
