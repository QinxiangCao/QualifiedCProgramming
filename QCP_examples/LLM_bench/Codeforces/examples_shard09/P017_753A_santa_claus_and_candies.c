/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P017_753A_santa_claus_and_candies_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P017_753A_santa_claus_and_candies_lib
*/

/*
 * Codeforces 753/A - Santa Claus and Candies  (rating 1000, GREEDY)
 *
 * Handing out 1, 2, 3, ... keeps the totals as small as possible, so the
 * largest k is the one with k(k+1)/2 <= n.  Give 1..k and add the leftover
 * n - k(k+1)/2 (which is < k+1) to the last child, keeping all values distinct.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : Z -> list Z -> Prop)
      (triangular : Z -> Z)
      (CandyPrefix : Z -> list Z -> Prop)
      (GreedyCandyPlan : Z -> Z -> list Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P017_753A_santa_claus_and_candies_lib */

/* solver: pure.  Fills out[] with the gift sizes and returns their count. */
static int solver(int n, int *out)
/* QCP_INSERT_BEGIN:shard09-P017-solver-contract */
/*@
    Require
      1 <= n && n <= 1000 &&
      IntArray::undef_full(out, n)
    Ensure
      exists (out_spec : list Z),
        Spec(n, out_spec) &&
        __return == Zlength(out_spec) && IntArray::full(out, Zlength(out_spec), out_spec) * IntArray::undef_seg(out, Zlength(out_spec), n)
*/
/* QCP_INSERT_END:shard09-P017-solver-contract */
{
    int k = 0;
    long long used = 0;
    /*@ Inv Assert
      n == n@pre && out == out@pre &&
      1 <= n@pre && n@pre <= 1000 &&
      0 <= k && k <= n@pre &&
      used == triangular(k) && 0 <= used && used <= n@pre &&
      IntArray::undef_full(out, n@pre)
    */
    while (used + (k + 1) <= n) {
        k++;
        used += k;
    }
    /*@ Inv Assert
      exists (written : list Z),
        n == n@pre && out == out@pre &&
        1 <= n@pre && n@pre <= 1000 &&
        1 <= k && k <= n@pre &&
        used == triangular(k) && 0 <= used && used <= n@pre &&
        n@pre < used + (k + 1) &&
        0 <= i && i <= k &&
        CandyPrefix(i, written) &&
        IntArray::seg(out, 0, i, written) *
        IntArray::undef_seg(out, i, n@pre)
    */
    for (int i = 0; i < k; i++)
        out[i] = i + 1;
    out[k - 1] += (int)(n - used);
    /*@ Assert
      exists (out_spec : list Z),
        n == n@pre && out == out@pre &&
        1 <= n@pre && n@pre <= 1000 &&
        1 <= k && k <= n@pre &&
        used == triangular(k) && 0 <= used && used <= n@pre &&
        n@pre < used + (k + 1) &&
        GreedyCandyPlan(n@pre, k, out_spec) &&
        Spec(n@pre, out_spec) &&
        IntArray::full(out, k, out_spec) *
        IntArray::undef_seg(out, k, n@pre)
    */
    return k;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static int out[100];
//     int k = solver(n, out);
//     printf("%d\n", k);
//     for (int i = 0; i < k; i++)
//         printf("%d%c", out[i], i + 1 == k ? '\n' : ' ');
//     return 0;
// }
