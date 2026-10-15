/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_lib
*/

/*
 * Codeforces 1382/B - Sequential Nim  (rating 1100, GAMES)
 *
 * Piles of exactly one stone force a move; piles with more than one let the
 * player on turn decide who faces the next pile (take all, or all but one).
 * So whoever first reaches a pile > 1 wins: with c leading ones, that is the
 * first player iff c is even.  If every pile is a single stone, parity of n
 * decides.
 */

// #include <stdio.h>
/*@ Extern Coq
      (LeadingOnes : list Z -> Z -> Prop)
      (Spec : list Z -> Z -> Prop)
      (SolverReturnBridge : Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_lib */

/* solver: pure.  1 if the first player wins on piles a[0..n-1]. */
static int solver(const int *a, int n)
/* QCP_INSERT_BEGIN:shard09-P018-solver-contract */
/*@ With (piles : list Z)
    Require
      1 <= n && n <= 100000 && (forall i, (0 <= i && i < n) => (1 <= piles[i] && piles[i] <= 1000000000)) &&
      n == Zlength(piles) && IntArray::full(a, n, piles)
    Ensure
      exists (out : Z),
        Spec(piles, out) &&
        SolverReturnBridge(out, __return) && IntArray::full(a, n, piles)
*/
/* QCP_INSERT_END:shard09-P018-solver-contract */
{
    int c = 0;
    /*@ Inv Assert
          a == a@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          n@pre == Zlength(piles) &&
          (forall i,
             (0 <= i && i < n@pre) =>
             (1 <= piles[i] && piles[i] <= 1000000000)) &&
          0 <= c && c <= n@pre &&
          (forall i, (0 <= i && i < c) => piles[i] == 1) &&
          IntArray::full(a, n@pre, piles)
    */
    while (c < n && a[c] == 1)
        c++;
    /*@ Assert
          a == a@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          n@pre == Zlength(piles) &&
          0 <= c && c <= n@pre &&
          LeadingOnes(piles, c) &&
          IntArray::full(a, n@pre, piles)
    */
    if (c == n)                     /* all piles are single stones */
        return n % 2 == 1;
    return c % 2 == 0;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static int a[100005];
//     while (t--) {
//         int n;
//         scanf("%d", &n);
//         for (int i = 0; i < n; i++)
//             scanf("%d", &a[i]);
//         puts(solver(a, n) ? "First" : "Second");
//     }
//     return 0;
// }
