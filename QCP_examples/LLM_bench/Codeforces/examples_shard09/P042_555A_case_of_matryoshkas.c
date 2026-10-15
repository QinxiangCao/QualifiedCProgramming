/*
 * Codeforces 555/A - Case of Matryoshkas  (rating 1500, IMPLEMENTATION)
 *
 * The prefix 1 -> 2 -> ... -> p that already sits at the start of some chain
 * can be kept as is.  Everything else must be taken apart: each chain of
 * length m costs m-1 extractions, minus the p-1 we keep, and then n-p
 * insertions rebuild the big chain.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Pre : Z -> list(list Z) -> Prop)
      (Spec : Z -> list(list Z) -> Z -> Prop)
      (concat : list(list Z) -> list Z)
      (usable_prefix : list(list Z) -> Z)
      (ChainLengths : list (list Z) -> list Z)
*/
/*@ Extern Coq
      (PrefixExtractionCost : list(list Z) -> Z -> Z)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P042_555A_case_of_matryoshkas_lib */

/* solver: pure.  Minimum seconds, given the total n, the chain lengths m[],
 * the number of chains k, and p = length of the usable 1..p prefix. */
static long long solver(int n, const int *m, int k, int p)
/* QCP_INSERT_BEGIN:shard09-P042-solver-contract */
/*@ With (chains : list(list Z))
    Require
      1 <= n && n <= 100000 &&
      1 <= k && k <= 100000 &&
      (forall i, (0 <= i && i < k) =>
        (1 <= ChainLengths(chains)[i] && ChainLengths(chains)[i] <= n)) &&
      Pre(n, chains) && (forall i, (0 <= i && i < n) => (1 <= concat(chains)[i] && concat(chains)[i] <= n)) &&
      k == Zlength(chains) && p == usable_prefix(chains) &&
      IntArray::full(m, k, ChainLengths(chains))
    Ensure
      Spec(n@pre, chains, __return) &&
      IntArray::full(m, k, ChainLengths(chains))
*/
/* QCP_INSERT_END:shard09-P042-solver-contract */
{
    long long ops = 0;
    /*@ Inv Assert
          n == n@pre && m == m@pre && k == k@pre && p == p@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          Pre(n@pre, chains) &&
          (forall j, (0 <= j && j < n@pre) =>
            (1 <= concat(chains)[j] && concat(chains)[j] <= n@pre)) &&
          k@pre == Zlength(chains) &&
          p@pre == usable_prefix(chains) &&
          1 <= k@pre && k@pre <= n@pre &&
          1 <= p@pre && p@pre <= n@pre &&
          (forall j, (0 <= j && j < k@pre) =>
            (1 <= ChainLengths(chains)[j] && ChainLengths(chains)[j] <= n@pre)) &&
          0 <= i && i <= k@pre &&
          0 <= ops && ops <= n@pre &&
          ops == PrefixExtractionCost(chains, i) &&
          IntArray::full(m, k@pre, ChainLengths(chains))
    */
    for (int i = 0; i < k; i++)
        ops += m[i] - 1;                  /* full disassembly */
    ops -= p - 1;                         /* the kept prefix stays nested */
    ops += n - p;                         /* re-nest everything else */
    /*@ Assert
          n == n@pre && m == m@pre && k == k@pre && p == p@pre &&
          Spec(n@pre, chains, ops) &&
          IntArray::full(m, k@pre, ChainLengths(chains))
    */
    return ops;
}

// int main(void)
// {
//     int n, k;
//     if (scanf("%d %d", &n, &k) != 2)
//         return 0;
//     static int m[100005];
//     int p = 0;
//     for (int i = 0; i < k; i++) {
//         scanf("%d", &m[i]);
//         int prev = 0, run = 0;
//         for (int j = 0; j < m[i]; j++) {
//             int a;
//             scanf("%d", &a);
//             if (j == 0 && a == 1)
//                 run = 1;
//             else if (run == j && a == prev + 1)
//                 run++;
//             prev = a;
//         }
//         if (run > p)
//             p = run;
//     }
//     if (p == 0)
//         p = 1;                            /* doll 1 is always usable alone */
//     printf("%lld\n", solver(n, m, k, p));
//     return 0;
// }
