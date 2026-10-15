/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P020_433A_kitahara_harukis_gift_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P020_433A_kitahara_harukis_gift_lib
*/

/*
 * Codeforces 433/A - Kitahara Haruki's Gift  (rating 1100, BRUTE FORCE)
 *
 * Work in units of 100 grams, so weights are 1 and 2 and the total is at most
 * 200.  A subset-sum bitmask over the reachable half-weights decides whether
 * one friend can receive exactly half of the total.
 */

// #include <stdio.h>
#include "string.h"
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (SolverReturnBridge : Z -> Z -> Prop)
      (PrefixUnitTotal : list Z -> Z -> Z -> Prop)
      (ReachTable : list Z -> Z -> Z -> list Z -> Prop)
      (ReachInnerProgress : list Z -> Z -> Z -> Z -> list Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P020_433A_kitahara_harukis_gift_lib */

/* solver: pure.  1 if the apples w[0..n-1] (100 or 200 g) split evenly. */
static int solver(const int *w, int n)
/* QCP_INSERT_BEGIN:shard09-P020-solver-contract */
/*@ With (weights : list Z)
    Require
      1 <= n && n <= 100 &&
      (forall i, (0 <= i && i < n) =>
        (weights[i] == 100 || weights[i] == 200)) &&
      n == Zlength(weights) && IntArray::full(w, n, weights)
    Ensure
      exists (out : Z),
        Spec(weights, out) &&
        SolverReturnBridge(out, __return) && IntArray::full(w, n, weights)
*/
/* QCP_INSERT_END:shard09-P020-solver-contract */
{
    int total = 0;
    /*@ Inv Assert
          w == w@pre && n == n@pre &&
          (forall j, (0 <= j && j < n@pre) =>
            (weights[j] == 100 || weights[j] == 200)) &&
          n@pre == Zlength(weights) &&
          1 <= n@pre && n@pre <= 100 &&
          0 <= i && i <= n@pre &&
          0 <= total && total <= 2 * i &&
          PrefixUnitTotal(weights, i, total) &&
          IntArray::full(w@pre, n@pre, weights)
    */
    for (int i = 0; i < n; i++)
        total += w[i] / 100;
    if (total % 2)
        /*@ Assert
              w == w@pre && n == n@pre &&
              (forall j, (0 <= j && j < n@pre) =>
                (weights[j] == 100 || weights[j] == 200)) &&
              n@pre == Zlength(weights) &&
              1 <= n@pre && n@pre <= 100 &&
              0 <= total && total <= 200 &&
              PrefixUnitTotal(weights, n@pre, total) &&
              Spec(weights, 0) && SolverReturnBridge(0, 0) &&
              IntArray::full(w@pre, n@pre, weights)
        */
        return 0;
    char reach[205];
    /*@ Assert
          w == w@pre && n == n@pre &&
          (forall j, (0 <= j && j < n@pre) =>
            (weights[j] == 100 || weights[j] == 200)) &&
          n@pre == Zlength(weights) &&
          1 <= n@pre && n@pre <= 100 &&
          0 <= total && total <= 200 && total % 2 == 0 &&
          PrefixUnitTotal(weights, n@pre, total) &&
          0 <= sizeof(char[205]) && sizeof(char[205]) < INT_MAX &&
          IntArray::full(w@pre, n@pre, weights) *
          CharArray::undef_full(
            pointer_offset(reach, 0, sizeof(char), signed char),
            sizeof(char[205]))
    */
    memset(reach, 0, sizeof reach);
    /*@ Assert
          w == w@pre && n == n@pre &&
          (forall j, (0 <= j && j < n@pre) =>
            (weights[j] == 100 || weights[j] == 200)) &&
          n@pre == Zlength(weights) &&
          1 <= n@pre && n@pre <= 100 &&
          0 <= total && total <= 200 && total % 2 == 0 &&
          PrefixUnitTotal(weights, n@pre, total) &&
          IntArray::full(w@pre, n@pre, weights) *
          CharArray::full(reach, 205, repeat_Z(0, 205))
    */
    reach[0] = 1;
    /*@ Assert
          exists reach_l,
            w == w@pre && n == n@pre &&
            (forall j, (0 <= j && j < n@pre) =>
              (weights[j] == 100 || weights[j] == 200)) &&
            n@pre == Zlength(weights) &&
            1 <= n@pre && n@pre <= 100 &&
            0 <= total && total <= 200 && total % 2 == 0 &&
            PrefixUnitTotal(weights, n@pre, total) &&
            ReachTable(weights, 0, total, reach_l) &&
            IntArray::full(w@pre, n@pre, weights) *
            CharArray::full(reach, 205, reach_l)
    */
    /*@ Inv Assert
          exists reach_l,
            w == w@pre && n == n@pre &&
            (forall j, (0 <= j && j < n@pre) =>
              (weights[j] == 100 || weights[j] == 200)) &&
            n@pre == Zlength(weights) &&
            1 <= n@pre && n@pre <= 100 &&
            0 <= total && total <= 200 && total % 2 == 0 &&
            PrefixUnitTotal(weights, n@pre, total) &&
            0 <= i && i <= n@pre &&
            ReachTable(weights, i, total, reach_l) &&
            IntArray::full(w@pre, n@pre, weights) *
            CharArray::full(reach, 205, reach_l)
    */
    for (int i = 0; i < n; i++) {
        int u = w[i] / 100;
        /*@ Inv Assert
              exists reach_l,
                w == w@pre && n == n@pre &&
                (forall j, (0 <= j && j < n@pre) =>
                  (weights[j] == 100 || weights[j] == 200)) &&
                n@pre == Zlength(weights) &&
                1 <= n@pre && n@pre <= 100 &&
                0 <= total && total <= 200 && total % 2 == 0 &&
                PrefixUnitTotal(weights, n@pre, total) &&
                0 <= i && i < n@pre &&
                u == weights[i] / 100 && 1 <= u && u <= 2 &&
                u - 1 <= s && s <= total &&
                ReachInnerProgress(weights, i, s, total, reach_l) &&
                IntArray::full(w@pre, n@pre, weights) *
                CharArray::full(reach, 205, reach_l)
        */
        for (int s = total; s >= u; s--)
            if (reach[s - u])
                reach[s] = 1;
        /*@ Assert
              exists reach_l,
                w == w@pre && n == n@pre &&
                (forall j, (0 <= j && j < n@pre) =>
                  (weights[j] == 100 || weights[j] == 200)) &&
                n@pre == Zlength(weights) &&
                1 <= n@pre && n@pre <= 100 &&
                0 <= total && total <= 200 && total % 2 == 0 &&
                PrefixUnitTotal(weights, n@pre, total) &&
                0 <= i && i < n@pre &&
                u == weights[i] / 100 && 1 <= u && u <= 2 &&
                ReachTable(weights, i + 1, total, reach_l) &&
                IntArray::full(w@pre, n@pre, weights) *
                CharArray::full(reach, 205, reach_l)
        */
    }
    /*@ Assert
          exists reach_l,
            w == w@pre && n == n@pre &&
            (forall j, (0 <= j && j < n@pre) =>
              (weights[j] == 100 || weights[j] == 200)) &&
            n@pre == Zlength(weights) &&
            1 <= n@pre && n@pre <= 100 &&
            0 <= total && total <= 200 && total % 2 == 0 &&
            0 <= total / 2 && total / 2 < 205 &&
            PrefixUnitTotal(weights, n@pre, total) &&
            ReachTable(weights, n@pre, total, reach_l) &&
            Spec(weights, reach_l[total / 2]) &&
            SolverReturnBridge(reach_l[total / 2], reach_l[total / 2]) &&
            IntArray::full(w@pre, n@pre, weights) *
            CharArray::full(reach, 205, reach_l)
    */
    return reach[total / 2];
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static int w[105];
//     for (int i = 0; i < n; i++)
//         scanf("%d", &w[i]);
//     puts(solver(w, n) ? "YES" : "NO");
//     return 0;
// }
