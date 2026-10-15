/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
*/

/*
 * Codeforces 435/B - Pasha Maximizes  (rating 1400, GREEDY)
 *
 * Fill the number left to right: for each position take the largest digit
 * still reachable within the remaining swap budget (it sits at most k places
 * to the right) and bubble it into place, paying its distance.
 */

// #include <stdio.h>
// #include <string.h>
/*@ Extern Coq
      (Spec : list Z -> Z -> list Z -> Prop)
*/
/*@ Extern Coq
      (GreedyProgress : list Z -> Z -> list Z -> Z -> Z -> Prop)
      (FirstMaximumPrefix : list Z -> Z -> Z -> Z -> Prop)
      (ReachableFirstMaximum : list Z -> Z -> Z -> Z -> Prop)
      (move_left : list Z -> Z -> Z -> list Z)
*/
/*@ Extern Coq
      (GreedyExchangeClosure : list Z -> Z -> Z -> Z -> Prop)
*/
/*@ Extern Coq
      (GreedySelectionReady : list Z -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib */

/* solver: rearranges the digit string d in place using at most k adjacent
 * swaps to make it as large as possible. */
static void solver(char *d, int n, int k)
/* QCP_INSERT_BEGIN:shard09-P039-solver-contract */
/*@ With (digits : list Z)
    Require
      1 <= n && n <= 19 && 0 <= k && k <= 100 &&
      n == Zlength(digits) && digits[0] != 48 &&
      (forall i, (0 <= i && i < n) => (48 <= digits[i] && digits[i] <= 57)) &&
      CharArray::full(d, n + 1, app(digits, cons(0, nil)))
    Ensure
      exists (out : list Z),
        Spec(digits, k@pre, out) &&
        CharArray::full(d, n + 1, app(out, cons(0, nil)))
*/
/* QCP_INSERT_END:shard09-P039-solver-contract */
{
    /*@ Inv Assert
          exists (cur : list Z),
          d == d@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 19 &&
          0 <= k && k <= k@pre && k@pre <= 100 &&
          n@pre == Zlength(digits) && Zlength(cur) == n@pre &&
          digits[0] != 48 &&
          (forall p, (0 <= p && p < n@pre) =>
             (48 <= digits[p] && digits[p] <= 57)) &&
          (forall p, (0 <= p && p < n@pre) =>
             (48 <= cur[p] && cur[p] <= 57)) &&
          0 <= i && i <= n@pre &&
          GreedyProgress(digits, k@pre, cur, i, k) &&
          GreedySelectionReady(cur, i, k) &&
          CharArray::full(d@pre, n@pre + 1, app(cur, cons(0, nil)))
    */
    for (int i = 0; i < n && k > 0; i++) {
        int best = i;
        /*@ Inv Assert
              exists (cur : list Z),
              d == d@pre && n == n@pre &&
              1 <= n@pre && n@pre <= 19 &&
              0 < k && k <= k@pre && k@pre <= 100 &&
              n@pre == Zlength(digits) && Zlength(cur) == n@pre &&
              digits[0] != 48 &&
              (forall p, (0 <= p && p < n@pre) =>
                 (48 <= digits[p] && digits[p] <= 57)) &&
              (forall p, (0 <= p && p < n@pre) =>
                 (48 <= cur[p] && cur[p] <= 57)) &&
              0 <= i && i < n@pre &&
              i + 1 <= j && j <= n@pre && j <= i + k + 1 &&
              i <= best && best < j &&
              FirstMaximumPrefix(cur, i, j, best) &&
              GreedyProgress(digits, k@pre, cur, i, k) &&
              GreedySelectionReady(cur, i, k) &&
              CharArray::full(d@pre, n@pre + 1, app(cur, cons(0, nil)))
        */
        for (int j = i + 1; j < n && j - i <= k; j++)
            if (d[j] > d[best])
                best = j;
        /*@ Inv Assert
              exists (before : list Z) (cur : list Z) (start_k : Z),
              d == d@pre && n == n@pre &&
              1 <= n@pre && n@pre <= 19 &&
              0 < start_k && start_k <= k@pre && k@pre <= 100 &&
              n@pre == Zlength(digits) &&
              Zlength(before) == n@pre && Zlength(cur) == n@pre &&
              digits[0] != 48 &&
              (forall p, (0 <= p && p < n@pre) =>
                 (48 <= digits[p] && digits[p] <= 57)) &&
              (forall p, (0 <= p && p < n@pre) =>
                 (48 <= before[p] && before[p] <= 57)) &&
              (forall p, (0 <= p && p < n@pre) =>
                 (48 <= cur[p] && cur[p] <= 57)) &&
              0 <= i && i < n@pre && i <= j && j <= best && best < n@pre &&
              best - i <= start_k &&
              k == start_k - (best - j) && 0 <= k && k <= start_k &&
              ReachableFirstMaximum(before, i, start_k, best) &&
              GreedyProgress(digits, k@pre, before, i, start_k) &&
              GreedySelectionReady(before, i, start_k) &&
              GreedyExchangeClosure(before, i, start_k, best) &&
              cur == move_left(before, best, j) &&
              CharArray::full(d@pre, n@pre + 1, app(cur, cons(0, nil)))
        */
        for (int j = best; j > i; j--) {
            char tmp = d[j];
            d[j] = d[j - 1];
            d[j - 1] = tmp;
            k--;
        }
    }
}

// int main(void)
// {
//     static char d[32];
//     int k;
//     if (scanf("%31s %d", d, &k) != 2)
//         return 0;
//     solver(d, (int)strlen(d), k);
//     puts(d);
//     return 0;
// }
