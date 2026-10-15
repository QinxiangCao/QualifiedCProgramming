/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines_lib
*/

/* Codeforces 1113/B - Sasha and Magnetic Machines */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P030_1113B_sasha_and_magnetic_machines.support */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P030_1113B_sasha_and_magnetic_machines_lib */
/* QCP_INSERT_END:P030_1113B_sasha_and_magnetic_machines.support */
/*@ Extern Coq
      (PrefixSummary : list Z -> Z -> Z -> Z -> Prop)
      (SearchMinimum : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/
static int solver(const int *a, int n)/* QCP_INSERT_BEGIN:P030_1113B_sasha_and_magnetic_machines.contract */

/*@ With (values : list Z)
    Require
      2 <= Zlength(values) && Zlength(values) <= 50000 &&
      (forall i, (0 <= i && i < Zlength(values)) => (1 <= values[i] && values[i] <= 100)) &&
      n == Zlength(values) && IntArray::full(a, n, values)
    Ensure
      Spec(values, __return) && IntArray::full(a, n, values)
*/
/* QCP_INSERT_END:P030_1113B_sasha_and_magnetic_machines.contract */

{
    int mn = 101, sum = 0;
    /*@ Inv Assert
          a == a@pre && n == n@pre &&
          2 <= Zlength(values) && Zlength(values) <= 50000 &&
          (forall k, (0 <= k && k < Zlength(values)) =>
            (1 <= values[k] && values[k] <= 100)) &&
          n@pre == Zlength(values) &&
          0 <= i && i <= n@pre &&
          0 <= sum && sum <= 100 * i &&
          1 <= mn && mn <= 101 &&
          PrefixSummary(values, i, sum, mn) &&
          IntArray::full(a, n@pre, values)
    */
    for (int i = 0; i < n; ++i) {
        sum += a[i];
        if (a[i] < mn) mn = a[i];
    }
    int answer = sum;
    /*@ Inv Assert
          a == a@pre && n == n@pre &&
          2 <= Zlength(values) && Zlength(values) <= 50000 &&
          (forall k, (0 <= k && k < Zlength(values)) =>
            (1 <= values[k] && values[k] <= 100)) &&
          n@pre == Zlength(values) &&
          PrefixSummary(values, n@pre, sum, mn) &&
          0 <= sum && sum <= 100 * n@pre &&
          1 <= mn && mn <= 100 &&
          0 <= i && i <= n@pre &&
          0 <= answer && answer <= sum &&
          SearchMinimum(values, sum, mn, i, 2, answer) &&
          IntArray::full(a, n@pre, values)
    */
    for (int i = 0; i < n; ++i) {
        /*@ Inv Assert
              a == a@pre && n == n@pre &&
              2 <= Zlength(values) && Zlength(values) <= 50000 &&
              (forall k, (0 <= k && k < Zlength(values)) =>
                (1 <= values[k] && values[k] <= 100)) &&
              n@pre == Zlength(values) &&
              PrefixSummary(values, n@pre, sum, mn) &&
              0 <= sum && sum <= 100 * n@pre &&
              1 <= mn && mn <= 100 &&
              0 <= i && i < n@pre &&
              2 <= x && x <= values[i] + 1 &&
              0 <= answer && answer <= sum &&
              SearchMinimum(values, sum, mn, i, x, answer) &&
              IntArray::full(a, n@pre, values)
        */
        for (int x = 2; x <= a[i]; ++x) {
            if (a[i] % x) continue;
            int candidate = sum - a[i] - mn + a[i] / x + mn * x;
            if (candidate < answer) answer = candidate;
        }
    }
    return answer;
}

// int main(void)
// {
//     int n, a[50000];
//     if (scanf("%d", &n) != 1) return 0;
//     for (int i = 0; i < n; ++i) scanf("%d", &a[i]);
//     printf("%d\n", solver(a, n));
//     return 0;
// }
