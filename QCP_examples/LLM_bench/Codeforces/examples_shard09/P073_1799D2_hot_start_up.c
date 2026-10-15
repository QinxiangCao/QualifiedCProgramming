/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P073_1799D2_hot_start_up_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P073_1799D2_hot_start_up_lib
*/

/*
 * Codeforces 1799/D2 - Hot Start Up (hard version)  (rating 2100, DP)
 *
 * After running a_i, one CPU necessarily holds a_i, so a state is just "what
 * the other CPU last ran".  Running a_{i+1} on the a_i CPU adds the same cost
 * to every state (a global offset), while running it on the other CPU moves
 * every state to "other = a_i", costing the best of cold from any state or hot
 * from state a_{i+1}.  Tracking the array minimum makes each step O(1).
 */

// #include <stdio.h>

/* QCP_INSERT_BEGIN:shard09-P073-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P073_1799D2_hot_start_up_lib */
/*@ Extern Coq
      (Spec : list Z -> list Z -> list Z -> Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P073-solver-support */

/*@ Extern Coq
      (NormalizedScheduleState : list Z -> list Z -> list Z -> Z -> list Z -> Z -> Z -> Prop)
*/

#define MAXK 300005
#define INF 0x3f3f3f3f3f3f3f3fLL

/* solver: minimum total running time.  d[] is scratch of size k+1 (state 0 is
 * the idle CPU). */
static long long solver(const int *a, int n, int k, const long long *cold,
                        const long long *hot, long long *d)
/* QCP_INSERT_BEGIN:shard09-P073-solver-contract */
/*@ With (prog : list Z) (cold_costs : list Z) (hot_costs : list Z)
    Require
      1 <= n && n <= 300000 && 1 <= k && k <= 300000 && (forall i, (0 <= i && i < n) => (1 <= prog[i] && prog[i] <= k)) && (forall i, (0 <= i && i < k) => (1 <= hot_costs[i] && hot_costs[i] <= cold_costs[i] && cold_costs[i] <= 1000000000)) &&
      n == Zlength(prog) && k == Zlength(cold_costs) && Zlength(hot_costs) == k &&
      IntArray::full(a, n, prog) * Int64Array::full(cold, k + 1, cons(0, cold_costs)) * Int64Array::full(hot, k + 1, cons(0, hot_costs)) * Int64Array::undef_full(d, k + 1)
    Ensure
      Spec(prog, cold_costs, hot_costs, __return) &&
        IntArray::full(a, n, prog) * Int64Array::full(cold, k + 1, cons(0, cold_costs)) * Int64Array::full(hot, k + 1, cons(0, hot_costs)) * Int64Array::full_shape(d, k + 1)
*/
/* QCP_INSERT_END:shard09-P073-solver-contract */
{
    /*@ Inv Assert
          exists (initialized : list Z),
          a == a@pre && n == n@pre && k == k@pre &&
          cold == cold@pre && hot == hot@pre && d == d@pre &&
          1 <= n@pre && n@pre <= 300000 &&
          1 <= k@pre && k@pre <= 300000 &&
          n@pre == Zlength(prog) &&
          k@pre == Zlength(cold_costs) &&
          k@pre == Zlength(hot_costs) &&
          (forall q, (0 <= q && q < n@pre) =>
             (1 <= prog[q] && prog[q] <= k@pre)) &&
          (forall q, (0 <= q && q < k@pre) =>
             (1 <= hot_costs[q] && hot_costs[q] <= cold_costs[q] &&
              cold_costs[q] <= 1000000000)) &&
          0 <= j && j <= k@pre + 1 &&
          Zlength(initialized) == j &&
          (forall q, (0 <= q && q < j) =>
             initialized[q] == 4557430888798830399) &&
          IntArray::full(a@pre, n@pre, prog) *
          Int64Array::full(cold@pre, k@pre + 1, cons(0, cold_costs)) *
          Int64Array::full(hot@pre, k@pre + 1, cons(0, hot_costs)) *
          Int64Array::seg(d@pre, 0, j, initialized) *
          Int64Array::undef_seg(d@pre, j, k@pre + 1)
    */
    for (int j = 0; j <= k; j++)
        d[j] = INF;
    d[0] = 0;                             /* second CPU still idle */
    long long off = cold[a[0]], mind = 0;
    /*@ Inv Assert
          exists (dp : list Z),
          a == a@pre && n == n@pre && k == k@pre &&
          cold == cold@pre && hot == hot@pre && d == d@pre &&
          1 <= n@pre && n@pre <= 300000 &&
          1 <= k@pre && k@pre <= 300000 &&
          n@pre == Zlength(prog) &&
          k@pre == Zlength(cold_costs) &&
          k@pre == Zlength(hot_costs) &&
          (forall q, (0 <= q && q < n@pre) =>
             (1 <= prog[q] && prog[q] <= k@pre)) &&
          (forall q, (0 <= q && q < k@pre) =>
             (1 <= hot_costs[q] && hot_costs[q] <= cold_costs[q] &&
              cold_costs[q] <= 1000000000)) &&
          1 <= i && i <= n@pre &&
          Zlength(dp) == k@pre + 1 && dp[0] == 0 &&
          i <= off && off <= i * 1000000000 &&
          -i * 1000000000 <= mind && mind <= 0 &&
          i <= mind + off && mind + off <= i * 1000000000 &&
          (forall q, (0 <= q && q <= k@pre) =>
             (dp[q] == 4557430888798830399 ||
              (-i * 1000000000 <= dp[q] &&
               dp[q] <= i * 1000000000))) &&
          NormalizedScheduleState(prog, cold_costs, hot_costs,
                                  i, dp, off, mind) &&
          IntArray::full(a@pre, n@pre, prog) *
          Int64Array::full(cold@pre, k@pre + 1, cons(0, cold_costs)) *
          Int64Array::full(hot@pre, k@pre + 1, cons(0, hot_costs)) *
          Int64Array::full(d@pre, k@pre + 1, dp)
    */
    for (int i = 1; i < n; i++) {
        int x = a[i], y = a[i - 1];
        long long costA = (x == y) ? hot[x] : cold[x];
        long long candB = mind + off + cold[x];
        if (d[x] < INF) {
            long long viaHot = d[x] + off + hot[x];
            if (viaHot < candB)
                candB = viaHot;
        }
        off += costA;                     /* run x on the CPU that held y */
        long long ny = candB - off;       /* run x on the other CPU instead */
        /*@ Assert
              exists (dp : list Z),
              a == a@pre && n == n@pre && k == k@pre &&
              cold == cold@pre && hot == hot@pre && d == d@pre &&
              1 <= n@pre && n@pre <= 300000 &&
              1 <= k@pre && k@pre <= 300000 &&
              n@pre == Zlength(prog) &&
              k@pre == Zlength(cold_costs) &&
              k@pre == Zlength(hot_costs) &&
              (forall q, (0 <= q && q < n@pre) =>
                 (1 <= prog[q] && prog[q] <= k@pre)) &&
              (forall q, (0 <= q && q < k@pre) =>
                 (1 <= hot_costs[q] && hot_costs[q] <= cold_costs[q] &&
                  cold_costs[q] <= 1000000000)) &&
              1 <= i && i < n@pre &&
              x == prog[i] && y == prog[i - 1] &&
              1 <= x && x <= k@pre && 1 <= y && y <= k@pre &&
              ((x == y &&
                costA == Znth(x, cons(0, hot_costs), 0)) ||
               (x != y &&
                costA == Znth(x, cons(0, cold_costs), 0))) &&
              1 <= costA && costA <= 1000000000 &&
              Zlength(dp) == k@pre + 1 && dp[0] == 0 &&
              i <= off - costA &&
              off - costA <= i * 1000000000 &&
              i + 1 <= off && off <= (i + 1) * 1000000000 &&
              -i * 1000000000 <= mind && mind <= 0 &&
              i <= mind + (off - costA) &&
              mind + (off - costA) <= i * 1000000000 &&
              (forall q, (0 <= q && q <= k@pre) =>
                 (dp[q] == 4557430888798830399 ||
                  (-i * 1000000000 <= dp[q] &&
                   dp[q] <= i * 1000000000))) &&
              candB <= mind + (off - costA) +
                         Znth(x, cons(0, cold_costs), 0) &&
              (dp[x] < 4557430888798830399 =>
                 candB <= dp[x] + (off - costA) +
                            Znth(x, cons(0, hot_costs), 0)) &&
              (candB == mind + (off - costA) +
                            Znth(x, cons(0, cold_costs), 0) ||
               (dp[x] < 4557430888798830399 &&
                candB == dp[x] + (off - costA) +
                              Znth(x, cons(0, hot_costs), 0))) &&
              ny == candB - off &&
              -(i + 1) * 1000000000 <= ny &&
              ny + off <= (i + 1) * 1000000000 &&
              i + 1 <= ny + off &&
              NormalizedScheduleState(prog, cold_costs, hot_costs,
                                      i, dp, off - costA, mind) &&
              ((ny < dp[y] && ny < mind) =>
                 NormalizedScheduleState(
                   prog, cold_costs, hot_costs, i + 1,
                   replace_Znth(y, ny, dp), off, ny)) &&
              ((ny < dp[y] && ny >= mind) =>
                 NormalizedScheduleState(
                   prog, cold_costs, hot_costs, i + 1,
                   replace_Znth(y, ny, dp), off, mind)) &&
              (ny >= dp[y] =>
                 NormalizedScheduleState(
                   prog, cold_costs, hot_costs, i + 1,
                   dp, off, mind)) &&
              IntArray::full(a@pre, n@pre, prog) *
              Int64Array::full(cold@pre, k@pre + 1,
                               cons(0, cold_costs)) *
              Int64Array::full(hot@pre, k@pre + 1,
                               cons(0, hot_costs)) *
              Int64Array::full(d@pre, k@pre + 1, dp)
        */
        if (ny < d[y]) {
            d[y] = ny;
            if (ny < mind)
                mind = ny;
        }
    }
    return mind + off;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static int a[MAXK];
//     static long long cold[MAXK], hot[MAXK], d[MAXK];
//     while (t--) {
//         int n, k;
//         scanf("%d %d", &n, &k);
//         for (int i = 0; i < n; i++)
//             scanf("%d", &a[i]);
//         cold[0] = hot[0] = 0;
//         for (int j = 1; j <= k; j++)
//             scanf("%lld", &cold[j]);
//         for (int j = 1; j <= k; j++)
//             scanf("%lld", &hot[j]);
//         printf("%lld\n", solver(a, n, k, cold, hot, d));
//     }
//     return 0;
// }
