/*
 * Codeforces 1561/C - Deep Down Below  (rating 1300, GREEDY)
 *
 * Cave i can only be entered with power at least req_i = max_j (a_ij + 1 - j)
 * (j counted from 0, since j monsters were already beaten inside), and leaving
 * it adds k_i power.  Clearing caves in increasing order of req is optimal, so
 * the answer is max_i (req_i - power already gained before cave i).
 */

// #include <stdio.h>
/*@ Extern Coq
      (Pre : list (list Z) -> Prop)
      (Spec : list (list Z) -> Z -> Prop)
      (concat : list (list Z) -> list Z)
      (CaveSummaryBridge : list (list Z) -> list Z -> list Z -> Prop)
      (increasing : list Z -> Prop)
      (sum : list Z -> Z)
      (ParallelPermutation : list Z -> list Z -> list Z -> list Z -> Prop)
      (HeapParentsFrom : list Z -> Z -> Z -> Prop)
      (HeapOrderedExceptAtFrom : list Z -> Z -> Z -> Z -> Prop)
      (SelectedLargerChild : list Z -> Z -> Z -> Z -> Prop)
      (HeapSortState : list Z -> list Z -> list Z -> list Z -> Z -> Prop)
      (GreedyNeed : list Z -> list Z -> Z -> Z -> Prop)
      (SortedCaveSummaries : list (list Z) -> list Z -> list Z -> list Z -> list Z -> Prop)
      (CaveInputBounds : list (list Z) -> Prop)
      (CaveSummaryBounds : list Z -> list Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P032_1561C_deep_down_below_lib */


/* Sort the two parallel arrays by requirement. */
static void sift_caves(long long *req, long long *gain, int root, int hi)
/*@ With (requirements gains : list Z) (n : Z)
    Require
      1 <= n && n <= 100000 &&
      Zlength(requirements) == n && Zlength(gains) == n &&
      0 <= root && root <= hi && hi < n &&
      HeapOrderedExceptAtFrom(requirements, root, hi, root) &&
      Int64Array::full(req, n, requirements) *
      Int64Array::full(gain, n, gains)
    Ensure
      exists (requirements_after : list Z) (gains_after : list Z),
        Zlength(requirements_after) == n &&
        Zlength(gains_after) == n &&
        ParallelPermutation(requirements, gains,
                            requirements_after, gains_after) &&
        HeapParentsFrom(requirements_after, root, hi) &&
        sublist(hi + 1, n, requirements_after) ==
          sublist(hi + 1, n, requirements) &&
        sublist(hi + 1, n, gains_after) ==
          sublist(hi + 1, n, gains) &&
        Int64Array::full(req, n, requirements_after) *
        Int64Array::full(gain, n, gains_after)
 */
{
    /*@ Inv Assert
        exists (requirements_now : list Z) (gains_now : list Z),
          req == req@pre && gain == gain@pre && hi == hi@pre &&
          1 <= n && n <= 100000 &&
          Zlength(requirements_now) == n && Zlength(gains_now) == n &&
          0 <= root@pre && root@pre <= root && root <= hi && hi < n &&
          0 <= 2 * root + 1 && 2 * root + 1 <= INT_MAX &&
          ParallelPermutation(requirements, gains,
                              requirements_now, gains_now) &&
          HeapOrderedExceptAtFrom(requirements_now,
                                  root@pre, hi, root) &&
          (root == root@pre ||
           ((2 * root + 1 <= hi =>
               requirements_now[2 * root + 1] <=
                 requirements_now[(root - 1) / 2]) &&
            (2 * root + 2 <= hi =>
               requirements_now[2 * root + 2] <=
                 requirements_now[(root - 1) / 2]))) &&
          sublist(hi + 1, n, requirements_now) ==
            sublist(hi + 1, n, requirements) &&
          sublist(hi + 1, n, gains_now) == sublist(hi + 1, n, gains) &&
          Int64Array::full(req, n, requirements_now) *
          Int64Array::full(gain, n, gains_now)
     */
    while (2 * root + 1 <= hi) {
        int child = 2 * root + 1;
        if (child + 1 <= hi && req[child] < req[child + 1])
            child++;
        /*@ Assert
            exists (requirements_now : list Z) (gains_now : list Z),
              req == req@pre && gain == gain@pre && hi == hi@pre &&
              1 <= n && n <= 100000 &&
              Zlength(requirements_now) == n && Zlength(gains_now) == n &&
              0 <= root@pre && root@pre <= root && root <= hi && hi < n &&
              0 <= child && child <= hi &&
              SelectedLargerChild(requirements_now, root, hi, child) &&
              (root == root@pre ||
               requirements_now[child] <=
                 requirements_now[(root - 1) / 2]) &&
              ParallelPermutation(requirements, gains,
                                  requirements_now, gains_now) &&
              HeapOrderedExceptAtFrom(requirements_now,
                                      root@pre, hi, root) &&
              sublist(hi + 1, n, requirements_now) ==
                sublist(hi + 1, n, requirements) &&
              sublist(hi + 1, n, gains_now) == sublist(hi + 1, n, gains) &&
              Int64Array::full(req, n, requirements_now) *
              Int64Array::full(gain, n, gains_now)
         */
        if (req[root] >= req[child])
            return;
        long long t = req[root]; req[root] = req[child]; req[child] = t;
        t = gain[root]; gain[root] = gain[child]; gain[child] = t;
        /*@ Assert
            exists (requirements_now : list Z) (gains_now : list Z),
              req == req@pre && gain == gain@pre && hi == hi@pre &&
              1 <= n && n <= 100000 &&
              Zlength(requirements_now) == n && Zlength(gains_now) == n &&
              0 <= root@pre && root@pre <= root && root < child &&
              child <= hi && hi < n &&
              ParallelPermutation(requirements, gains,
                                  requirements_now, gains_now) &&
              HeapOrderedExceptAtFrom(requirements_now,
                                      root@pre, hi, child) &&
              (child == root@pre ||
               ((2 * child + 1 <= hi =>
                   requirements_now[2 * child + 1] <=
                     requirements_now[(child - 1) / 2]) &&
                (2 * child + 2 <= hi =>
                   requirements_now[2 * child + 2] <=
                     requirements_now[(child - 1) / 2]))) &&
              sublist(hi + 1, n, requirements_now) ==
                sublist(hi + 1, n, requirements) &&
              sublist(hi + 1, n, gains_now) == sublist(hi + 1, n, gains) &&
              Int64Array::full(req, n, requirements_now) *
              Int64Array::full(gain, n, gains_now) *
              has_permission(&t)
         */
        root = child;
    }
}

static void sort_caves(long long *req, long long *gain, int n)
/*@ With (requirements gains : list Z)
    Require
      1 <= n && n <= 100000 &&
      Zlength(requirements) == n && Zlength(gains) == n &&
      Int64Array::full(req, n, requirements) *
      Int64Array::full(gain, n, gains)
    Ensure
      exists (requirements_after : list Z) (gains_after : list Z),
        Zlength(requirements_after) == n &&
        Zlength(gains_after) == n &&
        ParallelPermutation(requirements, gains,
                            requirements_after, gains_after) &&
        increasing(requirements_after) &&
        Int64Array::full(req, n, requirements_after) *
        Int64Array::full(gain, n, gains_after)
 */
{
    /*@ Inv Assert
        exists (requirements_now : list Z) (gains_now : list Z),
          req == req@pre && gain == gain@pre && n == n@pre &&
          1 <= n && n <= 100000 &&
          Zlength(requirements) == n &&
          Zlength(gains) == n &&
          Zlength(requirements_now) == n &&
          Zlength(gains_now) == n &&
          -1 <= root && root <= n / 2 - 1 &&
          ParallelPermutation(requirements, gains,
                              requirements_now, gains_now) &&
          HeapParentsFrom(requirements_now, root + 1, n - 1) &&
          Int64Array::full(req, n, requirements_now) *
          Int64Array::full(gain, n, gains_now)
     */
    for (int root = n / 2 - 1; root >= 0; root--) {
        /*@ Assert
            exists (requirements_now : list Z) (gains_now : list Z),
              req == req@pre && gain == gain@pre && n == n@pre &&
              1 <= n && n <= 100000 &&
              Zlength(requirements) == n &&
              Zlength(gains) == n &&
              Zlength(requirements_now) == n &&
              Zlength(gains_now) == n &&
              0 <= root && root <= n / 2 - 1 &&
              ParallelPermutation(requirements, gains,
                                  requirements_now, gains_now) &&
              HeapOrderedExceptAtFrom(requirements_now,
                                      root, n - 1, root) &&
              Int64Array::full(req, n, requirements_now) *
              Int64Array::full(gain, n, gains_now)
         */
        sift_caves(req, gain, root, n - 1) /*@ where n = n */;
    }
    /*@ Inv Assert
        exists (requirements_now : list Z) (gains_now : list Z),
          req == req@pre && gain == gain@pre && n == n@pre &&
          1 <= n && n <= 100000 &&
          Zlength(requirements) == n &&
          Zlength(gains) == n &&
          Zlength(requirements_now) == n &&
          Zlength(gains_now) == n &&
          0 <= hi && hi <= n - 1 &&
          HeapSortState(requirements, gains,
                        requirements_now, gains_now, hi) &&
          Int64Array::full(req, n, requirements_now) *
          Int64Array::full(gain, n, gains_now)
     */
    for (int hi = n - 1; hi > 0; hi--) {
        long long t = req[0]; req[0] = req[hi]; req[hi] = t;
        t = gain[0]; gain[0] = gain[hi]; gain[hi] = t;
        /*@ Assert
            exists (requirements_now : list Z) (gains_now : list Z),
              req == req@pre && gain == gain@pre && n == n@pre &&
              1 <= n && n <= 100000 &&
              Zlength(requirements) == n &&
              Zlength(gains) == n &&
              Zlength(requirements_now) == n &&
              Zlength(gains_now) == n &&
              1 <= hi && hi <= n - 1 &&
              ParallelPermutation(requirements, gains,
                                  requirements_now, gains_now) &&
              HeapOrderedExceptAtFrom(requirements_now, 0, hi - 1, 0) &&
              increasing(sublist(hi, n, requirements_now)) &&
              (forall p q,
                 (0 <= p && p < hi && hi <= q && q < n) =>
                 requirements_now[p] <= requirements_now[q]) &&
              Int64Array::full(req, n, requirements_now) *
              Int64Array::full(gain, n, gains_now) *
              has_permission(&t)
         */
        sift_caves(req, gain, 0, hi - 1) /*@ where n = n */;
    }
}

/* solver: minimum starting power.  Sorts req[]/gain[] together. */
static long long solver(long long *req, long long *gain, int n)
/* QCP_INSERT_BEGIN:shard09-P032-normalized-solver-contract */
/*@ With (caves : list(list Z))
          (requirements : list Z) (gains : list Z)
    Require
      1 <= n && n <= 100000 && (forall i, (0 <= i && i < n) => (0 < Zlength(caves[i]) && Zlength(caves[i]) <= 100000)) && Zlength(concat(caves)) <= 100000 && (forall k, (0 <= k && k < Zlength(concat(caves))) => (1 <= concat(caves)[k] && concat(caves)[k] <= 1000000000)) &&
      n == Zlength(caves) &&
      Zlength(requirements) == n && Zlength(gains) == n &&
      CaveSummaryBridge(caves, requirements, gains) &&
      Int64Array::full(req, n, requirements) *
      Int64Array::full(gain, n, gains)
    Ensure
      Spec(caves, __return) &&
      exists (req_after : list Z) (gain_after : list Z),
        Zlength(req_after) == n && Zlength(gain_after) == n &&
        Int64Array::full(req, n, req_after) *
        Int64Array::full(gain, n, gain_after)
*/
/* QCP_INSERT_END:shard09-P032-normalized-solver-contract */
{
    sort_caves(req, gain, n);
    long long need = 0, gained = 0;
    /*@ Inv Assert
        exists (requirements_sorted : list Z) (gains_sorted : list Z),
          req == req@pre && gain == gain@pre && n == n@pre &&
          1 <= n && n <= 100000 && n == Zlength(caves) &&
          Zlength(requirements_sorted) == n &&
          Zlength(gains_sorted) == n &&
          0 <= i && i <= n &&
          0 <= gained && gained <= 100000 &&
          0 <= need && need <= 1000000001 &&
          gained == sum(sublist(0, i, gains_sorted)) &&
          CaveInputBounds(caves) &&
          SortedCaveSummaries(caves, requirements, gains,
                              requirements_sorted, gains_sorted) &&
          CaveSummaryBounds(requirements_sorted, gains_sorted) &&
          GreedyNeed(requirements_sorted, gains_sorted, i, need) &&
          Int64Array::full(req, n, requirements_sorted) *
          Int64Array::full(gain, n, gains_sorted)
     */
    for (int i = 0; i < n; i++) {
        long long start = req[i] - gained;
        if (start > need)
            need = start;
        gained += gain[i];
    }
    /*@ Assert
        req == req@pre && gain == gain@pre && n == n@pre &&
        Spec(caves, need) &&
        exists (requirements_after : list Z) (gains_after : list Z),
          Zlength(requirements_after) == n &&
          Zlength(gains_after) == n &&
          Int64Array::full(req, n, requirements_after) *
          Int64Array::full(gain, n, gains_after) *
          has_permission(&gained)
     */
    return need;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static long long reqs[100005], gains[100005];
//     while (t--) {
//         int n;
//         scanf("%d", &n);
//         for (int i = 0; i < n; i++) {
//             int k;
//             scanf("%d", &k);
//             long long req = 0;
//             for (int j = 0; j < k; j++) {
//                 long long a;
//                 scanf("%lld", &a);
//                 long long r = a + 1 - j;
//                 if (r > req)
//                     req = r;
//             }
//             reqs[i] = req;
//             gains[i] = k;
//         }
//         printf("%lld\n", solver(reqs, gains, n));
//     }
//     return 0;
// }
