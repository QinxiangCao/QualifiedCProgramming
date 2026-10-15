/*
 * Codeforces 1201/C - Maximum Median  (rating 1400, BINARY SEARCH)
 *
 * Reaching median m costs sum over the sorted upper half of max(0, m - a_i),
 * which grows with m, so binary search the largest affordable m.  Only the
 * upper half matters: raising smaller elements never helps the median.
 */

// #include <stdio.h>
// #include <stdlib.h>

/* QCP_INSERT_BEGIN:shard09-P036-solver-support */
/*@ Import Coq Require Import AUXLib.MonotonicList */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P036_1201C_maximum_median_lib */
/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
      (Pre : Z -> list Z -> Prop)
      (Spec : Z -> list Z -> Z -> Prop)
      (MedianRaiseCost : list Z -> Z -> Z)
      (MedianCostPrefix : list Z -> Z -> Z -> Z -> Prop)
      (MedianSearchBounds : list Z -> Z -> Z -> Z -> Prop)
      (mono_nondec : list Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P036-solver-support */

void quicksort(int *arr, int n)
/*@ With (l : list Z)
    Require
      0 <= n && n <= 200000 &&
      IntArray::full(arr, n, l)
    Ensure
      exists l1,
        Permutation(l, l1) &&
        mono_nondec(l1) &&
        IntArray::full(arr, n, l1)
*/
;

// static int cmp_int(const void *a, const void *b)
// {
//     int x = *(const int *)a, y = *(const int *)b;
//     return (x > y) - (x < y);
// }

/* cost: operations needed to push the median of the sorted a[] up to m. */
static long long cost(const int *a, int n, long long m)
/*@ With (sorted : list Z)
    Require
      1 <= n && n <= 200000 &&
      0 <= m && m <= 2000000000 &&
      Zlength(sorted) == n &&
      mono_nondec(sorted) &&
      (forall i, (0 <= i && i < n) =>
        (1 <= sorted[i] && sorted[i] <= 1000000000)) &&
      IntArray::full(a, n, sorted)
    Ensure
      __return == MedianRaiseCost(sorted, m) &&
      IntArray::full(a, n, sorted)
*/
{
    long long need = 0;
    /*@ Inv Assert
          a == a@pre && n == n@pre && m == m@pre &&
          1 <= n@pre && n@pre <= 200000 &&
          0 <= m@pre && m@pre <= 2000000000 &&
          Zlength(sorted) == n@pre &&
          mono_nondec(sorted) &&
          (forall j, (0 <= j && j < n@pre) =>
            (1 <= sorted[j] && sorted[j] <= 1000000000)) &&
          0 <= i && n@pre / 2 <= i && i <= n@pre &&
          0 <= need &&
          need <= (i - n@pre / 2) * 2000000000 &&
          MedianCostPrefix(sorted, m@pre, i, need) &&
          IntArray::full(a, n@pre, sorted)
    */
    for (int i = n / 2; i < n; i++) {
        if (a[i] >= m)
            break;                        /* sorted: the rest are >= m too */
        need += m - a[i];
    }
    /*@ Assert
          a == a@pre && n == n@pre && m == m@pre &&
          1 <= n@pre && n@pre <= 200000 &&
          0 <= m@pre && m@pre <= 2000000000 &&
          Zlength(sorted) == n@pre &&
          mono_nondec(sorted) &&
          (forall j, (0 <= j && j < n@pre) =>
            (1 <= sorted[j] && sorted[j] <= 1000000000)) &&
          need == MedianRaiseCost(sorted, m@pre) &&
          IntArray::full(a, n@pre, sorted)
    */
    return need;
}

/* solver: largest achievable median within k operations.  Sorts a[]. */
static long long solver(int *a, int n, long long k)
/* QCP_INSERT_BEGIN:shard09-P036-solver-contract */
/*@ With (values : list Z)
    Require
      1 <= k && k <= 1000000000 &&
      Pre(k, values) && 1 <= n && n <= 200000 && (forall i, (0 <= i && i < n) => (1 <= values[i] && values[i] <= 1000000000)) &&
      n == Zlength(values) && IntArray::full(a, n, values)
    Ensure
      Spec(k, values, __return) &&
      exists (a_after : list Z), Permutation(values, a_after) && IntArray::full(a, n, a_after)
*/
/* QCP_INSERT_END:shard09-P036-solver-contract */
{
    // qsort(a, n, sizeof *a, cmp_int);
    quicksort(a, n) /*@ where l = values */;
    /*@ Assert
          exists sorted,
            a == a@pre && n == n@pre && k == k@pre &&
            1 <= k@pre && k@pre <= 1000000000 &&
            Pre(k@pre, values) &&
            1 <= n@pre && n@pre <= 200000 &&
            n@pre == Zlength(values) &&
            Zlength(sorted) == n@pre &&
            (forall j, (0 <= j && j < n@pre) =>
              (1 <= sorted[j] && sorted[j] <= 1000000000)) &&
            Permutation(values, sorted) && mono_nondec(sorted) &&
            0 <= n@pre / 2 && n@pre / 2 < n@pre &&
            IntArray::full(a, n@pre, sorted)
    */
    long long lo = a[n / 2], hi = 2000000000LL;
    /*@ Inv Assert
          exists sorted,
            a == a@pre && n == n@pre && k == k@pre &&
            1 <= k@pre && k@pre <= 1000000000 &&
            Pre(k@pre, values) &&
            1 <= n@pre && n@pre <= 200000 &&
            n@pre == Zlength(values) &&
            Zlength(sorted) == n@pre &&
            (forall j, (0 <= j && j < n@pre) =>
              (1 <= sorted[j] && sorted[j] <= 1000000000)) &&
            Permutation(values, sorted) && mono_nondec(sorted) &&
            1 <= lo && lo <= hi && hi <= 2000000000 &&
            MedianSearchBounds(values, k@pre, lo, hi) &&
            IntArray::full(a, n@pre, sorted)
    */
    while (lo < hi) {
        long long mid = lo + (hi - lo + 1) / 2;
        if (cost(a, n, mid) <= k)
            lo = mid;
        else
            hi = mid - 1;
    }
    return lo;
}

// int main(void)
// {
//     int n;
//     long long k;
//     if (scanf("%d %lld", &n, &k) != 2)
//         return 0;
//     static int a[200005];
//     for (int i = 0; i < n; i++)
//         scanf("%d", &a[i]);
//     printf("%lld\n", solver(a, n, k));
//     return 0;
// }
