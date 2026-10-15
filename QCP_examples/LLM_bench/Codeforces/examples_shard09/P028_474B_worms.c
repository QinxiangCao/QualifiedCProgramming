/*
 * Codeforces 474/B - Worms  (rating 1200, BINARY SEARCH)
 *
 * Prefix sums give each pile's last label; a binary search over them maps a
 * queried label to its pile.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Pre : list Z -> list Z -> Prop)
      (Spec : list Z -> list Z -> list Z -> Prop)
      (PrefixSumsPrefix : list Z -> list Z -> Prop)
      (PrefixSums : list Z -> list Z -> Prop)
      (PileIndex : list Z -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P028_474B_worms_lib */

/* solver: pure.  Index (1-based) of the pile holding label q, given the
 * prefix sums pre[1..n] of the pile sizes. */
static int locate_pile(const long long *pre, int n, long long q)
/*@ With (pile_sizes : list Z) (prefix : list Z)
    Require
      1 <= n && n <= 100000 && n == Zlength(pile_sizes) &&
      Zlength(prefix) == n + 1 &&
      (forall k, (0 <= k && k < n) =>
         (1 <= pile_sizes[k] && pile_sizes[k] <= 1000)) &&
      1 <= q && q <= prefix[n] && PrefixSums(pile_sizes, prefix) &&
      Int64Array::full(pre, n + 1, prefix)
    Ensure
      PileIndex(pile_sizes, q, __return) &&
      Int64Array::full(pre, n + 1, prefix)
*/
{
    int lo = 1, hi = n;
    /*@ Inv Assert
          pre == pre@pre && n == n@pre && q == q@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          n@pre == Zlength(pile_sizes) &&
          Zlength(prefix) == n@pre + 1 &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= pile_sizes[k] && pile_sizes[k] <= 1000)) &&
          PrefixSums(pile_sizes, prefix) &&
          1 <= q@pre && q@pre <= prefix[n@pre] &&
          1 <= lo && lo <= hi && hi <= n@pre &&
          prefix[lo - 1] < q@pre && q@pre <= prefix[hi] &&
          Int64Array::full(pre@pre, n@pre + 1, prefix)
    */
    while (lo < hi) {
        int mid = lo + (hi - lo) / 2;
        /*@ lo <= mid && mid < hi by local */
        if (pre[mid] >= q)
            hi = mid;
        else
            lo = mid + 1;
    }
    return lo;
}

/* solver: complete case.  Build prefix sums and answer the whole query list. */
static void solver(const int *piles, int n, const long long *queries, int m,
                   int *out, long long *pre)
/* QCP_INSERT_BEGIN:shard09-P028-normalized-solver-contract */
/*@ With (pile_sizes : list Z) (worm_queries : list Z)
    Require
      1 <= n && n <= 100000 && 1 <= m && m <= 100000 && 
      (forall i, (0 <= i && i < n) => (1 <= pile_sizes[i] && pile_sizes[i] <= 1000)) && 
      (forall i, (0 <= i && i < m) => 1 <= worm_queries[i]) &&
      Pre(pile_sizes, worm_queries) && n == Zlength(pile_sizes) && m == Zlength(worm_queries) && IntArray::full(piles, n, pile_sizes) * Int64Array::full(queries, m, worm_queries) * IntArray::full_shape(out, m) * Int64Array::full_shape(pre, n + 1)
    Ensure
      exists (result : list Z), Spec(pile_sizes, worm_queries, result) && IntArray::full(piles, n, pile_sizes) * Int64Array::full(queries, m, worm_queries) * IntArray::full(out, m, result) * Int64Array::full_shape(pre, n + 1)
*/
/* QCP_INSERT_END:shard09-P028-normalized-solver-contract */
{
    /*@ Assert
          exists (old_pre0 : Z),
          piles == piles@pre && n == n@pre && queries == queries@pre &&
          m == m@pre && out == out@pre && pre == pre@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= m@pre && m@pre <= 100000 &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= pile_sizes[k] && pile_sizes[k] <= 1000)) &&
          (forall k, (0 <= k && k < m@pre) =>
             1 <= worm_queries[k]) &&
          Pre(pile_sizes, worm_queries) &&
          n@pre == Zlength(pile_sizes) && m@pre == Zlength(worm_queries) &&
          IntArray::full(piles@pre, n@pre, pile_sizes) *
          Int64Array::full(queries@pre, m@pre, worm_queries) *
          IntArray::full_shape(out@pre, m@pre) *
          data_at(pre@pre + 0 * sizeof(long long), long long, old_pre0) *
          Int64Array::missing_i_shape(pre@pre, 0, 0, n@pre + 1)
    */
    pre[0] = 0;
    /*@ Assert
          piles == piles@pre && n == n@pre && queries == queries@pre &&
          m == m@pre && out == out@pre && pre == pre@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= m@pre && m@pre <= 100000 &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= pile_sizes[k] && pile_sizes[k] <= 1000)) &&
          (forall k, (0 <= k && k < m@pre) =>
             1 <= worm_queries[k]) &&
          Pre(pile_sizes, worm_queries) &&
          n@pre == Zlength(pile_sizes) && m@pre == Zlength(worm_queries) &&
          PrefixSumsPrefix(pile_sizes, cons(0, nil)) &&
          IntArray::full(piles@pre, n@pre, pile_sizes) *
          Int64Array::full(queries@pre, m@pre, worm_queries) *
          IntArray::full_shape(out@pre, m@pre) *
          Int64Array::seg(pre@pre, 0, 1, cons(0, nil)) *
          Int64Array::seg_shape(pre@pre, 1, n@pre + 1)
    */
    /*@ Inv Assert
          exists (prefix : list Z),
          piles == piles@pre && n == n@pre && queries == queries@pre &&
          m == m@pre && out == out@pre && pre == pre@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= m@pre && m@pre <= 100000 &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= pile_sizes[k] && pile_sizes[k] <= 1000)) &&
          (forall k, (0 <= k && k < m@pre) =>
             1 <= worm_queries[k]) &&
          Pre(pile_sizes, worm_queries) &&
          n@pre == Zlength(pile_sizes) && m@pre == Zlength(worm_queries) &&
          0 <= i && i <= n@pre &&
          Zlength(prefix) == i + 1 && PrefixSumsPrefix(pile_sizes, prefix) &&
          IntArray::full(piles@pre, n@pre, pile_sizes) *
          Int64Array::full(queries@pre, m@pre, worm_queries) *
          IntArray::full_shape(out@pre, m@pre) *
          Int64Array::seg(pre@pre, 0, i + 1, prefix) *
          Int64Array::seg_shape(pre@pre, i + 1, n@pre + 1)
    */
    for (int i = 0; i < n; i++) {
        /*@ Assert
              exists (prefix : list Z) (old_next : Z),
              piles == piles@pre && n == n@pre && queries == queries@pre &&
              m == m@pre && out == out@pre && pre == pre@pre &&
              1 <= n@pre && n@pre <= 100000 &&
              1 <= m@pre && m@pre <= 100000 &&
              (forall k, (0 <= k && k < n@pre) =>
                 (1 <= pile_sizes[k] && pile_sizes[k] <= 1000)) &&
              (forall k, (0 <= k && k < m@pre) =>
                 1 <= worm_queries[k]) &&
              Pre(pile_sizes, worm_queries) &&
              n@pre == Zlength(pile_sizes) && m@pre == Zlength(worm_queries) &&
              0 <= i && i < n@pre &&
              Zlength(prefix) == i + 1 && PrefixSumsPrefix(pile_sizes, prefix) &&
              IntArray::full(piles@pre, n@pre, pile_sizes) *
              Int64Array::full(queries@pre, m@pre, worm_queries) *
              IntArray::full_shape(out@pre, m@pre) *
              Int64Array::seg(pre@pre, 0, i + 1, prefix) *
              data_at(pre@pre + (i + 1) * sizeof(long long), long long, old_next) *
              Int64Array::missing_i_shape(pre@pre, i + 1, i + 1, n@pre + 1)
        */
        pre[i + 1] = pre[i] + piles[i];
        /*@ Assert
              exists (prefix_next : list Z),
              piles == piles@pre && n == n@pre && queries == queries@pre &&
              m == m@pre && out == out@pre && pre == pre@pre &&
              1 <= n@pre && n@pre <= 100000 &&
              1 <= m@pre && m@pre <= 100000 &&
              (forall k, (0 <= k && k < n@pre) =>
                 (1 <= pile_sizes[k] && pile_sizes[k] <= 1000)) &&
              (forall k, (0 <= k && k < m@pre) =>
                 1 <= worm_queries[k]) &&
              Pre(pile_sizes, worm_queries) &&
              n@pre == Zlength(pile_sizes) && m@pre == Zlength(worm_queries) &&
              0 <= i && i < n@pre &&
              Zlength(prefix_next) == i + 2 &&
              PrefixSumsPrefix(pile_sizes, prefix_next) &&
              IntArray::full(piles@pre, n@pre, pile_sizes) *
              Int64Array::full(queries@pre, m@pre, worm_queries) *
              IntArray::full_shape(out@pre, m@pre) *
              Int64Array::seg(pre@pre, 0, i + 2, prefix_next) *
              Int64Array::seg_shape(pre@pre, i + 2, n@pre + 1)
        */
    }

    /*@ Assert
          exists (prefix : list Z),
          piles == piles@pre && n == n@pre && queries == queries@pre &&
          m == m@pre && out == out@pre && pre == pre@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= m@pre && m@pre <= 100000 &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= pile_sizes[k] && pile_sizes[k] <= 1000)) &&
          (forall k, (0 <= k && k < m@pre) =>
             1 <= worm_queries[k]) &&
          Pre(pile_sizes, worm_queries) &&
          n@pre == Zlength(pile_sizes) && m@pre == Zlength(worm_queries) &&
          PrefixSums(pile_sizes, prefix) &&
          IntArray::full(piles@pre, n@pre, pile_sizes) *
          Int64Array::full(queries@pre, m@pre, worm_queries) *
          IntArray::full_shape(out@pre, m@pre) *
          Int64Array::full(pre@pre, n@pre + 1, prefix)
    */
    /*@ Inv Assert
          exists (prefix : list Z) (result : list Z),
          piles == piles@pre && n == n@pre && queries == queries@pre &&
          m == m@pre && out == out@pre && pre == pre@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= m@pre && m@pre <= 100000 &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= pile_sizes[k] && pile_sizes[k] <= 1000)) &&
          (forall k, (0 <= k && k < m@pre) =>
             1 <= worm_queries[k]) &&
          Pre(pile_sizes, worm_queries) &&
          n@pre == Zlength(pile_sizes) && m@pre == Zlength(worm_queries) &&
          PrefixSums(pile_sizes, prefix) &&
          0 <= i && i <= m@pre && Zlength(result) == i &&
          (forall j, (0 <= j && j < i) =>
             PileIndex(pile_sizes, worm_queries[j], result[j])) &&
          IntArray::full(piles@pre, n@pre, pile_sizes) *
          Int64Array::full(queries@pre, m@pre, worm_queries) *
          IntArray::seg(out@pre, 0, i, result) *
          IntArray::seg_shape(out@pre, i, m@pre) *
          Int64Array::full(pre@pre, n@pre + 1, prefix)
    */
    for (int i = 0; i < m; i++) {
        /*@ Assert
              exists (prefix : list Z) (result : list Z) (old_out : Z),
              piles == piles@pre && n == n@pre && queries == queries@pre &&
              m == m@pre && out == out@pre && pre == pre@pre &&
              1 <= n@pre && n@pre <= 100000 &&
              1 <= m@pre && m@pre <= 100000 &&
              (forall k, (0 <= k && k < n@pre) =>
                 (1 <= pile_sizes[k] && pile_sizes[k] <= 1000)) &&
              (forall k, (0 <= k && k < m@pre) =>
                 1 <= worm_queries[k]) &&
              Pre(pile_sizes, worm_queries) &&
              n@pre == Zlength(pile_sizes) && m@pre == Zlength(worm_queries) &&
              PrefixSums(pile_sizes, prefix) &&
              0 <= i && i < m@pre && Zlength(result) == i &&
              (forall j, (0 <= j && j < i) =>
                 PileIndex(pile_sizes, worm_queries[j], result[j])) &&
              IntArray::full(piles@pre, n@pre, pile_sizes) *
              Int64Array::full(queries@pre, m@pre, worm_queries) *
              IntArray::seg(out@pre, 0, i, result) *
              data_at(out@pre + i * sizeof(int), int, old_out) *
              IntArray::missing_i_shape(out@pre, i, i, m@pre) *
              Int64Array::full(pre@pre, n@pre + 1, prefix)
        */
        out[i] = locate_pile(pre, n, queries[i])
          /*@ where pile_sizes = pile_sizes */;
        /*@ Assert
              exists (prefix : list Z) (result_next : list Z),
              piles == piles@pre && n == n@pre && queries == queries@pre &&
              m == m@pre && out == out@pre && pre == pre@pre &&
              1 <= n@pre && n@pre <= 100000 &&
              1 <= m@pre && m@pre <= 100000 &&
              (forall k, (0 <= k && k < n@pre) =>
                 (1 <= pile_sizes[k] && pile_sizes[k] <= 1000)) &&
              (forall k, (0 <= k && k < m@pre) =>
                 1 <= worm_queries[k]) &&
              Pre(pile_sizes, worm_queries) &&
              n@pre == Zlength(pile_sizes) && m@pre == Zlength(worm_queries) &&
              PrefixSums(pile_sizes, prefix) &&
              0 <= i && i < m@pre && Zlength(result_next) == i + 1 &&
              (forall j, (0 <= j && j < i + 1) =>
                 PileIndex(pile_sizes, worm_queries[j], result_next[j])) &&
              IntArray::full(piles@pre, n@pre, pile_sizes) *
              Int64Array::full(queries@pre, m@pre, worm_queries) *
              IntArray::seg(out@pre, 0, i + 1, result_next) *
              IntArray::seg_shape(out@pre, i + 1, m@pre) *
              Int64Array::full(pre@pre, n@pre + 1, prefix)
        */
    }
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static int piles[100005], out[100005];
//     static long long pre[100005], queries[100005];
//     for (int i = 0; i < n; i++)
//         scanf("%d", &piles[i]);
//     int m;
//     scanf("%d", &m);
//     for (int i = 0; i < m; i++)
//         scanf("%lld", &queries[i]);
//     solver(piles, n, queries, m, out, pre);
//     for (int i = 0; i < m; i++)
//         printf("%d\n", out[i]);
//     return 0;
// }
