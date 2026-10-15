/*
 * Codeforces 2000/D - Right Left Wrong  (rating 1200, GREEDY)
 *
 * All a_i are positive, so a segment is worth taking whenever it exists.
 * Pairing the outermost 'L' with the outermost 'R', then the next pair inside,
 * and so on, covers the largest possible total: nested pairs never conflict
 * and any crossing pairing covers no more cells.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : list Z -> list Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P026_2000D_right_left_wrong_lib */
/*@ Extern Coq
      (PrefixSumsPrefix : list Z -> list Z -> Prop)
      (PrefixSums : list Z -> list Z -> Prop)
      (GreedyProgress : list Z -> list Z -> Z -> Z -> Z -> Prop)
*/

/* solver: pure.  Maximum score for strip a[0..n-1] with letters s[0..n-1]. */
static long long solver(const int *a, const char *s, int n, long long *pre)
/* QCP_INSERT_BEGIN:shard09-P026-solver-contract */
/*@ With (values : list Z) (directions : list Z)
    Require
      2 <= n && n <= 200000 && 
      (forall i, (0 <= i && i < n) => (1 <= values[i] && values[i] <= 100000)) && 
      (forall i, (0 <= i && i < n) => (directions[i] == 76 || directions[i] == 82)) &&
      n == Zlength(values) && Zlength(directions) == n && IntArray::full(a, n, values) * CharArray::full(s, n, directions) * Int64Array::undef_full(pre, n + 1)
    Ensure
      Spec(values, directions, __return) &&
      IntArray::full(a, n, values) * CharArray::full(s, n, directions) * Int64Array::full_shape(pre, n + 1)
*/
/* QCP_INSERT_END:shard09-P026-solver-contract */
{
    pre[0] = 0;
    /*@ Inv Assert
          exists (prefix : list Z),
          a == a@pre && s == s@pre && n == n@pre && pre == pre@pre &&
          2 <= n@pre && n@pre <= 200000 &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= values[k] && values[k] <= 100000)) &&
          (forall k, (0 <= k && k < n@pre) =>
             (directions[k] == 76 || directions[k] == 82)) &&
          n@pre == Zlength(values) && Zlength(directions) == n@pre &&
          0 <= i && i <= n@pre &&
          Zlength(prefix) == i + 1 && PrefixSumsPrefix(values, prefix) &&
          IntArray::full(a@pre, n@pre, values) *
          CharArray::full(s@pre, n@pre, directions) *
          Int64Array::seg(pre@pre, 0, i + 1, prefix) *
          Int64Array::undef_seg(pre@pre, i + 1, n@pre + 1)
    */
    for (int i = 0; i < n; i++)
        pre[i + 1] = pre[i] + a[i];

    /*@ Assert
          exists (prefix : list Z),
          a == a@pre && s == s@pre && n == n@pre && pre == pre@pre &&
          2 <= n@pre && n@pre <= 200000 &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= values[k] && values[k] <= 100000)) &&
          (forall k, (0 <= k && k < n@pre) =>
             (directions[k] == 76 || directions[k] == 82)) &&
          n@pre == Zlength(values) && Zlength(directions) == n@pre &&
          PrefixSums(values, prefix) &&
          IntArray::full(a@pre, n@pre, values) *
          CharArray::full(s@pre, n@pre, directions) *
          Int64Array::full(pre@pre, n@pre + 1, prefix)
    */
    long long score = 0;
    int l = 0, r = n - 1;
    /*@ Inv Assert
          exists (prefix : list Z),
          a == a@pre && s == s@pre && n == n@pre && pre == pre@pre &&
          2 <= n@pre && n@pre <= 200000 &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= values[k] && values[k] <= 100000)) &&
          (forall k, (0 <= k && k < n@pre) =>
             (directions[k] == 76 || directions[k] == 82)) &&
          n@pre == Zlength(values) && Zlength(directions) == n@pre &&
          PrefixSums(values, prefix) &&
          0 <= l && l < n@pre && 0 <= r && r < n@pre && l <= r + 1 &&
          0 <= score && score <= 2000000000000000 &&
          GreedyProgress(values, directions, l, r, score) &&
          IntArray::full(a@pre, n@pre, values) *
          CharArray::full(s@pre, n@pre, directions) *
          Int64Array::full(pre@pre, n@pre + 1, prefix)
    */
    while (l < r) {
        /*@ Inv Assert
              exists (prefix : list Z),
              a == a@pre && s == s@pre && n == n@pre && pre == pre@pre &&
              2 <= n@pre && n@pre <= 200000 &&
              (forall k, (0 <= k && k < n@pre) =>
                 (1 <= values[k] && values[k] <= 100000)) &&
              (forall k, (0 <= k && k < n@pre) =>
                 (directions[k] == 76 || directions[k] == 82)) &&
              n@pre == Zlength(values) && Zlength(directions) == n@pre &&
              PrefixSums(values, prefix) &&
              0 <= l && l < n@pre && 0 <= r && r < n@pre && l <= r &&
              0 <= score && score <= 2000000000000000 &&
              GreedyProgress(values, directions, l, r, score) &&
              IntArray::full(a@pre, n@pre, values) *
              CharArray::full(s@pre, n@pre, directions) *
              Int64Array::full(pre@pre, n@pre + 1, prefix)
        */
        while (l < r && s[l] != 'L')
            l++;
        /*@ Inv Assert
              exists (prefix : list Z),
              a == a@pre && s == s@pre && n == n@pre && pre == pre@pre &&
              2 <= n@pre && n@pre <= 200000 &&
              (forall k, (0 <= k && k < n@pre) =>
                 (1 <= values[k] && values[k] <= 100000)) &&
              (forall k, (0 <= k && k < n@pre) =>
                 (directions[k] == 76 || directions[k] == 82)) &&
              n@pre == Zlength(values) && Zlength(directions) == n@pre &&
              PrefixSums(values, prefix) &&
              0 <= l && l < n@pre && 0 <= r && r < n@pre && l <= r &&
              (l < r => directions[l] == 76) &&
              0 <= score && score <= 2000000000000000 &&
              GreedyProgress(values, directions, l, r, score) &&
              IntArray::full(a@pre, n@pre, values) *
              CharArray::full(s@pre, n@pre, directions) *
              Int64Array::full(pre@pre, n@pre + 1, prefix)
        */
        while (l < r && s[r] != 'R')
            r--;
        if (l < r) {
            score += pre[r + 1] - pre[l];
            l++;
            r--;
        }
    }
    return score;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static int a[200005];
//     static char s[200005];
//     static long long pre[200006];
//     while (t--) {
//         int n;
//         scanf("%d", &n);
//         for (int i = 0; i < n; i++)
//             scanf("%d", &a[i]);
//         scanf("%200004s", s);
//         printf("%lld\n", solver(a, s, n, pre));
//     }
//     return 0;
// }
