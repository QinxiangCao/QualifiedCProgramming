/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P075_1474D_cleaning_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P075_1474D_cleaning_lib
*/

/*
 * Codeforces 1474/D - Cleaning  (rating 2200, PREFIX SUMS)
 *
 * Sweeping left to right, the stones pile i must hand to the right are forced:
 * pre[i] = a_i - pre[i-1], and the array clears iff every pre[i] >= 0 and
 * pre[n] == 0.  Build the mirrored suffix values too; a swap at (i, i+1) then
 * only needs the two middle values recomputed against pre[i-1] and suf[i+2].
 */

// #include <stdio.h>

/* solver: 1 if all stones can be removed using at most one adjacent swap. */
/* QCP_INSERT_BEGIN:shard09-P075-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P075_1474D_cleaning_lib */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P075-solver-support */
/*@ Extern Coq
      (PrefixResidualState : list Z -> list Z -> list Z -> Prop)
      (SuffixResidualState : list Z -> Z -> list Z -> list Z -> Prop)
      (CheckedSwapPrefix : list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
*/
static int solver(const long long *a, int n, long long *pre, long long *suf,
                  char *okpre, char *oksuf)
/* QCP_INSERT_BEGIN:shard09-P075-solver-contract */
/*@ With (values : list Z)
    Require
      2 <= n && n <= 200000 && (forall i, (0 <= i && i < n) => (1 <= values[i] && values[i] <= 1000000000)) &&
      n == Zlength(values) &&
      Int64Array::full(a, n + 1, cons(0, values)) * Int64Array::full_shape(pre, n + 1) * Int64Array::full_shape(suf, n + 2) * CharArray::full_shape(okpre, n + 1) * CharArray::full_shape(oksuf, n + 2)
    Ensure
      Spec(values, __return) &&
        Int64Array::full(a, n + 1, cons(0, values)) * Int64Array::full_shape(pre, n + 1) * Int64Array::full_shape(suf, n + 2) * CharArray::full_shape(okpre, n + 1) * CharArray::full_shape(oksuf, n + 2)
*/
/* QCP_INSERT_END:shard09-P075-solver-contract */
{
    /*@ Assert
          exists (old_pre0 : Z) (old_okpre0 : Z),
          a == a@pre && n == n@pre && pre == pre@pre && suf == suf@pre &&
          okpre == okpre@pre && oksuf == oksuf@pre &&
          2 <= n@pre && n@pre <= 200000 && n@pre == Zlength(values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= values[k] && values[k] <= 1000000000)) &&
          Int64Array::full(a@pre, n@pre + 1, cons(0, values)) *
          data_at(pre@pre + 0 * sizeof(long long), long long, old_pre0) *
          Int64Array::missing_i_shape(pre@pre, 0, 0, n@pre + 1) *
          Int64Array::full_shape(suf@pre, n@pre + 2) *
          data_at(okpre@pre + 0 * sizeof(char), char, old_okpre0) *
          CharArray::missing_i_shape(okpre@pre, 0, 0, n@pre + 1) *
          CharArray::full_shape(oksuf@pre, n@pre + 2)
    */
    pre[0] = 0;
    okpre[0] = 1;
    /*@ Inv Assert
          exists (pre_values : list Z) (okpre_values : list Z),
          a == a@pre && n == n@pre && pre == pre@pre && suf == suf@pre &&
          okpre == okpre@pre && oksuf == oksuf@pre &&
          2 <= n@pre && n@pre <= 200000 && n@pre == Zlength(values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= values[k] && values[k] <= 1000000000)) &&
          1 <= i && i <= n@pre + 1 &&
          Zlength(pre_values) == i && Zlength(okpre_values) == i &&
          PrefixResidualState(values, pre_values, okpre_values) &&
          (forall k, (0 <= k && k < i) =>
             (-1000000000 * k <= pre_values[k] &&
              pre_values[k] <= 1000000000 * k)) &&
          Int64Array::full(a@pre, n@pre + 1, cons(0, values)) *
          Int64Array::seg(pre@pre, 0, i, pre_values) *
          Int64Array::seg_shape(pre@pre, i, n@pre + 1) *
          Int64Array::full_shape(suf@pre, n@pre + 2) *
          CharArray::seg(okpre@pre, 0, i, okpre_values) *
          CharArray::seg_shape(okpre@pre, i, n@pre + 1) *
          CharArray::full_shape(oksuf@pre, n@pre + 2)
    */
    for (int i = 1; i <= n; i++) {
        /*@ Assert
              exists (pre_values : list Z) (okpre_values : list Z)
                     (old_pre_i : Z) (old_okpre_i : Z),
              a == a@pre && n == n@pre && pre == pre@pre && suf == suf@pre &&
              okpre == okpre@pre && oksuf == oksuf@pre &&
              2 <= n@pre && n@pre <= 200000 && n@pre == Zlength(values) &&
              (forall k, (0 <= k && k < n@pre) =>
                 (1 <= values[k] && values[k] <= 1000000000)) &&
              1 <= i && i <= n@pre &&
              Zlength(pre_values) == i && Zlength(okpre_values) == i &&
              PrefixResidualState(values, pre_values, okpre_values) &&
              (forall k, (0 <= k && k < i) =>
                 (-1000000000 * k <= pre_values[k] &&
                  pre_values[k] <= 1000000000 * k)) &&
              Int64Array::full(a@pre, n@pre + 1, cons(0, values)) *
              Int64Array::seg(pre@pre, 0, i, pre_values) *
              data_at(pre@pre + i * sizeof(long long), long long, old_pre_i) *
              Int64Array::missing_i_shape(pre@pre, i, i, n@pre + 1) *
              Int64Array::full_shape(suf@pre, n@pre + 2) *
              CharArray::seg(okpre@pre, 0, i, okpre_values) *
              data_at(okpre@pre + i * sizeof(char), char, old_okpre_i) *
              CharArray::missing_i_shape(okpre@pre, i, i, n@pre + 1) *
              CharArray::full_shape(oksuf@pre, n@pre + 2)
        */
        pre[i] = a[i] - pre[i - 1];
        okpre[i] = okpre[i - 1] && pre[i] >= 0;
    }
    /*@ Assert
          exists (pre_values : list Z) (okpre_values : list Z)
                 (old_suf_terminal : Z) (old_oksuf_terminal : Z),
          a == a@pre && n == n@pre && pre == pre@pre && suf == suf@pre &&
          okpre == okpre@pre && oksuf == oksuf@pre &&
          2 <= n@pre && n@pre <= 200000 && n@pre == Zlength(values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= values[k] && values[k] <= 1000000000)) &&
          Zlength(pre_values) == n@pre + 1 &&
          Zlength(okpre_values) == n@pre + 1 &&
          PrefixResidualState(values, pre_values, okpre_values) &&
          (forall k, (0 <= k && k <= n@pre) =>
             (-1000000000 * k <= pre_values[k] &&
              pre_values[k] <= 1000000000 * k)) &&
          Int64Array::full(a@pre, n@pre + 1, cons(0, values)) *
          Int64Array::full(pre@pre, n@pre + 1, pre_values) *
          data_at(suf@pre + (n@pre + 1) * sizeof(long long),
                  long long, old_suf_terminal) *
          Int64Array::missing_i_shape(suf@pre, n@pre + 1, 0, n@pre + 2) *
          CharArray::full(okpre@pre, n@pre + 1, okpre_values) *
          data_at(oksuf@pre + (n@pre + 1) * sizeof(char),
                  char, old_oksuf_terminal) *
          CharArray::missing_i_shape(oksuf@pre, n@pre + 1, 0, n@pre + 2)
    */
    suf[n + 1] = 0;
    oksuf[n + 1] = 1;
    /*@ Inv Assert
          exists (pre_values : list Z) (okpre_values : list Z)
                 (suf_values : list Z) (oksuf_values : list Z),
          a == a@pre && n == n@pre && pre == pre@pre && suf == suf@pre &&
          okpre == okpre@pre && oksuf == oksuf@pre &&
          2 <= n@pre && n@pre <= 200000 && n@pre == Zlength(values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= values[k] && values[k] <= 1000000000)) &&
          0 <= i && i <= n@pre &&
          Zlength(pre_values) == n@pre + 1 &&
          Zlength(okpre_values) == n@pre + 1 &&
          Zlength(suf_values) == n@pre + 1 - i &&
          Zlength(oksuf_values) == n@pre + 1 - i &&
          PrefixResidualState(values, pre_values, okpre_values) &&
          SuffixResidualState(values, i + 1, suf_values, oksuf_values) &&
          (forall k, (0 <= k && k <= n@pre) =>
             (-1000000000 * k <= pre_values[k] &&
              pre_values[k] <= 1000000000 * k)) &&
          (forall q, (0 <= q && q < Zlength(suf_values)) =>
             (-1000000000 * (n@pre - i - q) <= suf_values[q] &&
              suf_values[q] <= 1000000000 * (n@pre - i - q))) &&
          Int64Array::full(a@pre, n@pre + 1, cons(0, values)) *
          Int64Array::full(pre@pre, n@pre + 1, pre_values) *
          Int64Array::seg_shape(suf@pre, 0, i + 1) *
          Int64Array::seg(suf@pre, i + 1, n@pre + 2, suf_values) *
          CharArray::full(okpre@pre, n@pre + 1, okpre_values) *
          CharArray::seg_shape(oksuf@pre, 0, i + 1) *
          CharArray::seg(oksuf@pre, i + 1, n@pre + 2, oksuf_values)
    */
    for (int i = n; i >= 1; i--) {
        /*@ Assert
              exists (pre_values : list Z) (okpre_values : list Z)
                     (suf_values : list Z) (oksuf_values : list Z)
                     (suf_prefix : list Z) (oksuf_prefix : list Z),
              a == a@pre && n == n@pre && pre == pre@pre && suf == suf@pre &&
              okpre == okpre@pre && oksuf == oksuf@pre &&
              2 <= n@pre && n@pre <= 200000 && n@pre == Zlength(values) &&
              (forall k, (0 <= k && k < n@pre) =>
                 (1 <= values[k] && values[k] <= 1000000000)) &&
              1 <= i && i <= n@pre &&
              Zlength(pre_values) == n@pre + 1 &&
              Zlength(okpre_values) == n@pre + 1 &&
              Zlength(suf_values) == n@pre + 1 - i &&
              Zlength(oksuf_values) == n@pre + 1 - i &&
              Zlength(suf_prefix) == i + 1 &&
              Zlength(oksuf_prefix) == i + 1 &&
              PrefixResidualState(values, pre_values, okpre_values) &&
              SuffixResidualState(values, i + 1, suf_values, oksuf_values) &&
              (forall k, (0 <= k && k <= n@pre) =>
                 (-1000000000 * k <= pre_values[k] &&
                  pre_values[k] <= 1000000000 * k)) &&
              (forall q, (0 <= q && q < Zlength(suf_values)) =>
                 (-1000000000 * (n@pre - i - q) <= suf_values[q] &&
                  suf_values[q] <= 1000000000 * (n@pre - i - q))) &&
              Int64Array::full(a@pre, n@pre + 1, cons(0, values)) *
              Int64Array::full(pre@pre, n@pre + 1, pre_values) *
              Int64Array::seg(suf@pre, 0, i + 1, suf_prefix) *
              Int64Array::seg(suf@pre, i + 1, n@pre + 2, suf_values) *
              CharArray::full(okpre@pre, n@pre + 1, okpre_values) *
              CharArray::seg(oksuf@pre, 0, i + 1, oksuf_prefix) *
              CharArray::seg(oksuf@pre, i + 1, n@pre + 2, oksuf_values)
        */
        suf[i] = a[i] - suf[i + 1];
        /*@ Assert
              exists (pre_values : list Z) (okpre_values : list Z)
                     (suf_values : list Z) (oksuf_values : list Z)
                     (suf_leading : list Z) (oksuf_prefix : list Z)
                     (new_suf_i : Z),
              a == a@pre && n == n@pre && pre == pre@pre && suf == suf@pre &&
              okpre == okpre@pre && oksuf == oksuf@pre &&
              2 <= n@pre && n@pre <= 200000 && n@pre == Zlength(values) &&
              (forall k, (0 <= k && k < n@pre) =>
                 (1 <= values[k] && values[k] <= 1000000000)) &&
              1 <= i && i <= n@pre &&
              Zlength(pre_values) == n@pre + 1 &&
              Zlength(okpre_values) == n@pre + 1 &&
              Zlength(suf_values) == n@pre + 1 - i &&
              Zlength(oksuf_values) == n@pre + 1 - i &&
              Zlength(suf_leading) == i &&
              Zlength(oksuf_prefix) == i + 1 &&
              PrefixResidualState(values, pre_values, okpre_values) &&
              SuffixResidualState(values, i + 1, suf_values, oksuf_values) &&
              new_suf_i == values[i - 1] - suf_values[0] &&
              -1000000000 * (n@pre - i + 1) <= new_suf_i &&
              new_suf_i <= 1000000000 * (n@pre - i + 1) &&
              (forall k, (0 <= k && k <= n@pre) =>
                 (-1000000000 * k <= pre_values[k] &&
                  pre_values[k] <= 1000000000 * k)) &&
              (forall q, (0 <= q && q < Zlength(suf_values)) =>
                 (-1000000000 * (n@pre - i - q) <= suf_values[q] &&
                  suf_values[q] <= 1000000000 * (n@pre - i - q))) &&
              Int64Array::full(a@pre, n@pre + 1, cons(0, values)) *
              Int64Array::full(pre@pre, n@pre + 1, pre_values) *
              Int64Array::seg(suf@pre, 0, i, suf_leading) *
              data_at(suf@pre + i * sizeof(long long),
                      long long, new_suf_i) *
              Int64Array::seg(suf@pre, i + 1, n@pre + 2, suf_values) *
              CharArray::full(okpre@pre, n@pre + 1, okpre_values) *
              CharArray::seg(oksuf@pre, 0, i + 1, oksuf_prefix) *
              CharArray::seg(oksuf@pre, i + 1, n@pre + 2, oksuf_values)
        */
        oksuf[i] = oksuf[i + 1] && suf[i] >= 0;
        /*@ Assert
              exists (pre_values : list Z) (okpre_values : list Z)
                     (suf_values : list Z) (oksuf_values : list Z)
                     (suf_leading : list Z) (oksuf_leading : list Z)
                     (new_suf_i : Z) (new_oksuf_i : Z),
              a == a@pre && n == n@pre && pre == pre@pre && suf == suf@pre &&
              okpre == okpre@pre && oksuf == oksuf@pre &&
              2 <= n@pre && n@pre <= 200000 && n@pre == Zlength(values) &&
              (forall k, (0 <= k && k < n@pre) =>
                 (1 <= values[k] && values[k] <= 1000000000)) &&
              1 <= i && i <= n@pre &&
              Zlength(pre_values) == n@pre + 1 &&
              Zlength(okpre_values) == n@pre + 1 &&
              Zlength(suf_values) == n@pre + 1 - i &&
              Zlength(oksuf_values) == n@pre + 1 - i &&
              Zlength(suf_leading) == i &&
              Zlength(oksuf_leading) == i &&
              PrefixResidualState(values, pre_values, okpre_values) &&
              SuffixResidualState(values, i + 1, suf_values, oksuf_values) &&
              new_suf_i == values[i - 1] - suf_values[0] &&
              (new_oksuf_i == 0 || new_oksuf_i == 1) &&
              (new_oksuf_i == 1 =>
                 oksuf_values[0] == 1 && 0 <= new_suf_i) &&
              (oksuf_values[0] == 1 && 0 <= new_suf_i =>
                 new_oksuf_i == 1) &&
              -1000000000 * (n@pre - i + 1) <= new_suf_i &&
              new_suf_i <= 1000000000 * (n@pre - i + 1) &&
              (forall k, (0 <= k && k <= n@pre) =>
                 (-1000000000 * k <= pre_values[k] &&
                  pre_values[k] <= 1000000000 * k)) &&
              (forall q, (0 <= q && q < Zlength(suf_values)) =>
                 (-1000000000 * (n@pre - i - q) <= suf_values[q] &&
                  suf_values[q] <= 1000000000 * (n@pre - i - q))) &&
              Int64Array::full(a@pre, n@pre + 1, cons(0, values)) *
              Int64Array::full(pre@pre, n@pre + 1, pre_values) *
              Int64Array::seg(suf@pre, 0, i, suf_leading) *
              data_at(suf@pre + i * sizeof(long long),
                      long long, new_suf_i) *
              Int64Array::seg(suf@pre, i + 1, n@pre + 2, suf_values) *
              CharArray::full(okpre@pre, n@pre + 1, okpre_values) *
              CharArray::seg(oksuf@pre, 0, i, oksuf_leading) *
              data_at(oksuf@pre + i * sizeof(char), char, new_oksuf_i) *
              CharArray::seg(oksuf@pre, i + 1, n@pre + 2, oksuf_values)
        */
    }
    if (okpre[n] && pre[n] == 0)
        return 1;
    /*@ Inv Assert
          exists (pre_values : list Z) (okpre_values : list Z)
                 (suf_values : list Z) (oksuf_values : list Z),
          a == a@pre && n == n@pre && pre == pre@pre && suf == suf@pre &&
          okpre == okpre@pre && oksuf == oksuf@pre &&
          2 <= n@pre && n@pre <= 200000 && n@pre == Zlength(values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= values[k] && values[k] <= 1000000000)) &&
          1 <= i && i <= n@pre &&
          Zlength(pre_values) == n@pre + 1 &&
          Zlength(okpre_values) == n@pre + 1 &&
          Zlength(suf_values) == n@pre + 1 &&
          Zlength(oksuf_values) == n@pre + 1 &&
          PrefixResidualState(values, pre_values, okpre_values) &&
          SuffixResidualState(values, 1, suf_values, oksuf_values) &&
          CheckedSwapPrefix(values, pre_values, suf_values,
                            okpre_values, oksuf_values, i) &&
          (forall k, (0 <= k && k <= n@pre) =>
             (-1000000000 * k <= pre_values[k] &&
              pre_values[k] <= 1000000000 * k)) &&
          (forall q, (0 <= q && q <= n@pre) =>
             (-1000000000 * (n@pre - q) <= suf_values[q] &&
              suf_values[q] <= 1000000000 * (n@pre - q))) &&
          Int64Array::full(a@pre, n@pre + 1, cons(0, values)) *
          Int64Array::full(pre@pre, n@pre + 1, pre_values) *
          Int64Array::seg_shape(suf@pre, 0, 1) *
          Int64Array::seg(suf@pre, 1, n@pre + 2, suf_values) *
          CharArray::full(okpre@pre, n@pre + 1, okpre_values) *
          CharArray::seg_shape(oksuf@pre, 0, 1) *
          CharArray::seg(oksuf@pre, 1, n@pre + 2, oksuf_values)
    */
    for (int i = 1; i < n; i++) {         /* swap piles i and i+1 */
        if (!okpre[i - 1] || !oksuf[i + 2])
            continue;
        long long x = a[i + 1] - pre[i - 1];
        if (x < 0)
            continue;
        long long y = a[i] - x;
        if (y < 0)
            continue;
        if (y == suf[i + 2])
            return 1;
    }
    return 0;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static long long a[200005], pre[200005], suf[200007];
//     static char okpre[200005], oksuf[200007];
//     while (t--) {
//         int n;
//         scanf("%d", &n);
//         for (int i = 1; i <= n; i++)
//             scanf("%lld", &a[i]);
//         puts(solver(a, n, pre, suf, okpre, oksuf) ? "YES" : "NO");
//     }
//     return 0;
// }
