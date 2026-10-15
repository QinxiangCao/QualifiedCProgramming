/*
 * Codeforces 847/H - Load Testing  (rating 1600, GREEDY)
 *
 * Requests can only be added, so from the left the cheapest strictly
 * increasing profile is inc[i] = max(a[i], inc[i-1]+1), and symmetrically from
 * the right.  Trying every peak, the cost is the two prefix costs minus the
 * double-counted peak, whose value must be max(inc[i], dec[i]).
 */

// #include <stdio.h>

/* QCP_INSERT_BEGIN:shard09-P050-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P050_847H_load_testing_lib */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P050-solver-support */

/*@ Extern Coq
      (LeftProfilePrefix : list Z -> list Z -> Prop)
      (RightProfileSuffix : list Z -> list Z -> Prop)
      (PrefixCosts : list Z -> list Z -> list Z -> Prop)
      (SuffixCosts : list Z -> list Z -> list Z -> Prop)
      (BestPeakPrefix : list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
*/

/*@ Extern Coq
      (PartialPrefixCosts : list Z -> list Z -> list Z -> Prop)
      (PartialSuffixCosts : list Z -> list Z -> list Z -> Prop)
*/

/* solver: minimum requests to add.  pre/suf are scratch arrays of size n. */
static long long solver(const long long *a, int n, long long *inc,
                        long long *dec, long long *pre, long long *suf)
/* QCP_INSERT_BEGIN:shard09-P050-solver-contract */
/*@ With (values : list Z)
    Require
      1 <= n && n <= 100000 && (forall i, (0 <= i && i < n) => (1 <= values[i] && values[i] <= 1000000000)) &&
      n == Zlength(values) && Int64Array::full(a, n, values) * Int64Array::undef_full(inc, n) * Int64Array::undef_full(dec, n) * Int64Array::undef_full(pre, n) * Int64Array::undef_full(suf, n)
    Ensure
      Spec(values, __return) &&
      Int64Array::full(a, n, values) * Int64Array::full_shape(inc, n) * Int64Array::full_shape(dec, n) * Int64Array::full_shape(pre, n) * Int64Array::full_shape(suf, n)
*/
/* QCP_INSERT_END:shard09-P050-solver-contract */
{
    inc[0] = a[0];
    /*@ Inv Assert
          exists (inc_values : list Z),
          a == a@pre && n == n@pre && inc == inc@pre && dec == dec@pre &&
          pre == pre@pre && suf == suf@pre &&
          1 <= n@pre && n@pre <= 100000 && n@pre == Zlength(values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= values[k] && values[k] <= 1000000000)) &&
          1 <= i && i <= n@pre && Zlength(inc_values) == i &&
          LeftProfilePrefix(values, inc_values) &&
          (forall k, (0 <= k && k < i) =>
             (1 <= inc_values[k] && inc_values[k] <= 1000100000)) &&
          Int64Array::full(a@pre, n@pre, values) *
          Int64Array::seg(inc@pre, 0, i, inc_values) *
          Int64Array::undef_seg(inc@pre, i, n@pre) *
          Int64Array::undef_full(dec@pre, n@pre) *
          Int64Array::undef_full(pre@pre, n@pre) *
          Int64Array::undef_full(suf@pre, n@pre)
    */
    for (int i = 1; i < n; i++)
        inc[i] = a[i] > inc[i - 1] + 1 ? a[i] : inc[i - 1] + 1;
    /*@ Assert
          exists (inc_values : list Z),
          a == a@pre && n == n@pre && inc == inc@pre && dec == dec@pre &&
          pre == pre@pre && suf == suf@pre &&
          1 <= n@pre && n@pre <= 100000 && n@pre == Zlength(values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= values[k] && values[k] <= 1000000000)) &&
          Zlength(inc_values) == n@pre && LeftProfilePrefix(values, inc_values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= inc_values[k] && inc_values[k] <= 1000100000)) &&
          Int64Array::full(a@pre, n@pre, values) *
          Int64Array::full(inc@pre, n@pre, inc_values) *
          Int64Array::undef_full(dec@pre, n@pre) *
          Int64Array::undef_full(pre@pre, n@pre) *
          Int64Array::undef_full(suf@pre, n@pre)
    */
    dec[n - 1] = a[n - 1];
    /*@ Inv Assert
          exists (inc_values : list Z) (dec_values : list Z),
          a == a@pre && n == n@pre && inc == inc@pre && dec == dec@pre &&
          pre == pre@pre && suf == suf@pre &&
          1 <= n@pre && n@pre <= 100000 && n@pre == Zlength(values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= values[k] && values[k] <= 1000000000)) &&
          Zlength(inc_values) == n@pre && LeftProfilePrefix(values, inc_values) &&
          -1 <= i && i <= n@pre - 2 && Zlength(dec_values) == n@pre - i - 1 &&
          RightProfileSuffix(values, dec_values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= inc_values[k] && inc_values[k] <= 1000100000)) &&
          (forall k, (0 <= k && k < Zlength(dec_values)) =>
             (1 <= dec_values[k] && dec_values[k] <= 1000100000)) &&
          Int64Array::full(a@pre, n@pre, values) *
          Int64Array::full(inc@pre, n@pre, inc_values) *
          Int64Array::undef_seg(dec@pre, 0, i + 1) *
          Int64Array::seg(dec@pre, i + 1, n@pre, dec_values) *
          Int64Array::undef_full(pre@pre, n@pre) *
          Int64Array::undef_full(suf@pre, n@pre)
    */
    for (int i = n - 2; i >= 0; i--)
        dec[i] = a[i] > dec[i + 1] + 1 ? a[i] : dec[i + 1] + 1;

    /*@ Assert
          exists (inc_values : list Z) (dec_values : list Z),
          a == a@pre && n == n@pre && inc == inc@pre && dec == dec@pre &&
          pre == pre@pre && suf == suf@pre &&
          1 <= n@pre && n@pre <= 100000 && n@pre == Zlength(values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= values[k] && values[k] <= 1000000000)) &&
          Zlength(inc_values) == n@pre && LeftProfilePrefix(values, inc_values) &&
          Zlength(dec_values) == n@pre && RightProfileSuffix(values, dec_values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= inc_values[k] && inc_values[k] <= 1000100000)) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= dec_values[k] && dec_values[k] <= 1000100000)) &&
          Int64Array::full(a@pre, n@pre, values) *
          Int64Array::full(inc@pre, n@pre, inc_values) *
          Int64Array::full(dec@pre, n@pre, dec_values) *
          Int64Array::undef_full(pre@pre, n@pre) *
          Int64Array::undef_full(suf@pre, n@pre)
    */

    pre[0] = inc[0] - a[0];
    /*@ Inv Assert
          exists (inc_values : list Z) (dec_values : list Z) (pre_values : list Z),
          a == a@pre && n == n@pre && inc == inc@pre && dec == dec@pre &&
          pre == pre@pre && suf == suf@pre &&
          1 <= n@pre && n@pre <= 100000 && n@pre == Zlength(values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= values[k] && values[k] <= 1000000000)) &&
          Zlength(inc_values) == n@pre && LeftProfilePrefix(values, inc_values) &&
          Zlength(dec_values) == n@pre && RightProfileSuffix(values, dec_values) &&
          1 <= i && i <= n@pre && Zlength(pre_values) == i &&
          PartialPrefixCosts(values, inc_values, pre_values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= inc_values[k] && inc_values[k] <= 1000100000 &&
              1 <= dec_values[k] && dec_values[k] <= 1000100000)) &&
          (forall k, (0 <= k && k < i) =>
             (0 <= pre_values[k] && pre_values[k] <= 100010000000000)) &&
          Int64Array::full(a@pre, n@pre, values) *
          Int64Array::full(inc@pre, n@pre, inc_values) *
          Int64Array::full(dec@pre, n@pre, dec_values) *
          Int64Array::seg(pre@pre, 0, i, pre_values) *
          Int64Array::undef_seg(pre@pre, i, n@pre) *
          Int64Array::undef_full(suf@pre, n@pre)
    */
    for (int i = 1; i < n; i++)
        pre[i] = pre[i - 1] + (inc[i] - a[i]);
    /*@ Assert
          exists (inc_values : list Z) (dec_values : list Z) (pre_values : list Z),
          a == a@pre && n == n@pre && inc == inc@pre && dec == dec@pre &&
          pre == pre@pre && suf == suf@pre &&
          1 <= n@pre && n@pre <= 100000 && n@pre == Zlength(values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= values[k] && values[k] <= 1000000000)) &&
          Zlength(inc_values) == n@pre && LeftProfilePrefix(values, inc_values) &&
          Zlength(dec_values) == n@pre && RightProfileSuffix(values, dec_values) &&
          Zlength(pre_values) == n@pre && PrefixCosts(values, inc_values, pre_values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= inc_values[k] && inc_values[k] <= 1000100000 &&
              1 <= dec_values[k] && dec_values[k] <= 1000100000 &&
              0 <= pre_values[k] && pre_values[k] <= 100010000000000)) &&
          Int64Array::full(a@pre, n@pre, values) *
          Int64Array::full(inc@pre, n@pre, inc_values) *
          Int64Array::full(dec@pre, n@pre, dec_values) *
          Int64Array::full(pre@pre, n@pre, pre_values) *
          Int64Array::undef_full(suf@pre, n@pre)
    */
    suf[n - 1] = dec[n - 1] - a[n - 1];
    /*@ Inv Assert
          exists (inc_values : list Z) (dec_values : list Z)
                 (pre_values : list Z) (suf_values : list Z),
          a == a@pre && n == n@pre && inc == inc@pre && dec == dec@pre &&
          pre == pre@pre && suf == suf@pre &&
          1 <= n@pre && n@pre <= 100000 && n@pre == Zlength(values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= values[k] && values[k] <= 1000000000)) &&
          Zlength(inc_values) == n@pre && LeftProfilePrefix(values, inc_values) &&
          Zlength(dec_values) == n@pre && RightProfileSuffix(values, dec_values) &&
          Zlength(pre_values) == n@pre && PrefixCosts(values, inc_values, pre_values) &&
          -1 <= i && i <= n@pre - 2 && Zlength(suf_values) == n@pre - i - 1 &&
          PartialSuffixCosts(values, dec_values, suf_values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= inc_values[k] && inc_values[k] <= 1000100000 &&
              1 <= dec_values[k] && dec_values[k] <= 1000100000 &&
              0 <= pre_values[k] && pre_values[k] <= 100010000000000)) &&
          (forall k, (0 <= k && k < Zlength(suf_values)) =>
             (0 <= suf_values[k] && suf_values[k] <= 100010000000000)) &&
          Int64Array::full(a@pre, n@pre, values) *
          Int64Array::full(inc@pre, n@pre, inc_values) *
          Int64Array::full(dec@pre, n@pre, dec_values) *
          Int64Array::full(pre@pre, n@pre, pre_values) *
          Int64Array::undef_seg(suf@pre, 0, i + 1) *
          Int64Array::seg(suf@pre, i + 1, n@pre, suf_values)
    */
    for (int i = n - 2; i >= 0; i--)
        suf[i] = suf[i + 1] + (dec[i] - a[i]);

    /*@ Assert
          exists (inc_values : list Z) (dec_values : list Z)
                 (pre_values : list Z) (suf_values : list Z),
          a == a@pre && n == n@pre && inc == inc@pre && dec == dec@pre &&
          pre == pre@pre && suf == suf@pre &&
          1 <= n@pre && n@pre <= 100000 && n@pre == Zlength(values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= values[k] && values[k] <= 1000000000)) &&
          Zlength(inc_values) == n@pre && LeftProfilePrefix(values, inc_values) &&
          Zlength(dec_values) == n@pre && RightProfileSuffix(values, dec_values) &&
          Zlength(pre_values) == n@pre && PrefixCosts(values, inc_values, pre_values) &&
          Zlength(suf_values) == n@pre && SuffixCosts(values, dec_values, suf_values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= inc_values[k] && inc_values[k] <= 1000100000 &&
              1 <= dec_values[k] && dec_values[k] <= 1000100000 &&
              0 <= pre_values[k] && pre_values[k] <= 100010000000000 &&
              0 <= suf_values[k] && suf_values[k] <= 100010000000000)) &&
          Int64Array::full(a@pre, n@pre, values) *
          Int64Array::full(inc@pre, n@pre, inc_values) *
          Int64Array::full(dec@pre, n@pre, dec_values) *
          Int64Array::full(pre@pre, n@pre, pre_values) *
          Int64Array::full(suf@pre, n@pre, suf_values)
    */

    long long best = -1;
    /*@ Inv Assert
          exists (inc_values : list Z) (dec_values : list Z)
                 (pre_values : list Z) (suf_values : list Z),
          a == a@pre && n == n@pre && inc == inc@pre && dec == dec@pre &&
          pre == pre@pre && suf == suf@pre &&
          1 <= n@pre && n@pre <= 100000 && n@pre == Zlength(values) &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= values[k] && values[k] <= 1000000000)) &&
          Zlength(inc_values) == n@pre && LeftProfilePrefix(values, inc_values) &&
          Zlength(dec_values) == n@pre && RightProfileSuffix(values, dec_values) &&
          Zlength(pre_values) == n@pre && PrefixCosts(values, inc_values, pre_values) &&
          Zlength(suf_values) == n@pre && SuffixCosts(values, dec_values, suf_values) &&
          0 <= i && i <= n@pre && BestPeakPrefix(values, inc_values, dec_values,
                                                   pre_values, suf_values, i, best) &&
          -1 <= best && best <= 200020000000000 &&
          (forall k, (0 <= k && k < n@pre) =>
             (1 <= inc_values[k] && inc_values[k] <= 1000100000 &&
              1 <= dec_values[k] && dec_values[k] <= 1000100000 &&
              0 <= pre_values[k] && pre_values[k] <= 100010000000000 &&
              0 <= suf_values[k] && suf_values[k] <= 100010000000000)) &&
          Int64Array::full(a@pre, n@pre, values) *
          Int64Array::full(inc@pre, n@pre, inc_values) *
          Int64Array::full(dec@pre, n@pre, dec_values) *
          Int64Array::full(pre@pre, n@pre, pre_values) *
          Int64Array::full(suf@pre, n@pre, suf_values)
    */
    for (int i = 0; i < n; i++) {
        long long peak = inc[i] > dec[i] ? inc[i] : dec[i];
        long long cost = pre[i] + suf[i] - (inc[i] - a[i]) - (dec[i] - a[i])
                         + (peak - a[i]);
        if (best < 0 || cost < best)
            best = cost;
    }
    return best;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static long long a[100005], inc[100005], dec[100005], pre[100005], suf[100005];
//     for (int i = 0; i < n; i++)
//         scanf("%lld", &a[i]);
//     printf("%lld\n", solver(a, n, inc, dec, pre, suf));
//     return 0;
// }
