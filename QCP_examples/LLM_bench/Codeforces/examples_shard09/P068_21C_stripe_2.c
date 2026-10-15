/*
 * Codeforces 21/C - Stripe 2  (rating 2000, PREFIX SUMS)
 *
 * The total must split into three equal thirds.  Sweep the second cut from
 * left to right, counting on the way how many earlier positions carry prefix
 * sum S/3; whenever the prefix at the current position is 2S/3 those counted
 * positions each give one valid pair of cuts.
 */

// #include <stdio.h>

/* QCP_INSERT_BEGIN:shard09-P068-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P068_21C_stripe_2_lib */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (PrefixSum : list Z -> Z -> Z)
      (FirstCutCount : list Z -> Z -> Z -> Z)
      (ValidPairCount : list Z -> Z -> Z -> Z)
*/
/* QCP_INSERT_END:shard09-P068-solver-support */

/* solver: pure.  Number of ways to cut a[0..n-1] into three equal-sum parts. */
static long long solver(const long long *a, int n)
/* QCP_INSERT_BEGIN:shard09-P068-solver-contract */
/*@ With (values : list Z)
    Require
      1 <= n && n <= 100000 && (forall i, (0 <= i && i < n) => (-10000 <= values[i] && values[i] <= 10000)) &&
      n == Zlength(values) && Int64Array::full(a, n, values)
    Ensure
      Spec(values, __return) &&
      Int64Array::full(a, n, values)
*/
/* QCP_INSERT_END:shard09-P068-solver-contract */
{
    long long total = 0;
    /*@ Inv Assert
          a == a@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          Zlength(values) == n@pre &&
          (forall (k : Z), (0 <= k && k < n@pre) => (-10000 <= values[k] && values[k] <= 10000)) &&
          0 <= i && i <= n@pre &&
          total == PrefixSum(values, i) &&
          -10000 * i <= total && total <= 10000 * i &&
          Int64Array::full(a@pre, n@pre, values)
    */
    for (int i = 0; i < n; i++)
        total += a[i];
    if (total % 3 != 0)
        /*@ Assert
              a == a@pre && n == n@pre &&
              1 <= n@pre && n@pre <= 100000 &&
              Zlength(values) == n@pre &&
              (forall (k : Z), (0 <= k && k < n@pre) => (-10000 <= values[k] && values[k] <= 10000)) &&
              total == PrefixSum(values, n@pre) &&
              Spec(values, 0) &&
              Int64Array::full(a@pre, n@pre, values)
        */
        return 0;
    long long third = total / 3, run = 0, first = 0, ways = 0;
    /*@ Inv Assert
          a == a@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          Zlength(values) == n@pre &&
          (forall (k : Z), (0 <= k && k < n@pre) => (-10000 <= values[k] && values[k] <= 10000)) &&
          total == PrefixSum(values, n@pre) && total == 3 * third &&
          -10000 * n@pre <= total && total <= 10000 * n@pre &&
          0 <= i && i <= n@pre - 1 &&
          run == PrefixSum(values, i) &&
          first == FirstCutCount(values, third, i) &&
          ways == ValidPairCount(values, third, i) &&
          -10000 * i <= run && run <= 10000 * i &&
          0 <= first && first <= i &&
          0 <= ways && ways <= 100000 * i &&
          Int64Array::full(a@pre, n@pre, values)
    */
    for (int i = 0; i + 1 < n; i++) {     /* second cut goes after index i */
        run += a[i];
        if (i >= 1 && run == 2 * third)
            ways += first;
        if (run == third)
            first++;                      /* usable as a first cut later */
    }
    return ways;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static long long a[100005];
//     for (int i = 0; i < n; i++)
//         scanf("%lld", &a[i]);
//     printf("%lld\n", solver(a, n));
//     return 0;
// }
