/*
 * Codeforces 1436/F - Sum Over Subsets  (rating 2800, NUMBER THEORY)
 *
 * Count first for every d the sets whose elements are all divisible by d, then
 * peel off the multiples to keep only gcd exactly d.  Over a pool of k items
 * with sum S and square-sum S2, summing sum(A)*sum(B) over all (A, B) with
 * B = A minus one element gives
 *     S2 * 2^(k-2) * (k-1)  +  (S^2 - S2) * (2^(k-3)*(k-2) + 2^(k-2)),
 * since a_i^2 appears once per element dropped from A, and a_i*a_j appears
 * both when a third element is dropped and when a_i itself is the dropped one.
 */

// #include <stdio.h>
// #include <stdlib.h>
// #include <string.h>

#define MOD 998244353LL
#define MAXV 100001

/*@ Extern Coq
      (pow_mod : Z -> Z -> Z)
      (pool_closed_form : Z -> Z -> Z -> Z)
      (PowmodState : Z -> Z -> Z -> Z -> Z -> Prop)
      (AnsExactPrefix : list Z -> list Z -> Z -> list Z -> Z -> Prop)
      (PoolAggregate : list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (PeelState : list Z -> list Z -> Z -> Z -> Z -> Prop)
*/

static long long powmod(long long b, long long e)
/*@
    Require
      0 <= b && b < 998244353 &&
      0 <= e && e <= 100000000000000 &&
      emp
    Ensure
      __return == pow_mod(b@pre, e@pre) &&
      0 <= __return && __return < 998244353 &&
      emp
*/
{
    long long r = 1;
    b %= MOD;
    if (b < 0)
        b += MOD;
    /*@ Inv Assert
          0 <= e && e <= 100000000000000 &&
          0 <= b && b < 998244353 &&
          0 <= r && r < 998244353 &&
          PowmodState(b@pre, e@pre, b, e, r) &&
          emp
     */
    while (e > 0) {
        if (e & 1)
            r = r * b % MOD;
        b = b * b % MOD;
        e >>= 1;
    }
    return r;
}

/* pool_sum: the contribution of a pool of k items with sums S and S2. */
static long long pool_sum(long long k, long long S, long long S2)
/*@
    Require
      0 <= k && k <= 100000000000000 &&
      0 <= S && S < 998244353 &&
      0 <= S2 && S2 < 998244353 &&
      emp
    Ensure
      __return == pool_closed_form(k@pre, S@pre, S2@pre) &&
      0 <= __return && __return < 998244353 &&
      emp
*/
{
    if (k < 2)
        return 0;
    long long cross = ((S * S - S2) % MOD + MOD) % MOD;
    long long p2 = powmod(2, k - 2);
    long long total = S2 % MOD * p2 % MOD * ((k - 1) % MOD) % MOD;
    long long second = p2;                /* the 2^(k-2) term */
    if (k >= 3)
        second = (second + powmod(2, k - 3) * ((k - 2) % MOD)) % MOD;
    total = (total + cross * second) % MOD;
    return total;
}

/* solver: the required sum over all valid (A, B) with gcd(A) = 1. */
/* QCP_INSERT_BEGIN:shard09-P096-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P096_1436F_sum_over_subsets_lib */
/*@ Extern Coq
      (Pre : list Z -> list Z -> Prop)
      (Spec : list Z -> list Z -> Z -> Prop)
      (maximum_value : list Z -> Z)
      (aggregate_arrays : list Z -> list Z -> list Z -> list Z -> list Z -> Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P096-solver-support */
static long long solver(const long long *cnt, const long long *sum,
                        const long long *sqsum, long long *ans, int maxv)
/* QCP_INSERT_BEGIN:shard09-P096-solver-contract */
/*@ With (vals : list Z) (freq : list Z)
    Require
      Pre(vals, freq) && 1 <= Zlength(vals) && Zlength(vals) <= 100000 && Zlength(freq) == Zlength(vals) && (forall i, (0 <= i && i < Zlength(vals)) => (1 <= vals[i] && vals[i] <= 100000)) && (forall i, (0 <= i && i < Zlength(freq)) => (1 <= freq[i] && freq[i] <= 1000000000)) &&
      maxv == maximum_value(vals) && exists (cnts : list Z) (sums : list Z) (squares : list Z), aggregate_arrays(vals, freq, cnts, sums, squares, maxv) && Int64Array::full(cnt, maxv + 1, cnts) * Int64Array::full(sum, maxv + 1, sums) * Int64Array::full(sqsum, maxv + 1, squares) * Int64Array::full_shape(ans, maxv + 1)
    Ensure
      Spec(vals, freq, __return) &&
        exists (cnts : list Z) (sums : list Z) (squares : list Z), aggregate_arrays(vals, freq, cnts, sums, squares, maxv) && Int64Array::full(cnt, maxv + 1, cnts) * Int64Array::full(sum, maxv + 1, sums) * Int64Array::full(sqsum, maxv + 1, squares) * Int64Array::full_shape(ans, maxv + 1)
*/
/* QCP_INSERT_END:shard09-P096-solver-contract */
{
    /*@ Inv Assert
          exists cnts sums squares anslist,
            cnt == cnt@pre && sum == sum@pre && sqsum == sqsum@pre &&
            ans == ans@pre && maxv == maxv@pre &&
            Pre(vals, freq) &&
            1 <= Zlength(vals) && Zlength(vals) <= 100000 &&
            Zlength(freq) == Zlength(vals) &&
            (forall i, (0 <= i && i < Zlength(vals)) =>
              (1 <= vals[i] && vals[i] <= 100000)) &&
            (forall i, (0 <= i && i < Zlength(freq)) =>
              (1 <= freq[i] && freq[i] <= 1000000000)) &&
            maxv@pre == maximum_value(vals) &&
            1 <= maxv@pre && maxv@pre <= 100000 &&
            0 <= d && d <= maxv@pre &&
            aggregate_arrays(vals, freq, cnts, sums, squares, maxv@pre) &&
            Zlength(anslist) == maxv@pre + 1 &&
            (forall w, (0 <= w && w <= maxv@pre) =>
              (0 <= cnts[w] && cnts[w] <= 1000000000 &&
               0 <= sums[w] && sums[w] < 998244353 &&
               0 <= squares[w] && squares[w] < 998244353)) &&
            (forall w, (d < w && w <= maxv@pre) =>
              (0 <= anslist[w] && anslist[w] < 998244353)) &&
            AnsExactPrefix(vals, freq, maxv@pre, anslist, d) &&
            Int64Array::full(cnt, maxv@pre + 1, cnts) *
            Int64Array::full(sum, maxv@pre + 1, sums) *
            Int64Array::full(sqsum, maxv@pre + 1, squares) *
            Int64Array::full(ans, maxv@pre + 1, anslist)
     */
    for (int d = maxv; d >= 1; d--) {
        long long k = 0, S = 0, S2 = 0;
        /*@ Inv Assert
              exists cnts sums squares anslist t,
                cnt == cnt@pre && sum == sum@pre && sqsum == sqsum@pre &&
                ans == ans@pre && maxv == maxv@pre &&
                Pre(vals, freq) &&
                1 <= Zlength(vals) && Zlength(vals) <= 100000 &&
                Zlength(freq) == Zlength(vals) &&
                (forall i, (0 <= i && i < Zlength(vals)) =>
                  (1 <= vals[i] && vals[i] <= 100000)) &&
                (forall i, (0 <= i && i < Zlength(freq)) =>
                  (1 <= freq[i] && freq[i] <= 1000000000)) &&
                maxv@pre == maximum_value(vals) &&
                1 <= maxv@pre && maxv@pre <= 100000 &&
                1 <= d && d <= maxv@pre &&
                1 <= t && v == t * d && d <= v && v <= maxv@pre + d &&
                (t - 1) * d <= maxv@pre && t - 1 <= 100000 &&
                0 <= k && k <= (t - 1) * 1000000000 &&
                0 <= S && S < 998244353 &&
                0 <= S2 && S2 < 998244353 &&
                aggregate_arrays(vals, freq, cnts, sums, squares, maxv@pre) &&
                Zlength(anslist) == maxv@pre + 1 &&
                (forall w, (0 <= w && w <= maxv@pre) =>
                  (0 <= cnts[w] && cnts[w] <= 1000000000 &&
                   0 <= sums[w] && sums[w] < 998244353 &&
                   0 <= squares[w] && squares[w] < 998244353)) &&
                (forall w, (d < w && w <= maxv@pre) =>
                  (0 <= anslist[w] && anslist[w] < 998244353)) &&
                PoolAggregate(cnts, sums, squares, d, t - 1, k, S, S2) &&
                AnsExactPrefix(vals, freq, maxv@pre, anslist, d) &&
                Int64Array::full(cnt, maxv@pre + 1, cnts) *
                Int64Array::full(sum, maxv@pre + 1, sums) *
                Int64Array::full(sqsum, maxv@pre + 1, squares) *
                Int64Array::full(ans, maxv@pre + 1, anslist)
         */
        for (int v = d; v <= maxv; v += d) {
            k += cnt[v];
            S = (S + sum[v]) % MOD;
            S2 = (S2 + sqsum[v]) % MOD;
        }
        long long cur = pool_sum(k, S, S2);
        /*@ Assert
              exists cnts sums squares anslist,
                cnt == cnt@pre && sum == sum@pre && sqsum == sqsum@pre &&
                ans == ans@pre && maxv == maxv@pre &&
                Pre(vals, freq) &&
                1 <= Zlength(vals) && Zlength(vals) <= 100000 &&
                Zlength(freq) == Zlength(vals) &&
                (forall i, (0 <= i && i < Zlength(vals)) =>
                  (1 <= vals[i] && vals[i] <= 100000)) &&
                (forall i, (0 <= i && i < Zlength(freq)) =>
                  (1 <= freq[i] && freq[i] <= 1000000000)) &&
                maxv@pre == maximum_value(vals) &&
                1 <= maxv@pre && maxv@pre <= 100000 &&
                1 <= d && d <= maxv@pre &&
                0 <= cur && cur < 998244353 &&
                0 <= k && k <= 100000000000000 &&
                0 <= S && S < 998244353 &&
                0 <= S2 && S2 < 998244353 &&
                aggregate_arrays(vals, freq, cnts, sums, squares, maxv@pre) &&
                Zlength(anslist) == maxv@pre + 1 &&
                (forall w, (0 <= w && w <= maxv@pre) =>
                  (0 <= cnts[w] && cnts[w] <= 1000000000 &&
                   0 <= sums[w] && sums[w] < 998244353 &&
                   0 <= squares[w] && squares[w] < 998244353)) &&
                (forall w, (d < w && w <= maxv@pre) =>
                  (0 <= anslist[w] && anslist[w] < 998244353)) &&
                PeelState(vals, freq, d, 1, cur) &&
                AnsExactPrefix(vals, freq, maxv@pre, anslist, d) &&
                Int64Array::full(cnt, maxv@pre + 1, cnts) *
                Int64Array::full(sum, maxv@pre + 1, sums) *
                Int64Array::full(sqsum, maxv@pre + 1, squares) *
                Int64Array::full(ans, maxv@pre + 1, anslist)
         */
        /*@ Inv Assert
              exists cnts sums squares anslist t,
                cnt == cnt@pre && sum == sum@pre && sqsum == sqsum@pre &&
                ans == ans@pre && maxv == maxv@pre &&
                Pre(vals, freq) &&
                1 <= Zlength(vals) && Zlength(vals) <= 100000 &&
                Zlength(freq) == Zlength(vals) &&
                (forall i, (0 <= i && i < Zlength(vals)) =>
                  (1 <= vals[i] && vals[i] <= 100000)) &&
                (forall i, (0 <= i && i < Zlength(freq)) =>
                  (1 <= freq[i] && freq[i] <= 1000000000)) &&
                maxv@pre == maximum_value(vals) &&
                1 <= maxv@pre && maxv@pre <= 100000 &&
                1 <= d && d <= maxv@pre &&
                2 <= t && v == t * d && 2 * d <= v && v <= maxv@pre + d &&
                0 <= cur && cur < 998244353 &&
                0 <= k && k <= 100000000000000 &&
                0 <= S && S < 998244353 &&
                0 <= S2 && S2 < 998244353 &&
                aggregate_arrays(vals, freq, cnts, sums, squares, maxv@pre) &&
                Zlength(anslist) == maxv@pre + 1 &&
                (forall w, (0 <= w && w <= maxv@pre) =>
                  (0 <= cnts[w] && cnts[w] <= 1000000000 &&
                   0 <= sums[w] && sums[w] < 998244353 &&
                   0 <= squares[w] && squares[w] < 998244353)) &&
                (forall w, (d < w && w <= maxv@pre) =>
                  (0 <= anslist[w] && anslist[w] < 998244353)) &&
                PeelState(vals, freq, d, t - 1, cur) &&
                AnsExactPrefix(vals, freq, maxv@pre, anslist, d) &&
                Int64Array::full(cnt, maxv@pre + 1, cnts) *
                Int64Array::full(sum, maxv@pre + 1, sums) *
                Int64Array::full(sqsum, maxv@pre + 1, squares) *
                Int64Array::full(ans, maxv@pre + 1, anslist)
         */
        for (int v = 2 * d; v <= maxv; v += d)
            cur = (cur - ans[v] % MOD + MOD) % MOD;
        ans[d] = cur;
    }
    return ans[1];
}

// int main(void)
// {
//     int m;
//     if (scanf("%d", &m) != 1)
//         return 0;
//     static long long cnt[MAXV], sum[MAXV], sqsum[MAXV], ans[MAXV];
//     int maxv = 1;
//     for (int i = 0; i < m; i++) {
//         long long a, f;
//         scanf("%lld %lld", &a, &f);
//         cnt[a] += f;
//         sum[a] = (sum[a] + a % MOD * (f % MOD)) % MOD;
//         sqsum[a] = (sqsum[a] + a % MOD * (a % MOD) % MOD * (f % MOD)) % MOD;
//         if (a > maxv)
//             maxv = (int)a;
//     }
//     printf("%lld\n", solver(cnt, sum, sqsum, ans, maxv));
//     return 0;
// }
