/*
 * Codeforces 223/C - Partial Sums  (rating 1900, COMBINATORICS)
 *
 * Applying the prefix-sum operator k times sends a_j to position i with the
 * multiplicity C(k-1 + i-j, i-j) (a standard stars-and-bars count of the ways
 * to distribute the k rounds).  n <= 2000, so evaluate that convolution
 * directly after building the coefficients incrementally.
 */

// #include <stdio.h>

/* QCP_INSERT_BEGIN:shard09-P064-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P064_223C_partial_sums_lib */
/*@ Extern Coq
      (Spec : Z -> list Z -> list Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P064-solver-support */

/*@ Extern Coq
      (ModPower : Z -> Z -> Z -> Prop)
*/

/*@ Extern Coq
      (PowerLoopState : Z -> Z -> Z -> Z -> Z -> Prop)
      (IdentityPrefix : list Z -> list Z -> Prop)
      (CoefficientPrefix : Z -> list Z -> Prop)
      (ConvolutionPrefix : list Z -> list Z -> list Z -> Prop)
      (ConvolutionAccumulator : list Z -> list Z -> Z -> Z -> Z -> Prop)
*/

#define MOD 1000000007LL

/* power: modular exponentiation, used for the modular inverse. */
static long long power(long long b, long long e)
/*@ Require
      0 <= b && b < 1000000007 &&
      0 <= e && e <= 1000000007
    Ensure
      0 <= __return && __return < 1000000007 &&
      ModPower(b, e, __return)
*/
{
    long long r = 1;
    b %= MOD;
    /*@ Inv Assert
          0 <= b@pre && b@pre < 1000000007 &&
          0 <= e@pre && e@pre <= 1000000007 &&
          0 <= b && b < 1000000007 &&
          0 <= r && r < 1000000007 &&
          0 <= e && e <= e@pre &&
          PowerLoopState(b@pre, e@pre, r, b, e)
    */
    while (e) {
        if (e & 1)
            r = r * b % MOD;
        b = b * b % MOD;
        e >>= 1;
    }
    return r;
}

/* solver: pure.  out[i] = sum_j C(k-1+i-j, i-j) * a[j] (mod 1e9+7). */
static void solver(const long long *a, int n, long long k, long long *out,
                   long long *coef)
/* QCP_INSERT_BEGIN:shard09-P064-solver-contract */
/*@ With (values : list Z)
    Require
      0 <= k && k <= 1000000000 &&
      1 <= n && n <= 2000 && (forall i, (0 <= i && i < n) => (0 <= values[i] && values[i] <= 1000000000)) &&
      n == Zlength(values) && Int64Array::full(a, n, values) * Int64Array::undef_full(out, n) * Int64Array::undef_full(coef, n)
    Ensure
      exists (out_spec : list Z),
        Spec(k, values, out_spec) &&
        Int64Array::full(a, n, values) * Int64Array::full(out, n, out_spec) * ((k == 0 && Int64Array::undef_full(coef, n)) || (k != 0 && Int64Array::full_shape(coef, n)))
*/
/* QCP_INSERT_END:shard09-P064-solver-contract */
{
    if (k == 0) {
        /*@ Inv Assert
              exists (written : list Z),
              a == a@pre && n == n@pre && k == k@pre &&
              out == out@pre && coef == coef@pre && k@pre == 0 &&
              1 <= n@pre && n@pre <= 2000 &&
              n@pre == Zlength(values) &&
              (forall q, (0 <= q && q < n@pre) =>
                 (0 <= values[q] && values[q] <= 1000000000)) &&
              0 <= i && i <= n@pre && Zlength(written) == i &&
              IdentityPrefix(values, written) &&
              Int64Array::full(a@pre, n@pre, values) *
              Int64Array::seg(out@pre, 0, i, written) *
              Int64Array::undef_seg(out@pre, i, n@pre) *
              Int64Array::undef_full(coef@pre, n@pre)
        */
        for (int i = 0; i < n; i++)
            out[i] = a[i] % MOD;
        return;
    }
    coef[0] = 1;
    /*@ Inv Assert
          exists (coefficients : list Z),
          a == a@pre && n == n@pre && k == k@pre &&
          out == out@pre && coef == coef@pre &&
          1 <= k@pre && k@pre <= 1000000000 &&
          1 <= n@pre && n@pre <= 2000 &&
          n@pre == Zlength(values) &&
          (forall q, (0 <= q && q < n@pre) =>
             (0 <= values[q] && values[q] <= 1000000000)) &&
          1 <= d && d <= n@pre && Zlength(coefficients) == d &&
          (forall q, (0 <= q && q < d) =>
             (0 <= coefficients[q] && coefficients[q] < 1000000007)) &&
          CoefficientPrefix(k@pre, coefficients) &&
          Int64Array::full(a@pre, n@pre, values) *
          Int64Array::undef_full(out@pre, n@pre) *
          Int64Array::seg(coef@pre, 0, d, coefficients) *
          Int64Array::undef_seg(coef@pre, d, n@pre)
    */
    for (int d = 1; d < n; d++)           /* C(k-1+d, d) from C(k-1+d-1, d-1) */
        /*@ Assert
              exists (coefficients : list Z),
              a == a@pre && n == n@pre && k == k@pre &&
              out == out@pre && coef == coef@pre &&
              1 <= k@pre && k@pre <= 1000000000 &&
              1 <= n@pre && n@pre <= 2000 &&
              n@pre == Zlength(values) &&
              (forall q, (0 <= q && q < n@pre) =>
                 (0 <= values[q] && values[q] <= 1000000000)) &&
              1 <= d && d < n@pre && Zlength(coefficients) == d &&
              (forall q, (0 <= q && q < d) =>
                 (0 <= coefficients[q] && coefficients[q] < 1000000007)) &&
              CoefficientPrefix(k@pre, coefficients) &&
              Int64Array::full(a@pre, n@pre, values) *
              Int64Array::undef_full(out@pre, n@pre) *
              Int64Array::seg(coef@pre, 0, d, coefficients) *
              Int64Array::undef_seg(coef@pre, d, n@pre)
        */
        coef[d] = coef[d - 1] % MOD * ((k - 1 + d) % MOD) % MOD
                  * power(d, MOD - 2) % MOD;
    /*@ Inv Assert
          exists (coefficients : list Z) (written : list Z),
          a == a@pre && n == n@pre && k == k@pre &&
          out == out@pre && coef == coef@pre &&
          1 <= k@pre && k@pre <= 1000000000 &&
          1 <= n@pre && n@pre <= 2000 &&
          n@pre == Zlength(values) &&
          (forall q, (0 <= q && q < n@pre) =>
             (0 <= values[q] && values[q] <= 1000000000)) &&
          Zlength(coefficients) == n@pre &&
          (forall q, (0 <= q && q < n@pre) =>
             (0 <= coefficients[q] && coefficients[q] < 1000000007)) &&
          CoefficientPrefix(k@pre, coefficients) &&
          0 <= i && i <= n@pre && Zlength(written) == i &&
          ConvolutionPrefix(values, coefficients, written) &&
          Int64Array::full(a@pre, n@pre, values) *
          Int64Array::full(coef@pre, n@pre, coefficients) *
          Int64Array::seg(out@pre, 0, i, written) *
          Int64Array::undef_seg(out@pre, i, n@pre)
    */
    for (int i = 0; i < n; i++) {
        long long s = 0;
        /*@ Inv Assert
              exists (coefficients : list Z) (written : list Z),
              a == a@pre && n == n@pre && k == k@pre &&
              out == out@pre && coef == coef@pre &&
              1 <= k@pre && k@pre <= 1000000000 &&
              1 <= n@pre && n@pre <= 2000 &&
              n@pre == Zlength(values) &&
              (forall q, (0 <= q && q < n@pre) =>
                 (0 <= values[q] && values[q] <= 1000000000)) &&
              Zlength(coefficients) == n@pre &&
              (forall q, (0 <= q && q < n@pre) =>
                 (0 <= coefficients[q] && coefficients[q] < 1000000007)) &&
              CoefficientPrefix(k@pre, coefficients) &&
              0 <= i && i < n@pre && Zlength(written) == i &&
              ConvolutionPrefix(values, coefficients, written) &&
              0 <= j && j <= i + 1 &&
              0 <= s && s < 1000000007 &&
              ConvolutionAccumulator(values, coefficients, i, j, s) &&
              Int64Array::full(a@pre, n@pre, values) *
              Int64Array::full(coef@pre, n@pre, coefficients) *
              Int64Array::seg(out@pre, 0, i, written) *
              Int64Array::undef_seg(out@pre, i, n@pre)
        */
        for (int j = 0; j <= i; j++)
            s = (s + coef[i - j] * (a[j] % MOD)) % MOD;
        out[i] = s;
    }
}

// int main(void)
// {
//     int n;
//     long long k;
//     if (scanf("%d %lld", &n, &k) != 2)
//         return 0;
//     static long long a[2005], out[2005], coef[2005];
//     for (int i = 0; i < n; i++)
//         scanf("%lld", &a[i]);
//     solver(a, n, k, out, coef);
//     for (int i = 0; i < n; i++)
//         printf("%lld%c", out[i], i + 1 == n ? '\n' : ' ');
//     return 0;
// }
