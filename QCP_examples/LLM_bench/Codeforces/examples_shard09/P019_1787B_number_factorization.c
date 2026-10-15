/*
 * Codeforces 1787/B - Number Factorization  (rating 1100, NUMBER THEORY)
 *
 * Each a_i must be squarefree, so writing n = prod q_j^{e_j} the factors split
 * into "layers": layer k (for k = 1 .. max e_j) may use every prime whose
 * exponent is at least k.  Multiplying a whole layer into one a_i with p_i = 1
 * beats splitting it, since for primes u,v the product u*v >= u + v when
 * u,v >= 2.  So the answer is the sum over layers of the layer's product.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : Z -> Z -> Prop)
*/
/*@ Extern Coq
      (FactorScan : Z -> Z -> Z -> list Z -> list Z -> Prop)
      (FactorExtract : Z -> Z -> Z -> list Z -> list Z -> Z -> Prop)
      (PrimeFactorization : Z -> list Z -> list Z -> Prop)
      (PrefixMaximum : list Z -> Z -> Z -> Prop)
      (MaximumExponent : list Z -> Z -> Prop)
      (LayerProductPrefix : Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (LayerSumPrefix : Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (FactorizationAnswer : Z -> list Z -> list Z -> Z -> Prop)
*/
/*@ Extern Coq
      (ExtractionScale : Z -> Z -> Z -> Prop)
*/
/*@ Extern Coq
      (LayerOptimalityCertificate : Z -> list Z -> list Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P019_1787B_number_factorization_lib */

/* solver: pure.  Maximum of sum a_i * p_i over valid factorisations of n. */
static long long solver(long long n)
/* QCP_INSERT_BEGIN:shard09-P019-solver-contract */
/*@
    Require
      2 <= n && n <= 1000000000 &&
      emp
    Ensure
      Spec(n@pre, __return) &&
      emp
*/
/* QCP_INSERT_END:shard09-P019-solver-contract */
{
    long long pr[40], ex[40];
    int m = 0;
    /*@ Inv Assert
          exists (ps : list Z) (es : list Z),
          2 <= n@pre && n@pre <= 1000000000 &&
          1 <= n && n <= n@pre &&
          2 <= d && d <= n@pre &&
          d * d <= 1000000000000000000 &&
          0 <= m && m <= 29 &&
          Zlength(ps) == m && Zlength(es) == m &&
          FactorScan(n@pre, n, d, ps, es) &&
          Int64Array::seg(pr, 0, m, ps) *
          Int64Array::undef_seg(pr, m, 40) *
          Int64Array::seg(ex, 0, m, es) *
          Int64Array::undef_seg(ex, m, 40)
     */
    for (long long d = 2; d * d <= n; d++)
        if (n % d == 0) {
            pr[m] = d;
            ex[m] = 0;
            /*@ Inv Assert
                  exists (ps : list Z) (es : list Z) (e : Z),
                  2 <= n@pre && n@pre <= 1000000000 &&
                  1 <= n && n <= n@pre &&
                  2 <= d && d <= n@pre &&
                  0 <= m && m <= 29 &&
                  Zlength(ps) == m && Zlength(es) == m &&
                  ExtractionScale(n, d, e) &&
                  FactorExtract(n@pre, n, d, ps, es, e) &&
                  Int64Array::seg(pr, 0, m + 1, app(ps, cons(d, nil))) *
                  Int64Array::undef_seg(pr, m + 1, 40) *
                  Int64Array::seg(ex, 0, m + 1, app(es, cons(e, nil))) *
                  Int64Array::undef_seg(ex, m + 1, 40)
             */
            while (n % d == 0) {
                n /= d;
                ex[m]++;
            }
            m++;
        }
    if (n > 1) {
        pr[m] = n;
        ex[m] = 1;
        m++;
    }
    /*@ Assert
          exists (ps : list Z) (es : list Z),
          2 <= n@pre && n@pre <= 1000000000 &&
          1 <= n && n <= n@pre &&
          1 <= m && m <= 30 &&
          Zlength(ps) == m && Zlength(es) == m &&
          PrimeFactorization(n@pre, ps, es) &&
          Int64Array::seg(pr, 0, m, ps) *
          Int64Array::undef_seg(pr, m, 40) *
          Int64Array::seg(ex, 0, m, es) *
          Int64Array::undef_seg(ex, m, 40)
     */
    long long maxe = 0;
    /*@ Inv Assert
          exists (ps : list Z) (es : list Z),
          2 <= n@pre && n@pre <= 1000000000 &&
          1 <= n && n <= n@pre &&
          1 <= m && m <= 30 &&
          Zlength(ps) == m && Zlength(es) == m &&
          0 <= i && i <= m &&
          PrefixMaximum(es, i, maxe) &&
          PrimeFactorization(n@pre, ps, es) &&
          Int64Array::seg(pr, 0, m, ps) *
          Int64Array::undef_seg(pr, m, 40) *
          Int64Array::seg(ex, 0, m, es) *
          Int64Array::undef_seg(ex, m, 40)
     */
    for (int i = 0; i < m; i++)
        if (ex[i] > maxe)
            maxe = ex[i];
    long long total = 0;
    /*@ Inv Assert
          exists (ps : list Z) (es : list Z),
          2 <= n@pre && n@pre <= 1000000000 &&
          1 <= n && n <= n@pre &&
          1 <= m && m <= 30 &&
          Zlength(ps) == m && Zlength(es) == m &&
          1 <= maxe && maxe <= 30 &&
          1 <= k && k <= maxe + 1 &&
          MaximumExponent(es, maxe) &&
          LayerOptimalityCertificate(n@pre, ps, es, maxe) &&
          LayerSumPrefix(n@pre, ps, es, maxe, k, total) &&
          Int64Array::seg(pr, 0, m, ps) *
          Int64Array::undef_seg(pr, m, 40) *
          Int64Array::seg(ex, 0, m, es) *
          Int64Array::undef_seg(ex, m, 40)
     */
    for (long long k = 1; k <= maxe; k++) {
        long long prod = 1;
        /*@ Inv Assert
              exists (ps : list Z) (es : list Z),
              2 <= n@pre && n@pre <= 1000000000 &&
              1 <= n && n <= n@pre &&
              1 <= m && m <= 30 &&
              Zlength(ps) == m && Zlength(es) == m &&
              1 <= maxe && maxe <= 30 &&
              1 <= k && k <= maxe &&
              0 <= i && i <= m &&
              MaximumExponent(es, maxe) &&
              LayerOptimalityCertificate(n@pre, ps, es, maxe) &&
              LayerSumPrefix(n@pre, ps, es, maxe, k, total) &&
              LayerProductPrefix(n@pre, ps, es, k, i, prod) &&
              Int64Array::seg(pr, 0, m, ps) *
              Int64Array::undef_seg(pr, m, 40) *
              Int64Array::seg(ex, 0, m, es) *
              Int64Array::undef_seg(ex, m, 40)
         */
        for (int i = 0; i < m; i++)
            if (ex[i] >= k)
                prod *= pr[i];
        total += prod;
    }
    /*@ Assert
          exists (ps : list Z) (es : list Z),
          1 <= n && n <= n@pre &&
          1 <= m && m <= 30 &&
          Zlength(ps) == m && Zlength(es) == m &&
          1 <= maxe && maxe <= 30 &&
          MaximumExponent(es, maxe) &&
          LayerOptimalityCertificate(n@pre, ps, es, maxe) &&
          LayerSumPrefix(n@pre, ps, es, maxe, maxe + 1, total) &&
          FactorizationAnswer(n@pre, ps, es, total) &&
          Int64Array::undef_full(pr, 40) *
          Int64Array::undef_full(ex, 40)
     */
    return total;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         long long n;
//         scanf("%lld", &n);
//         printf("%lld\n", solver(n));
//     }
//     return 0;
// }
