/*
 * Codeforces 26/A - Almost Prime  (rating 900, NUMBER THEORY)
 *
 * A sieve counts, for every value up to n, how many distinct primes divide it;
 * the answer is how many of them have exactly two.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : Z -> Z -> Prop)
      (AlmostPrime : Z -> Prop)
      (In : Z -> list Z -> Prop)
      (NoDup : list Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P008_26A_almost_prime_lib */

#define MAXN 3005

/* solver: pure.  Count of almost primes (exactly 2 distinct prime divisors)
 * in [1, n]. */
static int solver(int n)
/* QCP_INSERT_BEGIN:shard09-P008-solver-contract */
/*@
    Require
      1 <= n && n <= 3000 &&
      emp
    Ensure
      Spec(n, __return) &&
      emp
*/
/* QCP_INSERT_END:shard09-P008-solver-contract */
{
    int ndiv[MAXN] = {0};
    /*@ Inv Assert
          exists counts,
          n == n@pre &&
          1 <= n@pre && n@pre <= 3000 &&
          2 <= p && p <= n@pre + 1 &&
          Zlength(counts) == 3005 &&
          (forall x,
            (1 <= x && x <= n@pre) =>
              (0 <= counts[x] && counts[x] <= p - 2 &&
               exists (ps : list Z),
                 Zlength(ps) == counts[x] &&
                 NoDup(ps) &&
                 (forall q,
                   In(q, ps) =>
                     (2 <= q && q < p &&
                      (forall a b,
                        (2 <= a && q == a * b) => q <= a) &&
                      exists k, 1 <= k && x == q * k)) &&
                 (forall q,
                   (2 <= q && q < p &&
                    (forall a b,
                      (2 <= a && q == a * b) => q <= a) &&
                    (exists k, 1 <= k && x == q * k)) =>
                     In(q, ps)))) &&
          IntArray::full(ndiv, 3005, counts)
     */
    for (int p = 2; p <= n; p++)
        if (ndiv[p] == 0)                 /* p is prime */
            /*@ Inv Assert
                  exists counts t,
                  n == n@pre &&
                  1 <= n@pre && n@pre <= 3000 &&
                  2 <= p && p <= n@pre &&
                  (forall a b,
                    (2 <= a && p == a * b) => p <= a) &&
                  p <= m && m <= n@pre + p &&
                  1 <= t && m == p * t &&
                  Zlength(counts) == 3005 &&
                  (forall x,
                    (1 <= x && x <= n@pre) =>
                      (0 <= counts[x] && counts[x] <= p - 1 &&
                       exists (ps : list Z),
                         Zlength(ps) == counts[x] &&
                         NoDup(ps) &&
                         (forall q,
                           In(q, ps) =>
                             (2 <= q &&
                              (forall a b,
                                (2 <= a && q == a * b) => q <= a) &&
                              (exists k, 1 <= k && x == q * k) &&
                              (q < p || (q == p && x < m)))) &&
                         (forall q,
                           (2 <= q &&
                            (forall a b,
                              (2 <= a && q == a * b) => q <= a) &&
                            (exists k, 1 <= k && x == q * k) &&
                            (q < p || (q == p && x < m))) =>
                              In(q, ps)))) &&
                  IntArray::full(ndiv, 3005, counts)
             */
            for (int m = p; m <= n; m += p)
                ndiv[m]++;
    /*@ Assert
          exists counts,
          n == n@pre &&
          1 <= n@pre && n@pre <= 3000 &&
          Zlength(counts) == 3005 &&
          (forall x,
            (1 <= x && x <= n@pre) =>
              (0 <= counts[x] && counts[x] <= n@pre - 1 &&
               ((counts[x] == 2 && AlmostPrime(x)) ||
                (counts[x] != 2 && (! AlmostPrime(x)))))) &&
          IntArray::full(ndiv, 3005, counts)
     */
    int cnt = 0;
    /*@ Inv Assert
          exists counts,
          n == n@pre &&
          1 <= n@pre && n@pre <= 3000 &&
          1 <= v && v <= n@pre + 1 &&
          0 <= cnt && cnt <= v - 1 &&
          Spec(v - 1, cnt) &&
          Zlength(counts) == 3005 &&
          (forall x,
            (1 <= x && x <= n@pre) =>
              (0 <= counts[x] && counts[x] <= n@pre - 1 &&
               ((counts[x] == 2 && AlmostPrime(x)) ||
                (counts[x] != 2 && (! AlmostPrime(x)))))) &&
          IntArray::full(ndiv, 3005, counts)
     */
    for (int v = 1; v <= n; v++)
        if (ndiv[v] == 2)
            cnt++;
    return cnt;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     printf("%d\n", solver(n));
//     return 0;
// }
