/*
 * Codeforces 623/B - Array GCD  (rating 2300, DP)
 *
 * The removed segment cannot be the whole array, so a_1 or a_n survives, and
 * a surviving element is only changed by at most 1: every useful gcd divides
 * one of a_1-1, a_1, a_1+1, a_n-1, a_n, a_n+1.  For each prime factor p of
 * those six numbers, a three-state sweep (before the cut, inside it, after it)
 * gives the cheapest plan.
 */

// #include <stdio.h>

/* QCP_INSERT_BEGIN:shard09-P082-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P082_623B_array_gcd_lib */
/*@ Extern Coq
      (Spec : Z -> Z -> list Z -> Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P082-solver-support */

/*@ Extern Coq
      (CostForPrime : list Z -> Z -> Z -> Z -> Z -> Prop)
      (AddFactorsResult : Z -> list Z -> Prop)
*/

/*@ Extern Coq
      (ElemCost : Z -> Z -> Z -> Z)
      (CostForPrimeState : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (AddFactorsScan : Z -> Z -> Z -> list Z -> Prop)
      (AddFactorsExtract : Z -> Z -> Z -> list Z -> Prop)
      (AddFactorsResidual : Z -> Z -> list Z -> Prop)
      (CandidateCoverage : Z -> Z -> Z -> list Z -> Prop)
      (BestPrefixCost : list Z -> Z -> Z -> list Z -> Z -> Z -> Prop)
      (Z::min : Z -> Z -> Z)
      (Z::max : Z -> Z -> Z)
*/

#define INF (1LL << 62)

static void add_factors(long long v, long long *primes, int *nprime)
/*@ With (v0 : Z) (k0 : Z) (pre : list Z)
    Require
      v == v0 && 1 <= v0 && v0 <= 1000000001 &&
      0 <= k0 && k0 <= 200 && Zlength(pre) == k0 &&
      store(nprime, int, k0) *
      Int64Array::seg(primes, 0, k0, pre) *
      Int64Array::seg_shape(primes, k0, 256)
    Ensure
      exists fs,
        AddFactorsResult(v0, fs) &&
        0 <= Zlength(fs) && Zlength(fs) <= 30 &&
        store(nprime, int, k0 + Zlength(fs)) *
        Int64Array::seg(primes, 0, k0 + Zlength(fs), app(pre, fs)) *
        Int64Array::seg_shape(primes, k0 + Zlength(fs), 256)
 */
{
    /*@ 0 <= k0 && k0 <= 200 && Zlength(pre) == k0 &&
        Int64Array::seg(primes, 0, k0, pre) *
        Int64Array::seg_shape(primes, k0, 256)
        which implies
        exists (all : list Z),
          Zlength(all) == 256 &&
          sublist(0, k0, all) == pre &&
          Int64Array::full(primes, 256, all)
     */
    /*@ Inv Assert
          exists (fs : list Z) (all : list Z),
            primes == primes@pre && nprime == nprime@pre &&
            1 <= v0 && v0 <= 1000000001 &&
            1 <= v && v <= v0 &&
            2 <= d && d <= 31624 &&
            0 <= k0 && k0 <= 200 && Zlength(pre) == k0 &&
            0 <= Zlength(fs) && Zlength(fs) <= 29 &&
            Zlength(all) == 256 &&
            sublist(0, k0 + Zlength(fs), all) == app(pre, fs) &&
            AddFactorsScan(v0, v, d, fs) &&
            store(nprime@pre, int, k0 + Zlength(fs)) *
            Int64Array::full(primes@pre, 256, all)
     */
    for (long long d = 2; d * d <= v; d++)
        if (v % d == 0) {
            { primes[(*nprime)] = d; (*nprime)++; }
            /*@ Inv Assert
                  exists (fs : list Z) (all : list Z),
                    primes == primes@pre && nprime == nprime@pre &&
                    1 <= v0 && v0 <= 1000000001 &&
                    1 <= v && v <= v0 &&
                    2 <= d && d <= 31624 && d * d <= v0 &&
                    0 <= k0 && k0 <= 200 && Zlength(pre) == k0 &&
                    1 <= Zlength(fs) && Zlength(fs) <= 30 &&
                    Zlength(all) == 256 &&
                    sublist(0, k0 + Zlength(fs), all) == app(pre, fs) &&
                    AddFactorsExtract(v0, v, d, fs) &&
                    (v % d == 0 || AddFactorsScan(v0, v, d, fs)) &&
                    store(nprime@pre, int, k0 + Zlength(fs)) *
                    Int64Array::full(primes@pre, 256, all)
             */
            while (v % d == 0)
                v /= d;
        }
    /*@ Assert
          exists (fs : list Z) (all : list Z),
            primes == primes@pre && nprime == nprime@pre &&
            1 <= v0 && v0 <= 1000000001 &&
            1 <= v && v <= v0 &&
            0 <= k0 && k0 <= 200 && Zlength(pre) == k0 &&
            0 <= Zlength(fs) && Zlength(fs) <= 29 &&
            Zlength(all) == 256 &&
            sublist(0, k0 + Zlength(fs), all) == app(pre, fs) &&
            AddFactorsResidual(v0, v, fs) &&
            store(nprime@pre, int, k0 + Zlength(fs)) *
            Int64Array::full(primes@pre, 256, all)
     */
    if (v > 1)
        { primes[(*nprime)] = v; (*nprime)++; }
    /*@ exists (all : list Z) (m : Z),
          0 <= m && m <= 256 && Zlength(all) == 256 &&
          store(nprime, int, m) *
          Int64Array::full(primes, 256, all)
        which implies
          store(nprime, int, m) *
          Int64Array::seg(primes, 0, m, sublist(0, m, all)) *
          Int64Array::seg_shape(primes, m, 256)
     */
}

/* solver: cheapest plan for the fixed prime p, or INF if impossible. */
static long long cost_for_prime(const int *arr, int n, long long a,
                                long long b, long long p)
/*@ With (values : list Z)
    Require
      0 <= a && a <= 1000000000 && 0 <= b && b <= 1000000000 &&
      1 <= n && n <= 1000000 && n == Zlength(values) &&
      (forall i, (0 <= i && i < n) => (2 <= values[i] && values[i] <= 1000000000)) &&
      2 <= p &&
      IntArray::full(arr, n, values)
    Ensure
      CostForPrime(values, a, b, p, __return) &&
      ((0 <= __return && __return <= 2000000000000000) ||
       __return == 4611686018427387904) &&
      IntArray::full(arr, n, values)
 */
{
    long long keep = 0, cutFresh = 0, cutAfterKeep = INF, after = INF;
    /* keep         : no cut yet, everything so far kept
     * cutFresh     : inside a cut that started at index 0
     * cutAfterKeep : inside a cut with at least one kept element before it
     * after        : the cut is finished, later elements are kept  */
    /*@ Inv Assert
          arr == arr@pre && n == n@pre && a == a@pre && b == b@pre && p == p@pre &&
          0 <= a@pre && a@pre <= 1000000000 &&
          0 <= b@pre && b@pre <= 1000000000 &&
          1 <= n@pre && n@pre <= 1000000 && n@pre == Zlength(values) &&
          (forall j, (0 <= j && j < n@pre) =>
             (2 <= values[j] && values[j] <= 1000000000)) &&
          2 <= p@pre &&
          0 <= i && i <= n@pre &&
          0 <= keep && keep <= 4611686018427387904 &&
          0 <= cutFresh && cutFresh <= 4611686018427387904 &&
          0 <= cutAfterKeep && cutAfterKeep <= 4611686018427387904 &&
          0 <= after && after <= 4611686018427387904 &&
          CostForPrimeState(values, a@pre, b@pre, p@pre, i,
                            keep, cutFresh, cutAfterKeep, after) &&
          IntArray::full(arr@pre, n@pre, values)
     */
    for (int i = 0; i < n; i++) {
        long long v = arr[i];
        long long cost;
        if (v % p == 0)
            cost = 0;
        else if ((v - 1) % p == 0 || (v + 1) % p == 0)
            cost = b;
        else
            cost = INF;
        /*@ Branch join all with Assert
          arr == arr@pre && n == n@pre && a == a@pre && b == b@pre && p == p@pre &&
          0 <= a@pre && a@pre <= 1000000000 &&
          0 <= b@pre && b@pre <= 1000000000 &&
          1 <= n@pre && n@pre <= 1000000 && n@pre == Zlength(values) &&
          (forall j, (0 <= j && j < n@pre) =>
             (2 <= values[j] && values[j] <= 1000000000)) &&
          2 <= p@pre &&
          0 <= i && i < n@pre &&
          v == values[i] && 2 <= v && v <= 1000000000 &&
          cost == ElemCost(b@pre, p@pre, v) &&
          0 <= cost && cost <= 4611686018427387904 &&
          0 <= keep && keep <= 4611686018427387904 &&
          0 <= cutFresh && cutFresh <= 4611686018427387904 &&
          0 <= cutAfterKeep && cutAfterKeep <= 4611686018427387904 &&
          0 <= after && after <= 4611686018427387904 &&
          CostForPrimeState(values, a@pre, b@pre, p@pre, i,
                            keep, cutFresh, cutAfterKeep, after) &&
          IntArray::full(arr@pre, n@pre, values)
         */

        long long nkeep;
        if (keep == INF || cost == INF)
            nkeep = INF;
        else
            nkeep = keep + cost;
        /*@ Branch join all with nkeep == Z::min(INF, keep + cost) */
        long long ncutFresh;
        if (cutFresh == INF)
            ncutFresh = INF;
        else
            ncutFresh = cutFresh + a;
        /*@ Branch join all with
              ncutFresh == Z::min(INF, cutFresh + a)
         */
        long long from = keep;             /* start a cut after kept elements */
        long long ncutAfterKeep = INF;
        if (i > 0 && from != INF)
            ncutAfterKeep = from + a;
        if (cutAfterKeep != INF && cutAfterKeep + a < ncutAfterKeep)
            ncutAfterKeep = cutAfterKeep + a;
        /*@ Branch join all with
              ncutAfterKeep ==
                Z::min(INF,
                  Z::min(cutAfterKeep + a,
                    Z::max(keep + a, INF - i * INF)))
         */
        long long best_prev_cut;
        if (cutFresh < cutAfterKeep)
            best_prev_cut = cutFresh;
        else
            best_prev_cut = cutAfterKeep;
        /*@ Branch join all with
              best_prev_cut == Z::min(cutFresh, cutAfterKeep)
         */
        long long nafter = INF;
        if (cost != INF) {
            if (best_prev_cut != INF)
                nafter = best_prev_cut + cost;
            if (after != INF && after + cost < nafter)
                nafter = after + cost;
        }
        /*@ Branch join all with
              nafter ==
                Z::min(INF,
                  Z::min(best_prev_cut + cost, after + cost))
         */
        keep = nkeep;
        cutFresh = ncutFresh;
        cutAfterKeep = ncutAfterKeep;
        after = nafter;
    }
    long long best = keep;
    if (after < best) best = after;
    if (cutAfterKeep < best) best = cutAfterKeep;   /* cut runs to the end */
    /*@ Assert
          arr == arr@pre && n == n@pre && a == a@pre && b == b@pre && p == p@pre &&
          1 <= n@pre && n@pre <= 1000000 && n@pre == Zlength(values) &&
          0 <= keep && keep <= 4611686018427387904 &&
          0 <= cutFresh && cutFresh <= 4611686018427387904 &&
          0 <= cutAfterKeep && cutAfterKeep <= 4611686018427387904 &&
          0 <= after && after <= 4611686018427387904 &&
          ((0 <= best && best <= 2000000000000000) ||
           best == 4611686018427387904) &&
          CostForPrime(values, a@pre, b@pre, p@pre, best) &&
          IntArray::full(arr@pre, n@pre, values)
     */
    return best;
}

/* solver: complete case.  Enumerate every candidate prime internally. */
static long long solver(const int *arr, int n, long long a, long long b,
                        long long *primes)
/* QCP_INSERT_BEGIN:shard09-P082-normalized-solver-contract */
/*@ With (values : list Z)
    Require
      0 <= a && a <= 1000000000 && 0 <= b && b <= 1000000000 &&
      1 <= n && n <= 1000000 && (forall i, (0 <= i && i < n) => (2 <= values[i] && values[i] <= 1000000000)) && n == Zlength(values) && IntArray::full(arr, n, values) * Int64Array::full_shape(primes, 256)
    Ensure
      Spec(a, b, values, __return) && IntArray::full(arr, n, values) * Int64Array::full_shape(primes, 256)
*/
/* QCP_INSERT_END:shard09-P082-normalized-solver-contract */
{
    int nprime = 0;
    /*@ Inv Assert
          exists (ps : list Z),
            arr == arr@pre && n == n@pre && a == a@pre && b == b@pre &&
            primes == primes@pre &&
            0 <= a@pre && a@pre <= 1000000000 &&
            0 <= b@pre && b@pre <= 1000000000 &&
            1 <= n@pre && n@pre <= 1000000 && n@pre == Zlength(values) &&
            (forall j, (0 <= j && j < n@pre) =>
               (2 <= values[j] && values[j] <= 1000000000)) &&
            -1 <= d && d <= 2 &&
            0 <= nprime && nprime <= 60 * (d + 1) &&
            Zlength(ps) == nprime &&
            CandidateCoverage(values[0], values[n@pre - 1], d, ps) &&
            IntArray::full(arr@pre, n@pre, values) *
            Int64Array::seg(primes@pre, 0, nprime, ps) *
            Int64Array::seg_shape(primes@pre, nprime, 256)
     */
    for (int d = -1; d <= 1; d++) {
        add_factors(arr[0] + d, primes, &nprime);
        add_factors(arr[n - 1] + d, primes, &nprime);
    }
    long long best = INF;
    /*@ Inv Assert
          exists (ps : list Z),
            arr == arr@pre && n == n@pre && a == a@pre && b == b@pre &&
            primes == primes@pre &&
            0 <= a@pre && a@pre <= 1000000000 &&
            0 <= b@pre && b@pre <= 1000000000 &&
            1 <= n@pre && n@pre <= 1000000 && n@pre == Zlength(values) &&
            (forall j, (0 <= j && j < n@pre) =>
               (2 <= values[j] && values[j] <= 1000000000)) &&
            0 <= i && i <= nprime &&
            0 <= nprime && nprime <= 180 &&
            Zlength(ps) == nprime &&
            (forall j, (0 <= j && j < nprime) => (2 <= ps[j])) &&
            CandidateCoverage(values[0], values[n@pre - 1], 2, ps) &&
            0 <= best && best <= 4611686018427387904 &&
            BestPrefixCost(values, a@pre, b@pre, ps, i, best) &&
            IntArray::full(arr@pre, n@pre, values) *
            Int64Array::seg(primes@pre, 0, nprime, ps) *
            Int64Array::seg_shape(primes@pre, nprime, 256)
     */
    for (int i = 0; i < nprime; i++) {
        long long r = cost_for_prime(arr, n, a, b, primes[i]);
        if (r < best)
            best = r;
    }
    /*@ exists (ps : list Z),
          0 <= nprime && nprime <= 256 &&
          Int64Array::seg(primes, 0, nprime, ps) *
          Int64Array::seg_shape(primes, nprime, 256)
        which implies
          0 <= nprime && nprime <= 256 &&
          Int64Array::full_shape(primes, 256)
     */
    /*@ Assert
          arr == arr@pre && n == n@pre && a == a@pre && b == b@pre &&
          primes == primes@pre &&
          1 <= n@pre && n@pre <= 1000000 && n@pre == Zlength(values) &&
          0 <= nprime && nprime <= 180 &&
          Spec(a@pre, b@pre, values, best) &&
          IntArray::full(arr@pre, n@pre, values) *
          Int64Array::full_shape(primes@pre, 256)
     */
    return best;
}

// int main(void)
// {
//     int n;
//     long long a, b;
//     if (scanf("%d %lld %lld", &n, &a, &b) != 3)
//         return 0;
//     static int arr[1000006];
//     for (int i = 0; i < n; i++)
//         scanf("%d", &arr[i]);
//     static long long primes[256];
//     printf("%lld\n", solver(arr, n, a, b, primes));
//     return 0;
// }
