/*
 * Codeforces 938/E - Max History  (rating 2300, COMBINATORICS)
 *
 * An element v is added to f exactly when it becomes the running maximum and
 * is later beaten.  It becomes the running maximum iff it appears before every
 * element >= v (ties block it too), which happens in n!/g of the permutations,
 * where g counts the elements >= v.  It is beaten iff some element is strictly
 * greater.  So the answer is the sum of v * n!/g over the elements that have a
 * strictly larger one.
 */

// #include <stdio.h>
// #include <stdlib.h>

/* QCP_INSERT_BEGIN:shard09-P083-solver-support */
/*@ Import Coq Require Import AUXLib.MonotonicList */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P083_938E_max_history_lib */
/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
      (Spec : list Z -> Z -> Prop)
      (mono_nondec : list Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P083-solver-support */

/*@ Extern Coq
      (ModPower : Z -> Z -> Z -> Prop)
*/

/*@ Extern Coq
      (PowerLoopState : Z -> Z -> Z -> Z -> Z -> Prop)
      (FactorialModState : Z -> Z -> Prop)
      (GroupBoundary : list Z -> Z -> Prop)
      (ContribPrefixSum : list Z -> Z -> Z -> Prop)
*/

#define MOD 1000000007LL

// static int cmp_int(const void *a, const void *b)
// {
//     int x = *(const int *)a, y = *(const int *)b;
//     return (x > y) - (x < y);
// }

void quicksort(int *arr, int n)
/*@ With (l : list Z)
    Require
      0 <= n && n <= 1000000 &&
      IntArray::full(arr, n, l)
    Ensure
      exists l1,
        Permutation(l, l1) &&
        mono_nondec(l1) &&
        IntArray::full(arr, n, l1)
*/
;

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

/* solver: sum of f over all n! permutations, modulo 1e9+7.  Sorts a[]. */
static long long solver(int *a, int n)
/* QCP_INSERT_BEGIN:shard09-P083-solver-contract */
/*@ With (values : list Z)
    Require
      1 <= n && n <= 1000000 && (forall i, (0 <= i && i < n) => (1 <= values[i] && values[i] <= 1000000000)) &&
      n == Zlength(values) && IntArray::full(a, n, values)
    Ensure
      Spec(values, __return) &&
      exists (a_after : list Z), Permutation(values, a_after) && IntArray::full(a, n, a_after)
*/
/* QCP_INSERT_END:shard09-P083-solver-contract */
{
    // qsort(a, n, sizeof *a, cmp_int);
    quicksort(a, n) /*@ where l = values */;
    /*@ Assert
          exists (l1 : list Z),
            a == a@pre && n == n@pre &&
            1 <= n@pre && n@pre <= 1000000 &&
            n@pre == Zlength(values) &&
            Zlength(l1) == n@pre &&
            (forall q, (0 <= q && q < n@pre) =>
               (1 <= l1[q] && l1[q] <= 1000000000)) &&
            Permutation(values, l1) && mono_nondec(l1) &&
            IntArray::full(a@pre, n@pre, l1)
    */
    long long fact = 1;
    /*@ Inv Assert
          exists (l1 : list Z),
            a == a@pre && n == n@pre &&
            1 <= n@pre && n@pre <= 1000000 &&
            n@pre == Zlength(values) &&
            Zlength(l1) == n@pre &&
            (forall q, (0 <= q && q < n@pre) =>
               (1 <= l1[q] && l1[q] <= 1000000000)) &&
            Permutation(values, l1) && mono_nondec(l1) &&
            2 <= i && i <= n@pre + 1 &&
            0 <= fact && fact < 1000000007 &&
            FactorialModState(i, fact) &&
            IntArray::full(a@pre, n@pre, l1)
    */
    for (int i = 2; i <= n; i++)
        fact = fact * i % MOD;
    long long total = 0;
    /*@ Inv Assert
          exists (l1 : list Z),
            a == a@pre && n == n@pre &&
            1 <= n@pre && n@pre <= 1000000 &&
            n@pre == Zlength(values) &&
            Zlength(l1) == n@pre &&
            (forall q, (0 <= q && q < n@pre) =>
               (1 <= l1[q] && l1[q] <= 1000000000)) &&
            Permutation(values, l1) && mono_nondec(l1) &&
            0 <= i && i <= n@pre &&
            0 <= fact && fact < 1000000007 &&
            FactorialModState(n@pre + 1, fact) &&
            0 <= total && total < 1000000007 &&
            GroupBoundary(l1, i) &&
            ContribPrefixSum(l1, i, total) &&
            IntArray::full(a@pre, n@pre, l1)
    */
    for (int i = 0; i < n; i++) {
        int j = i;
        /*@ Inv Assert
              exists (l1 : list Z),
                a == a@pre && n == n@pre &&
                1 <= n@pre && n@pre <= 1000000 &&
                n@pre == Zlength(values) &&
                Zlength(l1) == n@pre &&
                (forall q, (0 <= q && q < n@pre) =>
                   (1 <= l1[q] && l1[q] <= 1000000000)) &&
                Permutation(values, l1) && mono_nondec(l1) &&
                0 <= i && i < n@pre &&
                i <= j && j <= n@pre &&
                (forall q, (i <= q && q < j) => (l1[q] == l1[i])) &&
                0 <= fact && fact < 1000000007 &&
                FactorialModState(n@pre + 1, fact) &&
                0 <= total && total < 1000000007 &&
                GroupBoundary(l1, i) &&
                ContribPrefixSum(l1, i, total) &&
                IntArray::full(a@pre, n@pre, l1)
        */
        while (j < n && a[j] == a[i])
            j++;
        if (j < n) {                      /* something strictly larger exists */
            long long g = n - i;          /* elements >= a[i] */
            long long share = fact % MOD * power(g % MOD, MOD - 2) % MOD;
            long long cnt = j - i;
            total = (total + cnt % MOD * (a[i] % MOD) % MOD * share) % MOD;
        }
        i = j - 1;
    }
    return total;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static int a[1000006];
//     for (int i = 0; i < n; i++)
//         scanf("%d", &a[i]);
//     printf("%lld\n", solver(a, n));
//     return 0;
// }
