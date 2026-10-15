/*
 * Codeforces 1656/A - Good Pairs  (rating 800, MATH)
 *
 * |a_i - a_k| + |a_k - a_j| = |a_i - a_j| says a_k lies between a_i and a_j,
 * so taking the smallest and the largest element makes it hold for every k.
 *
 * solver() takes one whole test case and writes both indices of the pair.
 */

// #include <stdio.h>
/* QCP_INSERT_BEGIN:shard03-P003-solver-support */

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard03.P003_1656A_good_pairs_lib */
/*@ Extern Coq
      (Spec : list Z -> Z -> Z -> Prop)
*/

/* QCP_INSERT_END:shard03-P003-solver-support */

/* solver: pure.  Writes 1-based indices of a good pair into *pi and *pj. */
static void solver(const int *a, int n, int *pi, int *pj)
/* QCP_INSERT_BEGIN:shard03-P003-solver-contract */
/*@ With (arr : list Z)
    Require
      1 <= n && n <= 100000 && n == Zlength(arr) &&
      (forall k, (0 <= k && k < n) => (1 <= arr[k] && arr[k] <= 1000000000)) &&
      IntArray::full(a, n, arr) * has_permission(pi, int) * has_permission(pj, int)
    Ensure
      exists (i : Z) (j : Z),
        Spec(arr, i, j) &&
        IntArray::full(a, n, arr) * store(pi, int, i) * store(pj, int, j)
*/
/* QCP_INSERT_END:shard03-P003-solver-contract */
{
    int lo = 0, hi = 0;
    for (int k = 1; k < n; k++) {
        if (a[k] < a[lo])
            lo = k;
        if (a[k] > a[hi])
            hi = k;
    }
    *pi = lo + 1;
    *pj = hi + 1;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static int a[100005];
//     while (t--) {
//         int n, i, j;
//         scanf("%d", &n);
//         for (int k = 0; k < n; k++)
//             scanf("%d", &a[k]);
//         solver(a, n, &i, &j);
//         printf("%d %d\n", i, j);
//     }
//     return 0;
// }
