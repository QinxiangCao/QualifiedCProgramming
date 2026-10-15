/*
 * Codeforces 215/A - Bicycle Chain  (rating 900, BRUTE FORCE)
 *
 * n, m <= 50, so scan all pairs, keep the largest integer ratio and count how
 * often it occurs.
 *
 * solver() takes the whole input (both star lists) and returns the count.
 */

// #include <stdio.h>
/* QCP_INSERT_BEGIN:shard03-P010-solver-support */

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard03.P010_215A_bicycle_chain_lib */
/*@ Extern Coq
      (Pre : list Z -> list Z -> Prop)
      (Spec : list Z -> list Z -> Z -> Prop)
*/

/* QCP_INSERT_END:shard03-P010-solver-support */

/* solver: pure.  Number of gears attaining the maximum integer ratio. */
static int solver(const int *a, int n, const int *b, int m)
/* QCP_INSERT_BEGIN:shard03-P010-solver-contract */
/*@ With (av : list Z) (bv : list Z)
    Require
      Pre(av, bv) &&
      1 <= n && n <= 50 && 1 <= m && m <= 50 &&
      n == Zlength(av) && m == Zlength(bv) &&
      (forall i, (0 <= i && i < n) => (1 <= av[i] && av[i] <= 10000)) &&
      (forall j, (0 <= j && j < m) => (1 <= bv[j] && bv[j] <= 10000)) &&
      IntArray::full(a, n, av) * IntArray::full(b, m, bv)
    Ensure
      Spec(av, bv, __return) &&
      IntArray::full(a, n, av) * IntArray::full(b, m, bv)
*/
/* QCP_INSERT_END:shard03-P010-solver-contract */
{
    int best = 0, cnt = 0;
    for (int i = 0; i < n; i++)
        for (int j = 0; j < m; j++) {
            if (b[j] % a[i])
                continue;
            int ratio = b[j] / a[i];
            if (ratio > best) {
                best = ratio;
                cnt = 1;
            } else if (ratio == best) {
                cnt++;
            }
        }
    return cnt;
}

// int main(void)
// {
//     int n, m;
//     static int a[55], b[55];
//     if (scanf("%d", &n) != 1)
//         return 0;
//     for (int i = 0; i < n; i++)
//         scanf("%d", &a[i]);
//     scanf("%d", &m);
//     for (int j = 0; j < m; j++)
//         scanf("%d", &b[j]);
//     printf("%d\n", solver(a, n, b, m));
//     return 0;
// }
