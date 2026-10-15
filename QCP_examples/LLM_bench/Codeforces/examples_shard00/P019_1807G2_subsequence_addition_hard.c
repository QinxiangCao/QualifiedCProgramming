/* Codeforces 1807/G2 - Subsequence Addition (Hard Version) */
// #include <stdio.h>
// #include <stdlib.h>

typedef unsigned long size_t;

static int cmp_int(const void *x, const void *y)
{
    int a = *(const int *)x, b = *(const int *)y;
    return (a > b) - (a < b);
}

/* QCP_INSERT_BEGIN:P019_1807G2_subsequence_addition_hard.support */
/*@ Extern Coq
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (Spec : list Z -> Z -> Prop)
*/
/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
      (increasing : list Z -> Prop)
      (PrefixAdditionState : list Z -> Z -> Z -> Prop)
      (FullDecisionSpecBridge : list Z -> list Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P019_1807G2_subsequence_addition_hard_lib */
/* QCP_INSERT_END:P019_1807G2_subsequence_addition_hard.support */

void qsort(int *base, size_t nmemb, size_t size,
           int (*compar)(const void *, const void *))
/*@ With (contents : list Z)
    Require
      nmemb == Zlength(contents) &&
      IntArray::full(base, nmemb, contents)
    Ensure
      exists sorted,
        Permutation(contents, sorted) &&
        increasing(sorted) &&
        Zlength(sorted) == nmemb &&
        FullDecisionSpecBridge(contents, sorted) &&
        IntArray::full(base, nmemb, sorted)
*/
;

static int solver(int *a, int n)/* QCP_INSERT_BEGIN:P019_1807G2_subsequence_addition_hard.contract */

/*@ With (input : list Z)
    Require
      n == Zlength(input) &&
      1 <= Zlength(input) && Zlength(input) <= 200000 &&
      (forall i, (0 <= i && i < Zlength(input)) =>
        (1 <= input[i] && input[i] <= 200000)) &&
      IntArray::full(a, n, input)
    Ensure
      exists post,
        Spec(input, __return) &&
        IntArray::full(a, n, post)
*/
/* QCP_INSERT_END:P019_1807G2_subsequence_addition_hard.contract */

{
    qsort(a, (size_t)n, sizeof(*a), cmp_int);
    if (a[0] != 1) return 0;
    long long sum = 1;
    /*@ Inv Assert
        exists sorted,
          a == a@pre && n == n@pre &&
          n == Zlength(input) &&
          1 <= n && n <= 200000 &&
          Zlength(sorted) == n &&
          Permutation(input, sorted) &&
          increasing(sorted) &&
          FullDecisionSpecBridge(input, sorted) &&
          (forall k, (0 <= k && k < n) =>
            (1 <= sorted[k] && sorted[k] <= 200000)) &&
          1 <= i && i <= n &&
          1 <= sum && sum <= 200000 * i &&
          PrefixAdditionState(sorted, i, sum) &&
          IntArray::full(a, n, sorted)
    */
    for (int i = 1; i < n; ++i) {
        if (a[i] > sum) return 0;
        sum += a[i];
    }
    return 1;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n, *a; scanf("%d", &n); a = malloc((size_t)n * sizeof(*a));
//         for (int i = 0; i < n; ++i) scanf("%d", &a[i]);
//         puts(solver(a, n) ? "YES" : "NO"); free(a);
//     }
//     return 0;
// }
