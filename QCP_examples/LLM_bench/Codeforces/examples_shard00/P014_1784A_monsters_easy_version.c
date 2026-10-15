/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_lib
*/

/* Codeforces 1784/A - Monsters (easy version) */
// #include <stdio.h>
// #include <stdlib.h>

typedef unsigned long size_t;

static int cmp_int(const void *x, const void *y)
{
    int a = *(const int *)x, b = *(const int *)y;
    return (a > b) - (a < b);
}

/* QCP_INSERT_BEGIN:P014_1784A_monsters_easy_version.support */
/*@ Extern Coq
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (Spec : list Z -> Z -> Prop)
*/
/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
      (increasing : list Z -> Prop)
      (PrefixGreedyState : list Z -> list Z -> Z -> Z -> Z -> Prop)
*/
/*@ Extern Coq
      (FullPreparationSpecBridge : list Z -> list Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_lib */
/* QCP_INSERT_END:P014_1784A_monsters_easy_version.support */

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
        FullPreparationSpecBridge(contents, sorted) &&
        IntArray::full(base, nmemb, sorted)
*/
;

static long long solver(int *a, int n)/* QCP_INSERT_BEGIN:P014_1784A_monsters_easy_version.contract */

/*@ With (input : list Z)
    Require
      n == Zlength(input) &&
      1 <= Zlength(input) && Zlength(input) <= 200000 &&
      (forall i, (0 <= i && i < Zlength(input)) =>
        (1 <= input[i] && input[i] <= Zlength(input))) &&
      IntArray::full(a, n, input)
    Ensure
      exists post,
        Spec(input, __return) &&
        IntArray::full(a, n, post)
*/
/* QCP_INSERT_END:P014_1784A_monsters_easy_version.contract */

{
    qsort(a, (size_t)n, sizeof(*a), cmp_int);
    long long spent = 0;
    int kept = 0;
    /*@ Inv Assert
        exists sorted,
          a == a@pre && n == n@pre &&
          n == Zlength(input) &&
          1 <= n && n <= 200000 &&
          Zlength(sorted) == n &&
          Permutation(input, sorted) &&
          increasing(sorted) &&
          FullPreparationSpecBridge(input, sorted) &&
          (forall k, (0 <= k && k < n) =>
            (1 <= sorted[k] && sorted[k] <= n)) &&
          0 <= i && i <= n &&
          0 <= kept && kept <= i &&
          0 <= spent && spent <= i * n &&
          PrefixGreedyState(input, sorted, i, kept, spent) &&
          IntArray::full(a, n, sorted)
    */
    for (int i = 0; i < n; ++i) {
        int next = kept + 1;
        if (next > a[i]) next = a[i];
        spent += a[i] - next;
        kept = next;
    }
    return spent;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n, *a; scanf("%d", &n); a = malloc((size_t)n * sizeof(*a));
//         for (int i = 0; i < n; ++i) scanf("%d", &a[i]);
//         printf("%lld\n", solver(a, n)); free(a);
//     }
//     return 0;
// }
