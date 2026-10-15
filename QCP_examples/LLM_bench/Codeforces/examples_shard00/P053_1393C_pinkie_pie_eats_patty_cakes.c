/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib
*/

/* Codeforces 1393/C - Pinkie Pie Eats Patty-cakes */
// #include <stdio.h>
// #include <stdlib.h>

typedef unsigned long size_t;

/* QCP_INSERT_BEGIN:P053_1393C_pinkie_pie_eats_patty_cakes.support */
/*@ Extern Coq
      (Pre : list Z -> Prop)
      (Spec : list Z -> Z -> Prop)
      (CountPrefix : list Z -> Z -> list Z -> Prop)
      (MaximumFrequencyPrefix : list Z -> Z -> Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P053_1393C_pinkie_pie_eats_patty_cakes_lib */
/* QCP_INSERT_END:P053_1393C_pinkie_pie_eats_patty_cakes.support */

void *calloc(unsigned long nmemb, unsigned long size)
/*@ calloc_int
    With (cap : Z)
    Require
      0 <= cap &&
      nmemb == cap &&
      size == sizeof(int)
    Ensure
      __return != 0 &&
      IntArray::full(__return, cap, repeat_Z(0, cap))
*/;

void free(void *ptr)
/*@ free_int
    Require exists values cap,
      IntArray::full(ptr, cap, values)
    Ensure emp
*/;

static int solver(const int *a, int n) /* QCP_INSERT_BEGIN:P053_1393C_pinkie_pie_eats_patty_cakes.contract */

/*@ With (values : list Z)
    Require
      2 <= Zlength(values) && Zlength(values) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(values)) => (1 <= values[i] && values[i] <= Zlength(values))) &&
      Pre(values) &&
      n == Zlength(values) && IntArray::full(a, n, values)
    Ensure
      Spec(values, __return) && IntArray::full(a, n, values)
*/
/* QCP_INSERT_END:P053_1393C_pinkie_pie_eats_patty_cakes.contract */

{
    int *cnt = calloc((size_t)n + 1, sizeof(*cnt))
      /*@ where (calloc_int) cap = n + 1 */;

    int mx = 0;
    int c = 0;

    /*@ Inv Assert
          exists counts,
            a == a@pre && n == n@pre && cnt != 0 &&
            mx == 0 && c == 0 &&
            n@pre == Zlength(values) &&
            2 <= Zlength(values) && Zlength(values) <= 100000 &&
            (forall k, (0 <= k && k < Zlength(values)) =>
              (1 <= values[k] && values[k] <= Zlength(values))) &&
            Pre(values) &&
            0 <= i && i <= n@pre &&
            CountPrefix(values, i, counts) &&
            (forall k, (0 <= k && k <= n@pre) =>
              (0 <= counts[k] && counts[k] <= i)) &&
            IntArray::full(a@pre, n@pre, values) *
            IntArray::full(cnt, n@pre + 1, counts)
    */
    for (int i = 0; i < n; ++i) {
        ++cnt[a[i]];
    }

    /*@ Inv Assert
          exists counts,
            a == a@pre && n == n@pre && cnt != 0 &&
            n@pre == Zlength(values) &&
            2 <= Zlength(values) && Zlength(values) <= 100000 &&
            (forall k, (0 <= k && k < Zlength(values)) =>
              (1 <= values[k] && values[k] <= Zlength(values))) &&
            Pre(values) &&
            1 <= i && i <= n@pre + 1 &&
            0 <= mx && mx <= n@pre &&
            0 <= c && c <= i - 1 &&
            CountPrefix(values, n@pre, counts) &&
            MaximumFrequencyPrefix(counts, i, mx, c) &&
            (forall k, (0 <= k && k <= n@pre) =>
              (0 <= counts[k] && counts[k] <= n@pre)) &&
            IntArray::full(a@pre, n@pre, values) *
            IntArray::full(cnt, n@pre + 1, counts)
    */
    for (int i = 1; i <= n; ++i) {
        if (cnt[i] > mx) {
            mx = cnt[i];
            c = 1;
        } else if (cnt[i] == mx) {
            ++c;
        }
    }

    int ans = (n - c) / (mx - 1) - 1;

    /*@ Assert
          exists counts,
            a == a@pre && n == n@pre && cnt != 0 &&
            n@pre == Zlength(values) &&
            2 <= Zlength(values) && Zlength(values) <= 100000 &&
            (forall k, (0 <= k && k < Zlength(values)) =>
              (1 <= values[k] && values[k] <= Zlength(values))) &&
            Pre(values) &&
            2 <= mx && mx <= n@pre &&
            1 <= c && c <= n@pre &&
            ans == (n@pre - c) / (mx - 1) - 1 &&
            CountPrefix(values, n@pre, counts) &&
            MaximumFrequencyPrefix(counts, n@pre + 1, mx, c) &&
            Spec(values, ans) &&
            IntArray::full(a@pre, n@pre, values) *
            IntArray::full(cnt, n@pre + 1, counts)
    */
    free(cnt) /*@ where (free_int) */;
    return ans;
}

// int main(void)
// {
//     int t;
//     scanf("%d", &t);
//
//     while (t--) {
//         int n;
//         scanf("%d", &n);
//
//         int *a = malloc((size_t)n * sizeof(*a));
//         for (int i = 0; i < n; ++i) {
//             scanf("%d", &a[i]);
//         }
//
//         printf("%d\n", solver(a, n));
//         free(a);
//     }
//
//     return 0;
// }
