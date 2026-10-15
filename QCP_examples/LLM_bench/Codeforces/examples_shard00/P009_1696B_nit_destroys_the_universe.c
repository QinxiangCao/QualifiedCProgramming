/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib
*/

/* Codeforces 1696/B - NIT Destroys the Universe */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P009_1696B_nit_destroys_the_universe.support */
/*@ Extern Coq
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (Spec : list Z -> Z -> Prop)
*/
/*@ Extern Coq (ScanState : list Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P009_1696B_nit_destroys_the_universe_lib */
/* QCP_INSERT_END:P009_1696B_nit_destroys_the_universe.support */
static int solver(const int *a,
                  int n) /* QCP_INSERT_BEGIN:P009_1696B_nit_destroys_the_universe.contract */

/*@ With (input : list Z)
    Require
      n == Zlength(input) &&
      1 <= Zlength(input) && Zlength(input) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(input)) =>
        (0 <= input[i] && input[i] <= 1000000000)) &&
      IntArray::full(a, n, input) * IntArray::undef_seg(a, n, 200005)
    Ensure
      Spec(input, __return) &&
      IntArray::full(a, n, input) * IntArray::undef_seg(a, n, 200005)
*/
/* QCP_INSERT_END:P009_1696B_nit_destroys_the_universe.contract */

{
    int runs = 0, inside = 0;
    /*@ Inv Assert
        a == a@pre && n == n@pre &&
        n == Zlength(input) &&
        1 <= Zlength(input) && Zlength(input) <= 100000 &&
        (forall k, (0 <= k && k < Zlength(input)) =>
          (0 <= input[k] && input[k] <= 1000000000)) &&
        0 <= i && i <= n &&
        0 <= runs && runs <= i &&
        0 <= inside && inside <= 1 &&
        ScanState(input, i, runs, inside) &&
        IntArray::full(a, n, input) * IntArray::undef_seg(a, n, 200005)
    */
    for (int i = 0; i < n; ++i)
    {
        if (a[i] != 0 && !inside)
        {
            ++runs;
            inside = 1;
        }
        if (a[i] == 0)
            inside = 0;
    }
    return runs > 2 ? 2 : runs;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n, a[200005]; scanf("%d", &n);
//         for (int i = 0; i < n; ++i) scanf("%d", &a[i]);
//         printf("%d\n", solver(a, n));
//     }
//     return 0;
// }
