/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_lib
*/

/* Codeforces 38/A - Army */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P006_38A_army.support */
/*@ Extern Coq
      (Spec : Z -> list Z -> Z -> Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_lib */
/* QCP_INSERT_END:P006_38A_army.support */
static int solver(const int *d, int a, int b)/* QCP_INSERT_BEGIN:P006_38A_army.contract */

/*@ With (years : list Z)
    Require
      2 <= Zlength(years) + 1 && Zlength(years) + 1 <= 100 &&
      (forall idx, (0 <= idx && idx < Zlength(years)) =>
        (1 <= years[idx] && years[idx] <= 100)) &&
      1 <= a && a < b && b <= Zlength(years) + 1 &&
      IntArray::full(d, Zlength(years) + 1, cons(0, years)) *
      IntArray::undef_seg(d, Zlength(years) + 1, 101)
    Ensure
      Spec(Zlength(years) + 1, years, a, b, __return) &&
      IntArray::full(d, Zlength(years) + 1, cons(0, years)) *
      IntArray::undef_seg(d, Zlength(years) + 1, 101)
*/
/* QCP_INSERT_END:P006_38A_army.contract */

{
    int ans = 0;
    /*@ Inv Assert
      2 <= Zlength(years) + 1 && Zlength(years) + 1 <= 100 &&
      (forall idx, (0 <= idx && idx < Zlength(years)) =>
        (1 <= years[idx] && years[idx] <= 100)) &&
      d == d@pre && a == a@pre && b == b@pre &&
      1 <= a && a <= i && i <= b && b <= Zlength(years) + 1 &&
      0 <= ans && ans <= 100 * (i - a) &&
      Spec(Zlength(years) + 1, years, a, i, ans) &&
      IntArray::full(d, Zlength(years) + 1, cons(0, years)) *
      IntArray::undef_seg(d, Zlength(years) + 1, 101)
    */
    for (int i = a; i < b; ++i) ans += d[i];
    return ans;
}

// int main(void)
// {
//     int n, d[101] = {0}, a, b;
//     if (scanf("%d", &n) != 1) return 0;
//     for (int i = 1; i < n; ++i) scanf("%d", &d[i]);
//     scanf("%d %d", &a, &b);
//     printf("%d\n", solver(d, a, b));
//     return 0;
// }
