/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P021_2030C_a_true_battle_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P021_2030C_a_true_battle_lib
*/

/* Codeforces 2030/C - A TRUE Battle */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P021_2030C_a_true_battle.support */
/*@ Extern Coq
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (CharArray::undef_seg : Z -> Z -> Z -> Assertion)
      (Spec : list Z -> Z -> Prop)
      (NoAdjacentOnesBefore : list Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P021_2030C_a_true_battle_lib */
/* QCP_INSERT_END:P021_2030C_a_true_battle.support */
static int solver(const char *s, int n)/* QCP_INSERT_BEGIN:P021_2030C_a_true_battle.contract */

/*@ With (values : list Z)
    Require
      n == Zlength(values) &&
      2 <= Zlength(values) && Zlength(values) <= 200000 &&
      (forall i, (0 <= i && i < Zlength(values)) =>
        (values[i] == 48 || values[i] == 49)) &&
      CharArray::full(s, n + 1, app(values, cons(0, nil))) *
      CharArray::undef_seg(s, n + 1, 200005)
    Ensure
      Spec(values, __return) &&
      CharArray::full(s, n + 1, app(values, cons(0, nil))) *
      CharArray::undef_seg(s, n + 1, 200005)
*/
/* QCP_INSERT_END:P021_2030C_a_true_battle.contract */

{
    if (s[0] == '1' || s[n - 1] == '1') return 1;
    /*@ Inv Assert
      s == s@pre && n == n@pre &&
      n == Zlength(values) &&
      2 <= Zlength(values) && Zlength(values) <= 200000 &&
      (forall k, (0 <= k && k < Zlength(values)) =>
        (values[k] == 48 || values[k] == 49)) &&
      values[0] != 49 && values[Zlength(values) - 1] != 49 &&
      0 <= i && i <= n - 1 &&
      NoAdjacentOnesBefore(values, i) &&
      CharArray::full(s, n + 1, app(values, cons(0, nil))) *
      CharArray::undef_seg(s, n + 1, 200005)
    */
    for (int i = 0; i + 1 < n; ++i)
        if (s[i] == '1' && s[i + 1] == '1') return 1;
    return 0;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n; char s[200005]; scanf("%d %200004s", &n, s);
//         puts(solver(s, n) ? "YES" : "NO");
//     }
//     return 0;
// }
