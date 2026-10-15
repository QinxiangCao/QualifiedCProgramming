/* Codeforces 1800/D - Remove Two Letters */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P027_1800D_remove_two_letters.support */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P027_1800D_remove_two_letters_lib */
/* QCP_INSERT_END:P027_1800D_remove_two_letters.support */
/*@ Extern Coq (EqualGapTwoCount : list Z -> Z -> Z) */
static int solver(const char *s, int n)/* QCP_INSERT_BEGIN:P027_1800D_remove_two_letters.contract */

/*@ With (text : list Z)
    Require
      3 <= Zlength(text) && Zlength(text) <= 200000 &&
      (forall i, (0 <= i && i < Zlength(text)) => (97 <= text[i] && text[i] <= 122)) &&
      n == Zlength(text) &&
      CharArray::full(s, n + 1, app(text, cons(0, nil)))
    Ensure
      Spec(text, __return) &&
      CharArray::full(s, n + 1, app(text, cons(0, nil)))
*/
/* QCP_INSERT_END:P027_1800D_remove_two_letters.contract */

{
    int answer = n - 1;
    /*@ Inv Assert
        s == s@pre && n == n@pre &&
        3 <= Zlength(text) && Zlength(text) <= 200000 &&
        (forall k, (0 <= k && k < Zlength(text)) =>
          (97 <= text[k] && text[k] <= 122)) &&
        n == Zlength(text) &&
        0 <= i && i + 2 <= n &&
        0 <= EqualGapTwoCount(text, i) && EqualGapTwoCount(text, i) <= i &&
        answer == n - 1 - EqualGapTwoCount(text, i) &&
        1 <= answer && answer <= n - 1 &&
        CharArray::full(s, n + 1, app(text, cons(0, nil)))
    */
    for (int i = 0; i + 2 < n; ++i) if (s[i] == s[i + 2]) --answer;
    return answer;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n; char s[200005]; scanf("%d %200004s", &n, s);
//         printf("%d\n", solver(s, n));
//     }
//     return 0;
// }
