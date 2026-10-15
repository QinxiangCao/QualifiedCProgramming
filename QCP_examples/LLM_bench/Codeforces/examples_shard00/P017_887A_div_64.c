/* Codeforces 887/A - Div. 64 */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P017_887A_div_64.support */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P017_887A_div_64_lib */
/*@ Extern Coq
      (PrefixScan : list Z -> Z -> Z -> Prop)
*/
/* QCP_INSERT_END:P017_887A_div_64.support */
static int solver(const char *s)/* QCP_INSERT_BEGIN:P017_887A_div_64.contract */

/*@ With (text : list Z)
    Require
      1 <= Zlength(text) && Zlength(text) <= 100 &&
      (forall i, (0 <= i && i < Zlength(text)) =>
        (text[i] == 48 || text[i] == 49)) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil)))
    Ensure
      Spec(text, __return) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil)))
*/
/* QCP_INSERT_END:P017_887A_div_64.contract */

{
    int seen_one = 0, zeros = 0;
    /*@ Inv Assert
      s == s@pre &&
      1 <= Zlength(text) && Zlength(text) <= 100 &&
      (forall j, (0 <= j && j < Zlength(text)) =>
        (text[j] == 48 || text[j] == 49)) &&
      0 <= i && i <= Zlength(text) &&
      0 <= seen_one && seen_one <= 1 &&
      0 <= zeros && zeros <= i &&
      PrefixScan(sublist(0, i, text), seen_one, zeros) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil)))
    */
    for (int i = 0; s[i]; ++i) {
        if (s[i] == '1') seen_one = 1;
        else if (seen_one) ++zeros;
    }
    return zeros >= 6;
}

// int main(void)
// {
//     char s[105];
//     if (scanf("%104s", s) != 1) return 0;
//     puts(solver(s) ? "yes" : "no");
//     return 0;
// }
