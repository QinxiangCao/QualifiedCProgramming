/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_lib
*/

/* Codeforces 765/B - Code obfuscation */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P023_765B_code_obfuscation.support */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P023_765B_code_obfuscation_lib */
/*@ Extern Coq
      (ObfuscationPrefixState : list Z -> Z -> Z -> Prop)
*/
/* QCP_INSERT_END:P023_765B_code_obfuscation.support */
static int solver(const char *s)/* QCP_INSERT_BEGIN:P023_765B_code_obfuscation.contract */

/*@ With (text : list Z)
    Require
      1 <= Zlength(text) && Zlength(text) <= 500 &&
      (forall i, (0 <= i && i < Zlength(text)) => (97 <= text[i] && text[i] <= 122)) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil)))
    Ensure
      Spec(text, __return) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil)))
*/
/* QCP_INSERT_END:P023_765B_code_obfuscation.contract */

{
    char next = 'a';
    /*@ Inv Assert
      s == s@pre &&
      1 <= Zlength(text) && Zlength(text) <= 500 &&
      (forall k, (0 <= k && k < Zlength(text)) =>
        (97 <= text[k] && text[k] <= 122)) &&
      0 <= i && i <= Zlength(text) &&
      97 <= next && next <= 122 &&
      ObfuscationPrefixState(text, i, next) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil)))
    */
    for (int i = 0; s[i]; ++i) {
        if (s[i] > next) return 0;
        if (s[i] == next && next < 'z') ++next;
    }
    return 1;
}

// int main(void)
// {
//     char s[505];
//     if (scanf("%504s", s) != 1) return 0;
//     puts(solver(s) ? "YES" : "NO");
//     return 0;
// }
