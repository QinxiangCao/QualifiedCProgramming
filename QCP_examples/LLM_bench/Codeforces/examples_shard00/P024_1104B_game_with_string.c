/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P024_1104B_game_with_string_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P024_1104B_game_with_string_lib
*/

/* Codeforces 1104/B - Game with string */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P024_1104B_game_with_string.support */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (PrefixGameState : list Z -> list Z -> Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (CharArray::undef_full : Z -> Z -> Assertion)
      (CharArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P024_1104B_game_with_string_lib */
/* QCP_INSERT_END:P024_1104B_game_with_string.support */
static char stack[100005];

static int solver(const char *s) /* QCP_INSERT_BEGIN:P024_1104B_game_with_string.contract */

/*@ With (text : list Z)
    Require
      1 <= Zlength(text) && Zlength(text) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(text)) => (97 <= text[i] && text[i] <= 122)) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil))) *
      CharArray::undef_full(stack, 100005)
    Ensure
      Spec(text, __return) &&
      CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil))) *
      CharArray::undef_full(stack, 100005)
*/
/* QCP_INSERT_END:P024_1104B_game_with_string.contract */

{
    int top = 0, moves = 0;
    /*@ Inv Assert
          exists reduced,
          s == s@pre &&
          1 <= Zlength(text) && Zlength(text) <= 100000 &&
          (forall j, (0 <= j && j < Zlength(text)) =>
             (97 <= text[j] && text[j] <= 122)) &&
          0 <= i && i <= Zlength(text) &&
          0 <= top && top <= i && top == Zlength(reduced) &&
          0 <= moves && moves <= i &&
          i == top + 2 * moves &&
          PrefixGameState(sublist(0, i, text), reduced, moves) &&
          CharArray::full(s, Zlength(text) + 1, app(text, cons(0, nil))) *
          CharArray::full(stack, top, reduced) *
          CharArray::undef_seg(stack, top, 100005)
    */
    for (int i = 0; s[i]; ++i)
    {
        if (top && stack[top - 1] == s[i])
        {
            --top;
            ++moves;
        }
        else
        {
            stack[top] = s[i];
            ++top;
        }
    }
    return moves & 1;
}

// int main(void)
// {
//     static char s[100005];
//     if (scanf("%100004s", s) != 1) return 0;
//     puts(solver(s) ? "Yes" : "No");
//     return 0;
// }
