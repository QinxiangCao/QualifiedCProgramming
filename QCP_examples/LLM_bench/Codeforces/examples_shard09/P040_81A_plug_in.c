/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_lib
*/

/*
 * Codeforces 81/A - Plug-in  (rating 1400, IMPLEMENTATION)
 *
 * Push characters on a stack; whenever the incoming character equals the top,
 * pop instead, which cancels the pair and immediately exposes any pair that
 * the deletion has created.
 */

// #include <stdio.h>

/* QCP_INSERT_BEGIN:shard09-P040-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P040_81A_plug_in_lib */
/*@ Extern Coq
      (Spec : list Z -> list Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P040-solver-support */

/* solver: pure.  Reduces s[0..n-1] into out (NUL-terminated), returning its
 * length. */
static int solver(const char *s, int n, char *out)
/* QCP_INSERT_BEGIN:shard09-P040-solver-contract */
/*@ With (text : list Z)
    Require
      1 <= n && n <= 200000 && (forall i, (0 <= i && i < n) => (97 <= text[i] && text[i] <= 122)) &&
      n == Zlength(text) && CharArray::full(s, n, text) * CharArray::undef_full(out, n + 1)
    Ensure
      exists (out_spec : list Z),
        Spec(text, out_spec) &&
        __return == Zlength(out_spec) && CharArray::full(s, n, text) * CharArray::full(out, Zlength(out_spec) + 1, app(out_spec, cons(0, nil))) * CharArray::undef_seg(out, Zlength(out_spec) + 1, n + 1)
*/
/* QCP_INSERT_END:shard09-P040-solver-contract */
{
    int top = 0;
    /*@ Inv Assert
        exists (stack : list Z),
          s == s@pre && n == n@pre && out == out@pre &&
          n@pre == Zlength(text) &&
          1 <= n@pre && n@pre <= 200000 &&
          (forall j, (0 <= j && j < n@pre) =>
            (97 <= text[j] && text[j] <= 122)) &&
          0 <= i && i <= n@pre &&
          0 <= top && top <= i &&
          top == Zlength(stack) &&
          Spec(sublist(0, i, text), stack) &&
          CharArray::full(s@pre, n@pre, text) *
          CharArray::full(out@pre, top, stack) *
          CharArray::undef_seg(out@pre, top, n@pre + 1)
    */
    for (int i = 0; i < n; i++) {
        if (top > 0 && out[top - 1] == s[i])
            top--;
        else
            { out[top] = s[i]; top++; }
    }
    out[top] = '\0';
    return top;
}

// int main(void)
// {
//     static char s[200005], out[200005];
//     if (scanf("%200004s", s) != 1)
//         return 0;
//     int n = 0;
//     while (s[n])
//         n++;
//     solver(s, n, out);
//     puts(out);
//     return 0;
// }
