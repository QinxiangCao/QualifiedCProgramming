/*
 * Codeforces 1994/B - Fun Game  (rating 1100, VERDICT)
 *
 * The operation can flip bits of s only at positions >= the first '1' of s.
 * So: if s is all zeros, t must equal s. Otherwise, let i be the first '1' in
 * s; t must have only zeros before i (those bits are unreachable). Everything
 * from i onward can be set arbitrarily, so the answer is "Yes" in that case.
 */

// #include <stdio.h>
#include "string.h"

/* solver: pure. Returns 1 ("Yes") if t is reachable from s, else 0. */
/* QCP_INSERT_BEGIN:P020_1994B_fun_game.support */
/*@ Extern Coq
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (CharArray::undef_seg : Z -> Z -> Z -> Assertion)
      (Spec : list Z -> list Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P020_1994B_fun_game_lib */
/* QCP_INSERT_END:P020_1994B_fun_game.support */
static int solver(const char *s, const char *t, int n)/* QCP_INSERT_BEGIN:P020_1994B_fun_game.contract */

/*@ With (source target : list Z)
    Require
      n == Zlength(source) && n == Zlength(target) &&
      1 <= Zlength(source) && Zlength(source) <= 200000 &&
      Zlength(target) == Zlength(source) &&
      (forall i, (0 <= i && i < Zlength(source)) =>
        (source[i] == 48 || source[i] == 49)) &&
      (forall i, (0 <= i && i < Zlength(target)) =>
        (target[i] == 48 || target[i] == 49)) &&
      CharArray::full(s, n + 1, app(source, cons(0, nil))) *
      CharArray::undef_seg(s, n + 1, 200005) *
      CharArray::full(t, n + 1, app(target, cons(0, nil))) *
      CharArray::undef_seg(t, n + 1, 200005)
    Ensure
      Spec(source, target, __return) &&
      CharArray::full(s, n + 1, app(source, cons(0, nil))) *
      CharArray::undef_seg(s, n + 1, 200005) *
      CharArray::full(t, n + 1, app(target, cons(0, nil))) *
      CharArray::undef_seg(t, n + 1, 200005)
*/
/* QCP_INSERT_END:P020_1994B_fun_game.contract */

{
    int i = 0;
    /*@ Inv Assert
      s == s@pre && t == t@pre && n == n@pre &&
      n == Zlength(source) && n == Zlength(target) &&
      1 <= Zlength(source) && Zlength(source) <= 200000 &&
      Zlength(target) == Zlength(source) &&
      (forall k, (0 <= k && k < Zlength(source)) =>
        (source[k] == 48 || source[k] == 49)) &&
      (forall k, (0 <= k && k < Zlength(target)) =>
        (target[k] == 48 || target[k] == 49)) &&
      0 <= i && i <= n &&
      (forall k, (0 <= k && k < i) => source[k] == 48) &&
      CharArray::full(s, n + 1, app(source, cons(0, nil))) *
      CharArray::undef_seg(s, n + 1, 200005) *
      CharArray::full(t, n + 1, app(target, cons(0, nil))) *
      CharArray::undef_seg(t, n + 1, 200005)
    */
    while (i < n && s[i] == '0')
        i++;

    if (i == n)                       /* s is all zeros */
        /*@ Assert
          s == s@pre && t == t@pre && n == n@pre &&
          n == Zlength(source) && n == Zlength(target) &&
          1 <= Zlength(source) && Zlength(source) <= 200000 &&
          Zlength(target) == Zlength(source) &&
          (forall k, (0 <= k && k < Zlength(source)) =>
            (source[k] == 48 || source[k] == 49)) &&
          (forall k, (0 <= k && k < Zlength(target)) =>
            (target[k] == 48 || target[k] == 49)) &&
          i == n &&
          (forall k, (0 <= k && k < n) => source[k] == 48) &&
          valid_string(source) && valid_string(target) &&
          string_length(source) == n && string_length(target) == n &&
          store_string(s, source) *
          CharArray::undef_seg(s, n + 1, 200005) *
          store_string(t, target) *
          CharArray::undef_seg(t, n + 1, 200005)
        */
        return strncmp(s, t, n) /*@ where str1 = source, str2 = target */ == 0;

    /*@ Inv Assert
      s == s@pre && t == t@pre && n == n@pre &&
      n == Zlength(source) && n == Zlength(target) &&
      1 <= Zlength(source) && Zlength(source) <= 200000 &&
      Zlength(target) == Zlength(source) &&
      (forall k, (0 <= k && k < Zlength(source)) =>
        (source[k] == 48 || source[k] == 49)) &&
      (forall k, (0 <= k && k < Zlength(target)) =>
        (target[k] == 48 || target[k] == 49)) &&
      0 <= i && i < n && source[i] == 49 &&
      (forall k, (0 <= k && k < i) => source[k] == 48) &&
      0 <= j && j <= i &&
      (forall k, (0 <= k && k < j) => target[k] == 48) &&
      CharArray::full(s, n + 1, app(source, cons(0, nil))) *
      CharArray::undef_seg(s, n + 1, 200005) *
      CharArray::full(t, n + 1, app(target, cons(0, nil))) *
      CharArray::undef_seg(t, n + 1, 200005)
    */
    for (int j = 0; j < i; j++)       /* t must be zero before first 1 of s */
        if (t[j] != '0')
            return 0;
    return 1;
}

// int main(void)
// {
//     int q;
//     if (scanf("%d", &q) != 1)
//         return 0;
//     while (q--) {
//         int n;
//         scanf("%d", &n);
//         static char s[200005], t[200005];
//         scanf("%s %s", s, t);
//         printf("%s\n", solver(s, t, n) ? "YES" : "NO");
//     }
//     return 0;
// }
