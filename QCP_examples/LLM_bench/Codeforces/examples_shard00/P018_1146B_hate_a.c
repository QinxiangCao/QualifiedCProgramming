/* Codeforces 1146/B - Hate "A" */
// #include <stdio.h>
#include "string.h"

/* QCP_INSERT_BEGIN:P018_1146B_hate_a.support */
/*@ Extern Coq
      (Spec : list Z -> option (list Z) -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (CharArray::undef_full : Z -> Z -> Assertion)
      (CharArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P018_1146B_hate_a_lib */
/* QCP_INSERT_END:P018_1146B_hate_a.support */
/*@ Extern Coq
      (FilteredPrefix : list Z -> Z -> list Z -> Prop)
      (NoAInterval : list Z -> Z -> Z -> Prop)
      (MatchedSuffixPrefix : list Z -> list Z -> Z -> Z -> Prop)
*/

static int solver(const char *given, char *out) /* QCP_INSERT_BEGIN:P018_1146B_hate_a.contract */

/*@ With (given_data : list Z)
    Require
      1 <= Zlength(given_data) && Zlength(given_data) <= 100000 &&
      (forall i, (0 <= i && i < Zlength(given_data)) => (97 <= given_data[i] && given_data[i] <= 122)) &&
      CharArray::full(given, Zlength(given_data) + 1, app(given_data, cons(0, nil))) *
      CharArray::undef_full(out, 100005)
    Ensure
      CharArray::full(given, Zlength(given_data) + 1, app(given_data, cons(0, nil))) *
      ((__return == 0 && Spec(given_data, None) &&
        CharArray::full(out, Zlength(given_data) + 1, app(given_data, cons(0, nil))) *
        CharArray::undef_seg(out, Zlength(given_data) + 1, 100005)) ||
       (exists result,
          __return == 1 && Spec(given_data, Some(result)) &&
          CharArray::full(out, Zlength(result) + 1, app(result, cons(0, nil))) *
          CharArray::undef_seg(out, Zlength(result) + 1, 100005)))
*/
/* QCP_INSERT_END:P018_1146B_hate_a.contract */

{
    char stripped[100005];
    /*@ Assert
          1 <= Zlength(given_data) && Zlength(given_data) <= 100000 &&
          (forall j, (0 <= j && j < Zlength(given_data)) =>
             (97 <= given_data[j] && given_data[j] <= 122)) &&
          valid_string(given_data) &&
          string_length(given_data) == Zlength(given_data) &&
          string_length(given_data) < INT_MAX &&
          given == given@pre && out == out@pre &&
          store_string(given, given_data) *
          CharArray::undef_full(out, string_length(given_data) + 1) *
          CharArray::undef_seg(out, string_length(given_data) + 1, 100005) *
          CharArray::undef_full(stripped, 100005)
    */
    strcpy(out, given) /*@ where src_str = given_data */;
    int n = (int)strlen(out) /*@ where str = given_data */, k = 0;
    /*@ Inv Assert
          exists filtered,
          given == given@pre && out == out@pre &&
          n == Zlength(given_data) &&
          1 <= Zlength(given_data) && Zlength(given_data) <= 100000 &&
          (forall j, (0 <= j && j < Zlength(given_data)) =>
             (97 <= given_data[j] && given_data[j] <= 122)) &&
          0 <= i && i <= n &&
          0 <= k && k <= i && k == Zlength(filtered) &&
          FilteredPrefix(given_data, i, filtered) &&
          CharArray::full(given, Zlength(given_data) + 1, app(given_data, cons(0, nil))) *
          CharArray::full(out, Zlength(given_data) + 1, app(given_data, cons(0, nil))) *
          CharArray::undef_seg(out, Zlength(given_data) + 1, 100005) *
          CharArray::full(stripped, k, filtered) *
          CharArray::undef_seg(stripped, k, 100005)
    */
    for (int i = 0; i < n; ++i)
        if (out[i] != 'a')
        {
            stripped[k] = out[i];
            ++k;
        }
    if (k & 1)
    {
        /*@ exists filtered,
            CharArray::full(stripped, k, filtered) *
            CharArray::undef_seg(stripped, k, 100005)
            which implies
            exists (filtered : list Z),
            k == Zlength(filtered) &&
            CharArray::undef_full(stripped, 100005)
        */
        return 0;
    }
    int suffix = k / 2, prefix = n - suffix;
    /*@ Inv Assert
          exists filtered,
          given == given@pre && out == out@pre &&
          n == Zlength(given_data) &&
          1 <= Zlength(given_data) && Zlength(given_data) <= 100000 &&
          (forall j, (0 <= j && j < Zlength(given_data)) =>
             (97 <= given_data[j] && given_data[j] <= 122)) &&
          0 <= k && k <= n &&
          k == Zlength(filtered) &&
          FilteredPrefix(given_data, n, filtered) &&
          0 <= suffix && k == 2 * suffix &&
          prefix == n - suffix && 0 <= prefix && prefix <= n &&
          prefix <= i && i <= n &&
          NoAInterval(given_data, prefix, i) &&
          CharArray::full(given, Zlength(given_data) + 1, app(given_data, cons(0, nil))) *
          CharArray::full(out, Zlength(given_data) + 1, app(given_data, cons(0, nil))) *
          CharArray::undef_seg(out, Zlength(given_data) + 1, 100005) *
          CharArray::full(stripped, k, filtered) *
          CharArray::undef_seg(stripped, k, 100005)
    */
    for (int i = prefix; i < n; ++i)
        if (out[i] == 'a')
        {
            /*@ exists filtered,
            CharArray::full(stripped, k, filtered) *
            CharArray::undef_seg(stripped, k, 100005)
            which implies
            exists (filtered : list Z),
            k == Zlength(filtered) &&
            CharArray::undef_full(stripped, 100005)
        */
            return 0;
        }
    /*@ Inv Assert
          exists filtered,
          given == given@pre && out == out@pre &&
          n == Zlength(given_data) &&
          1 <= Zlength(given_data) && Zlength(given_data) <= 100000 &&
          (forall j, (0 <= j && j < Zlength(given_data)) =>
             (97 <= given_data[j] && given_data[j] <= 122)) &&
          0 <= k && k <= n &&
          k == Zlength(filtered) &&
          FilteredPrefix(given_data, n, filtered) &&
          0 <= suffix && k == 2 * suffix &&
          prefix == n - suffix && 0 <= prefix && prefix <= n &&
          NoAInterval(given_data, prefix, n) &&
          0 <= i && i <= suffix &&
          MatchedSuffixPrefix(filtered, given_data, prefix, i) &&
          CharArray::full(given, Zlength(given_data) + 1, app(given_data, cons(0, nil))) *
          CharArray::full(out, Zlength(given_data) + 1, app(given_data, cons(0, nil))) *
          CharArray::undef_seg(out, Zlength(given_data) + 1, 100005) *
          CharArray::full(stripped, k, filtered) *
          CharArray::undef_seg(stripped, k, 100005)
    */
    for (int i = 0; i < suffix; ++i)
        if (stripped[i] != out[prefix + i])
        {
            /*@ exists filtered,
                CharArray::full(stripped, k, filtered) *
                CharArray::undef_seg(stripped, k, 100005)
                which implies
                exists (filtered : list Z),
                k == Zlength(filtered) &&
                CharArray::undef_full(stripped, 100005)
            */
            return 0;
        }
    out[prefix] = '\0';
    /*@ exists filtered,
        CharArray::full(stripped, k, filtered) *
        CharArray::undef_seg(stripped, k, 100005)
        which implies
        exists (filtered : list Z),
        k == Zlength(filtered) &&
        CharArray::undef_full(stripped, 100005)
    */
    return 1;
}

// int main(void)
// {
//     static char t[100005], out[100005];
//     if (scanf("%100004s", t) != 1) return 0;
//     puts(solver(t, out) ? out : ":(");
//     return 0;
// }
