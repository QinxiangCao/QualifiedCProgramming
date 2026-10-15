/*
 * Codeforces 1927/B - Following the String  (rating 900, CONSTRUCTIVE)
 *
 * a_i says how many earlier positions already carry the letter used at i, so
 * any letter whose running count equals a_i fits.  Keeping 26 counters and
 * taking the first matching letter rebuilds a valid string in one pass.
 *
 * solver() takes one whole test case (the trace) and writes the whole string.
 */

// #include <stdio.h>
/* QCP_INSERT_BEGIN:shard03-P008-solver-support */

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard03.P008_1927B_following_the_string_lib */
/*@ Extern Coq
      (Pre : list Z -> Prop)
      (Spec : list Z -> list Z -> Prop)
*/

/* QCP_INSERT_END:shard03-P008-solver-support */

/* solver: pure.  Writes a string whose trace is a[0..n-1]. */
static void solver(const int *a, int n, char *out)
/* QCP_INSERT_BEGIN:shard03-P008-solver-contract */
/*@ With (trace : list Z)
    Require
      Pre(trace) &&
      1 <= n && n <= 200000 && n == Zlength(trace) &&
      (forall i, (0 <= i && i < n) => (0 <= trace[i] && trace[i] < n)) &&
      IntArray::full(a, n, trace) * CharArray::undef_full(out, n + 1)
    Ensure
      exists (res : list Z),
        Spec(trace, res) &&
        Zlength(res) == n &&
        IntArray::full(a, n, trace) *
        CharArray::full(out, n + 1, app(res, cons(0, nil)))
*/
/* QCP_INSERT_END:shard03-P008-solver-contract */
{
    int cnt[26] = {0};
    for (int i = 0; i < n; i++)
        for (int c = 0; c < 26; c++)
            if (cnt[c] == a[i]) {
                out[i] = (char)('a' + c);
                cnt[c] = cnt[c] + 1;
                break;
            }
    out[n] = '\0';
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static int a[200005];
//     static char out[200006];
//     while (t--) {
//         int n;
//         scanf("%d", &n);
//         for (int i = 0; i < n; i++)
//             scanf("%d", &a[i]);
//         solver(a, n, out);
//         puts(out);
//     }
//     return 0;
// }
