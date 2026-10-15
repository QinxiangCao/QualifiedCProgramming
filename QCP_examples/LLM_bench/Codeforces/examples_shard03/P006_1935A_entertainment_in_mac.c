/*
 * Codeforces 1935/A - Entertainment in MAC  (rating 800, CONSTRUCTIVE)
 *
 * n is even, so plain reversals always land back on s.  The only other
 * reachable strings use the append exactly once: s + rev(s), which is a
 * palindrome and so survives any further reversals, or rev(s) + s, obtained by
 * reversing first.  Since s is a prefix of s + rev(s), the answer is the
 * smaller of s and rev(s) + s.
 *
 * solver() takes one whole test case and writes the resulting string.
 */

// #include <stdio.h>
// #include <string.h>
#include "string.h"
/* QCP_INSERT_BEGIN:shard03-P006-solver-support */

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard03.P006_1935A_entertainment_in_mac_lib */
/*@ Extern Coq
      (Pre : Z -> list Z -> Prop)
      (Spec : Z -> list Z -> list Z -> Prop)
*/

/* QCP_INSERT_END:shard03-P006-solver-support */

/* solver: pure.  Writes the lexicographically smallest reachable string. */
static void solver(const char *s, int len, long long n, char *out)
/* QCP_INSERT_BEGIN:shard03-P006-solver-contract */
/*@ With (str : list Z)
    Require
      Pre(n, str) &&
      2 <= n && n <= 1000000000 &&
      1 <= len && len <= 100 && len == Zlength(str) &&
      (forall i, (0 <= i && i < len) => (97 <= str[i] && str[i] <= 122)) &&
      CharArray::full(s, len + 1, app(str, cons(0, nil))) *
      CharArray::undef_full(out, 2 * len + 1)
    Ensure
      exists (res : list Z),
        Spec(n, str, res) &&
        Zlength(res) <= 2 * len &&
        CharArray::full(s, len + 1, app(str, cons(0, nil))) *
        CharArray::full(out, Zlength(res) + 1, app(res, cons(0, nil))) *
        CharArray::undef_seg(out, Zlength(res) + 1, 2 * len + 1)
*/
/* QCP_INSERT_END:shard03-P006-solver-contract */
{
    (void)n;                              /* only its parity matters, and it is even */
    char rev[105];
    for (int i = 0; i < len; i++)
        rev[i] = s[len - 1 - i];
    rev[len] = '\0';

    char cand[210];
    memcpy(cand, rev, len);
    memcpy(cand + len, s, len);
    cand[2 * len] = '\0';

    if (strcmp(s, cand) <= 0)
        strcpy(out, s);
    else
        strcpy(out, cand);
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         long long n;
//         char s[105], out[210];
//         scanf("%lld %104s", &n, s);
//         solver(s, (int)strlen(s), n, out);
//         puts(out);
//     }
//     return 0;
// }
