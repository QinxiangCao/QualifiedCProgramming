/*
 * Codeforces 2051/C - Preparing for the Exam  (rating 1000, IMPLEMENTATION)
 *
 * List i asks every question except a_i.  So Monocarp passes iff the set of
 * questions he does not know is empty, or is exactly {a_i}.
 */

// #include <stdio.h>
// #include <string.h>
/*@ Extern Coq
      (Pre : Z -> list Z -> (Z -> Prop) -> Prop)
      (Spec : Z -> list Z -> (Z -> Prop) -> list Z -> Prop)
      (KnownFlagsBridge : Z -> (Z -> Prop) -> list Z -> Prop)
      (ResultStringBridge : list Z -> list Z -> Prop)
      (UnknownPrefixSummary : Z -> (Z -> Prop) -> Z -> Z -> Z -> Prop)
      (ResultPrefix : Z -> list Z -> (Z -> Prop) -> Z -> list Z -> list Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P015_2051C_preparing_for_the_exam_lib */

/* solver: pure.  known[1..n] flags, a[0..m-1] the missing question per list;
 * fills res[0..m-1] with '1'/'0' and terminates it. */
static void solver(int n, const char *known, const int *a, int m, char *res)
/* QCP_INSERT_BEGIN:shard09-P015-solver-contract */
/*@ With (missing : list Z) (known_questions : Z -> Prop) (known_flags : list Z)
    Require
      Pre(n, missing, known_questions) && 
      2 <= n && n <= 300000 && 1 <= m && m <= n && 
      (forall i, (0 <= i && i < m) => (1 <= missing[i] && missing[i] <= n)) && (forall q, known_questions(q) => (1 <= q && q <= n)) &&
      m == Zlength(missing) && KnownFlagsBridge(n, known_questions, known_flags) && CharArray::full(known, n + 1, known_flags) * IntArray::full(a, m, missing) * CharArray::undef_full(res, m + 1)
    Ensure
      exists (out : list Z) (result_bytes : list Z),
        Spec(n, missing, known_questions, out) &&
        ResultStringBridge(out, result_bytes) && CharArray::full(known, n + 1, known_flags) * IntArray::full(a, m, missing) * CharArray::full(res, m + 1, result_bytes)
*/
/* QCP_INSERT_END:shard09-P015-solver-contract */
{
    int unknown = 0, only = 0;
    /*@ Inv Assert
        n == n@pre && known == known@pre && a == a@pre &&
        m == m@pre && res == res@pre &&
        Pre(n@pre, missing, known_questions) &&
        2 <= n@pre && n@pre <= 300000 &&
        1 <= m@pre && m@pre <= n@pre &&
        (forall i, (0 <= i && i < m@pre) =>
          (1 <= missing[i] && missing[i] <= n@pre)) &&
        (forall x, known_questions(x) => (1 <= x && x <= n@pre)) &&
        m@pre == Zlength(missing) &&
        1 <= q && q <= n@pre + 1 &&
        0 <= unknown && unknown <= q - 1 &&
        0 <= only && only <= n@pre &&
        UnknownPrefixSummary(n@pre, known_questions, q, unknown, only) &&
        KnownFlagsBridge(n@pre, known_questions, known_flags) &&
        CharArray::full(known@pre, n@pre + 1, known_flags) *
        IntArray::full(a@pre, m@pre, missing) *
        CharArray::undef_full(res@pre, m@pre + 1)
    */
    for (int q = 1; q <= n; q++)
        if (!known[q]) {
            unknown++;
            only = q;
        }
    /*@ Inv Assert
        exists (out : list Z) (result_bytes : list Z),
        n == n@pre && known == known@pre && a == a@pre &&
        m == m@pre && res == res@pre &&
        Pre(n@pre, missing, known_questions) &&
        2 <= n@pre && n@pre <= 300000 &&
        1 <= m@pre && m@pre <= n@pre &&
        (forall j, (0 <= j && j < m@pre) =>
          (1 <= missing[j] && missing[j] <= n@pre)) &&
        (forall x, known_questions(x) => (1 <= x && x <= n@pre)) &&
        m@pre == Zlength(missing) &&
        0 <= i && i <= m@pre &&
        0 <= unknown && unknown <= n@pre &&
        0 <= only && only <= n@pre &&
        UnknownPrefixSummary(n@pre, known_questions, n@pre + 1, unknown, only) &&
        ResultPrefix(n@pre, missing, known_questions, i, out, result_bytes) &&
        KnownFlagsBridge(n@pre, known_questions, known_flags) &&
        CharArray::full(known@pre, n@pre + 1, known_flags) *
        IntArray::full(a@pre, m@pre, missing) *
        CharArray::full(res@pre, i, result_bytes) *
        CharArray::undef_seg(res@pre, i, m@pre + 1)
    */
    for (int i = 0; i < m; i++)
        res[i] = (unknown == 0 || (unknown == 1 && a[i] == only)) ? '1' : '0';
    res[m] = '\0';
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static int a[300005];
//     static char known[300005], res[300006];
//     while (t--) {
//         int n, m, k;
//         scanf("%d %d %d", &n, &m, &k);
//         memset(known, 0, (size_t)n + 1);
//         for (int i = 0; i < m; i++)
//             scanf("%d", &a[i]);
//         for (int i = 0; i < k; i++) {
//             int q;
//             scanf("%d", &q);
//             known[q] = 1;
//         }
//         solver(n, known, a, m, res);
//         puts(res);
//     }
//     return 0;
// }
