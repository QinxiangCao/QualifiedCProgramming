/*
 * Codeforces 1311/C - Perform the Combo  (rating 1300, BRUTE FORCE)
 *
 * Position j (0-based) is pressed once per try that reaches past it: that is
 * the number of p_i > j, plus the final successful try.  A difference array
 * over the p values turns that into one linear pass.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Pre : list Z -> list Z -> Prop)
      (Spec : list Z -> list Z -> list Z -> Prop)
*/
/*@ Extern Coq
      (DifferencePrefix : list Z -> Z -> Z -> list Z -> Prop)
      (DifferenceReady : list Z -> Z -> list Z -> Prop)
      (PartialSpec : list Z -> list Z -> Z -> list Z -> Prop)
      (sum : list Z -> Z)
*/
/*@ Extern Coq (aligned_4 : Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P031_1311C_perform_the_combo_lib */



static void *memset(void *dst, int c, unsigned long n)
/*@ Require
      0 <= n && c == 0 && aligned_4(dst) &&
      UCharArray::undef_full(dst, n)
    Ensure
      __return == dst && aligned_4(dst) &&
      UCharArray::full(dst, n, repeat_Z(0, n))
*/
{
    unsigned char *p = (unsigned char *)dst;
    /*@ Inv Assert
          dst == dst@pre && c == c@pre && n == n@pre && p == dst@pre &&
          0 <= n@pre && c@pre == 0 && aligned_4(dst@pre) &&
          0 <= i && i <= n@pre &&
          UCharArray::full(dst@pre, i, repeat_Z(0, i)) *
          UCharArray::undef_seg(dst@pre, i, n@pre)
    */
    for (unsigned long i = 0; i < n; i++)
        p[i] = (unsigned char)c;
    return dst;
}

static long long diff[200006];            /* work array, cleared on every call */

/* solver: reads no input.  cover[j] = number of tries pressing s[j]; accumulates
 * the per-letter totals into cnt[26]. */
static void solver(const char *s, int n, const int *p, int m, long long *cnt)
/* QCP_INSERT_BEGIN:shard09-P031-solver-contract */
/*@ With (text : list Z) (tries : list Z)
    Require
      2 <= n && n <= 200000 && 1 <= m && m <= 200000 && (forall i, (0 <= i && i < n) => (97 <= text[i] && text[i] <= 122)) && (forall i, (0 <= i && i < m) => (1 <= tries[i] && tries[i] < n)) &&
      n == Zlength(text) && m == Zlength(tries) && CharArray::full(s, n, text) * IntArray::full(p, m, tries) * Int64Array::undef_full(cnt, 26) * Int64Array::undef_full(diff, n + 1)
    Ensure
      exists (out : list Z) (diff_after : list Z),
        Spec(text, tries, out) &&
        Zlength(diff_after) == n + 1 &&
        CharArray::full(s, n, text) * IntArray::full(p, m, tries) * Int64Array::full(cnt, 26, out) * Int64Array::full(diff, n + 1, diff_after)
*/
/* QCP_INSERT_END:shard09-P031-solver-contract */
{
    /*@ Assert
          s == s@pre && n == n@pre && p == p@pre && m == m@pre && cnt == cnt@pre &&
          2 <= n@pre && n@pre <= 200000 && 1 <= m@pre && m@pre <= 200000 &&
          (forall k, (0 <= k && k < n@pre) =>
             (97 <= text[k] && text[k] <= 122)) &&
          (forall k, (0 <= k && k < m@pre) =>
             (1 <= tries[k] && tries[k] < n@pre)) &&
          n@pre == Zlength(text) && m@pre == Zlength(tries) &&
          aligned_4(pointer_offset(diff, 0, sizeof(long long), long long)) &&
          CharArray::full(s@pre, n@pre, text) *
          IntArray::full(p@pre, m@pre, tries) *
          Int64Array::undef_full(cnt@pre, 26) *
          UCharArray::undef_full(
            pointer_offset(diff, 0, sizeof(long long), long long),
            sizeof(long long) * (n@pre + 1))
    */
    memset(diff, 0, sizeof(long long) * (n + 1));   /* p_i may be n, so n + 1 */
    /*@ Assert
          s == s@pre && n == n@pre && p == p@pre && m == m@pre && cnt == cnt@pre &&
          2 <= n@pre && n@pre <= 200000 && 1 <= m@pre && m@pre <= 200000 &&
          (forall k, (0 <= k && k < n@pre) =>
             (97 <= text[k] && text[k] <= 122)) &&
          (forall k, (0 <= k && k < m@pre) =>
             (1 <= tries[k] && tries[k] < n@pre)) &&
          n@pre == Zlength(text) && m@pre == Zlength(tries) &&
          aligned_4(pointer_offset(diff, 0, sizeof(long long), long long)) &&
          CharArray::full(s@pre, n@pre, text) *
          IntArray::full(p@pre, m@pre, tries) *
          Int64Array::undef_full(cnt@pre, 26) *
          Int64Array::full(diff, n@pre + 1, repeat_Z(0, n@pre + 1))
    */
    /*@ Inv Assert
          exists (diff_l : list Z),
          s == s@pre && n == n@pre && p == p@pre && m == m@pre && cnt == cnt@pre &&
          2 <= n@pre && n@pre <= 200000 && 1 <= m@pre && m@pre <= 200000 &&
          (forall k, (0 <= k && k < n@pre) =>
             (97 <= text[k] && text[k] <= 122)) &&
          (forall k, (0 <= k && k < m@pre) =>
             (1 <= tries[k] && tries[k] < n@pre)) &&
          n@pre == Zlength(text) && m@pre == Zlength(tries) &&
          0 <= i && i <= m@pre &&
          DifferencePrefix(tries, n@pre, i, diff_l) &&
          (forall k, (0 <= k && k < n@pre + 1) =>
             (-i <= diff_l[k] && diff_l[k] <= i)) &&
          CharArray::full(s@pre, n@pre, text) *
          IntArray::full(p@pre, m@pre, tries) *
          Int64Array::undef_full(cnt@pre, 26) *
          Int64Array::full(diff, n@pre + 1, diff_l)
    */
    for (int i = 0; i < m; i++) {         /* try i presses s[0 .. p_i-1] */
        diff[0] = diff[0] + 1;
        diff[p[i]] = diff[p[i]] - 1;
    }
    diff[0] = diff[0] + 1;                /* the final, successful try */
    /*@ Assert
          exists (diff_l : list Z),
          s == s@pre && n == n@pre && p == p@pre && m == m@pre && cnt == cnt@pre &&
          2 <= n@pre && n@pre <= 200000 && 1 <= m@pre && m@pre <= 200000 &&
          (forall k, (0 <= k && k < n@pre) =>
             (97 <= text[k] && text[k] <= 122)) &&
          (forall k, (0 <= k && k < m@pre) =>
             (1 <= tries[k] && tries[k] < n@pre)) &&
          n@pre == Zlength(text) && m@pre == Zlength(tries) &&
          DifferenceReady(tries, n@pre, diff_l) &&
          (forall k, (0 <= k && k < n@pre + 1) =>
             (-m@pre <= diff_l[k] && diff_l[k] <= m@pre + 1)) &&
          aligned_4(cnt@pre) &&
          CharArray::full(s@pre, n@pre, text) *
          IntArray::full(p@pre, m@pre, tries) *
          Int64Array::full(diff, n@pre + 1, diff_l) *
          UCharArray::undef_full(cnt@pre, sizeof(long long) * 26)
    */
    memset(cnt, 0, sizeof(long long) * 26);
    /*@ Assert
          exists (diff_l : list Z),
          s == s@pre && n == n@pre && p == p@pre && m == m@pre && cnt == cnt@pre &&
          2 <= n@pre && n@pre <= 200000 && 1 <= m@pre && m@pre <= 200000 &&
          (forall k, (0 <= k && k < n@pre) =>
             (97 <= text[k] && text[k] <= 122)) &&
          (forall k, (0 <= k && k < m@pre) =>
             (1 <= tries[k] && tries[k] < n@pre)) &&
          n@pre == Zlength(text) && m@pre == Zlength(tries) &&
          DifferenceReady(tries, n@pre, diff_l) &&
          (forall k, (0 <= k && k < n@pre + 1) =>
             (-m@pre <= diff_l[k] && diff_l[k] <= m@pre + 1)) &&
          aligned_4(cnt@pre) &&
          CharArray::full(s@pre, n@pre, text) *
          IntArray::full(p@pre, m@pre, tries) *
          Int64Array::full(diff, n@pre + 1, diff_l) *
          Int64Array::full(cnt@pre, 26, repeat_Z(0, 26))
    */
    long long cover = 0;
    /*@ Inv Assert
          exists (diff_l : list Z) (out : list Z),
          s == s@pre && n == n@pre && p == p@pre && m == m@pre && cnt == cnt@pre &&
          2 <= n@pre && n@pre <= 200000 && 1 <= m@pre && m@pre <= 200000 &&
          (forall k, (0 <= k && k < n@pre) =>
             (97 <= text[k] && text[k] <= 122)) &&
          (forall k, (0 <= k && k < m@pre) =>
             (1 <= tries[k] && tries[k] < n@pre)) &&
          n@pre == Zlength(text) && m@pre == Zlength(tries) &&
          0 <= j && j <= n@pre &&
          DifferenceReady(tries, n@pre, diff_l) &&
          (forall k, (0 <= k && k < n@pre + 1) =>
             (-m@pre <= diff_l[k] && diff_l[k] <= m@pre + 1)) &&
          cover == sum(sublist(0, j, diff_l)) &&
          0 <= cover && cover <= m@pre + 1 &&
          PartialSpec(text, tries, j, out) &&
          (forall k, (0 <= k && k < 26) =>
             (0 <= out[k] && out[k] <= j * (m@pre + 1))) &&
          CharArray::full(s@pre, n@pre, text) *
          IntArray::full(p@pre, m@pre, tries) *
          Int64Array::full(diff, n@pre + 1, diff_l) *
          Int64Array::full(cnt@pre, 26, out)
    */
    for (int j = 0; j < n; j++) {
        cover += diff[j];
        /*@ Assert
              exists (diff_l : list Z) (out : list Z),
              s == s@pre && n == n@pre && p == p@pre && m == m@pre && cnt == cnt@pre &&
              2 <= n@pre && n@pre <= 200000 && 1 <= m@pre && m@pre <= 200000 &&
              (forall k, (0 <= k && k < n@pre) =>
                 (97 <= text[k] && text[k] <= 122)) &&
              (forall k, (0 <= k && k < m@pre) =>
                 (1 <= tries[k] && tries[k] < n@pre)) &&
              n@pre == Zlength(text) && m@pre == Zlength(tries) &&
              0 <= j && j < n@pre &&
              DifferenceReady(tries, n@pre, diff_l) &&
              (forall k, (0 <= k && k < n@pre + 1) =>
                 (-m@pre <= diff_l[k] && diff_l[k] <= m@pre + 1)) &&
              cover == sum(sublist(0, j + 1, diff_l)) &&
              0 <= cover && cover <= m@pre + 1 &&
              PartialSpec(text, tries, j, out) &&
              (forall k, (0 <= k && k < 26) =>
                 (0 <= out[k] && out[k] <= j * (m@pre + 1))) &&
              CharArray::full(s@pre, n@pre, text) *
              IntArray::full(p@pre, m@pre, tries) *
              Int64Array::full(diff, n@pre + 1, diff_l) *
              Int64Array::full(cnt@pre, 26, out)
        */
        cnt[s[j] - 'a'] += cover;
    }
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static char s[200005];
//     static int p[200005];
//     long long cnt[26];
//     while (t--) {
//         int n, m;
//         scanf("%d %d", &n, &m);
//         scanf("%200004s", s);
//         for (int i = 0; i < m; i++)
//             scanf("%d", &p[i]);
//         solver(s, n, p, m, cnt);
//         for (int c = 0; c < 26; c++)
//             printf("%lld%c", cnt[c], c == 25 ? '\n' : ' ');
//     }
//     return 0;
// }
