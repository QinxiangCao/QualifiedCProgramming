/*
 * Codeforces 1930/D1 - Sum over all Substrings (Easy)  (rating 1800, OTHER)
 *
 * f(p) (minimum 1s in a p-good string) is computed greedily: scan left to
 * right; whenever an uncovered '1' is seen at position k, place a single 1 that
 * covers positions k, k+1, k+2 (advance the cover to k+2), counting one. This
 * greedy is prefix-consistent, so for a fixed left end i the running count
 * equals f(s[i..k]); summing over all k and all i gives the answer.
 */

// #include <stdio.h>

/* QCP_INSERT_BEGIN:shard09-P060-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P060_1930D1_sum_over_all_substrings_lib */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
*/
/*@ Extern Coq
      (CompletedRows : list Z -> Z -> Z -> Prop)
      (CurrentRow : list Z -> Z -> Z -> Z -> Prop)
      (PrefixCoverSummary : list Z -> Z -> Z -> Z -> Z -> Prop)
*/
/*@ Extern Coq (FValue : list Z -> Z -> Prop) */
/* QCP_INSERT_END:shard09-P060-solver-support */

/* solver: pure. Returns the sum of f over all substrings of s[0..n-1]. */
static long long solver(const char *s, int n)
/* QCP_INSERT_BEGIN:shard09-P060-solver-contract */
/*@ With (bits : list Z)
    Require
      1 <= n && n <= 100 && (forall i, (0 <= i && i < n) => (bits[i] == 48 || bits[i] == 49)) &&
      n == Zlength(bits) && CharArray::full(s, n, bits)
    Ensure
      Spec(bits, __return) &&
      CharArray::full(s, n, bits)
*/
/* QCP_INSERT_END:shard09-P060-solver-contract */
{
    long long total = 0;
    /*@ Inv Assert
          s == s@pre && n == n@pre &&
          1 <= n@pre && n@pre <= 100 && n@pre == Zlength(bits) &&
          (forall j, (0 <= j && j < n@pre) =>
             (bits[j] == 48 || bits[j] == 49)) &&
          0 <= i && i <= n@pre &&
          0 <= total && total <= i * n@pre * n@pre &&
          CompletedRows(bits, i, total) &&
          CharArray::full(s@pre, n@pre, bits)
    */
    for (int i = 0; i < n; i++) {
        int cover = i - 1;        /* positions <= cover already accounted for */
        long long cnt = 0;
        /*@ Inv Assert
              exists base row_total,
                s == s@pre && n == n@pre &&
                1 <= n@pre && n@pre <= 100 && n@pre == Zlength(bits) &&
                (forall j, (0 <= j && j < n@pre) =>
                   (bits[j] == 48 || bits[j] == 49)) &&
                0 <= i && i < n@pre && i <= k && k <= n@pre &&
                i - 1 <= cover && cover <= k + 1 &&
                0 <= cnt && cnt <= k - i &&
                0 <= base && base <= i * n@pre * n@pre &&
                0 <= row_total && row_total <= (k - i) * n@pre &&
                total == base + row_total &&
                CompletedRows(bits, i, base) &&
                CurrentRow(bits, i, k, row_total) &&
                PrefixCoverSummary(bits, i, k, cover, cnt) &&
                CharArray::full(s@pre, n@pre, bits)
        */
        for (int k = i; k < n; k++) {
            if (s[k] == '1' && k > cover) { cnt++; cover = k + 2; }
            /*@ FValue(sublist(i, k + 1, bits), cnt) */
            total += cnt;         /* cnt == f(s[i..k]) */
        }
    }
    return total;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         int n;
//         char s[105];
//         scanf("%d %104s", &n, s);
//         printf("%lld\n", solver(s, n));
//     }
//     return 0;
// }
