/*
 * Codeforces 1384/A - Common Prefixes  (rating 1200, CONSTRUCTIVE)
 *
 * Keep one working string of 200 letters.  To realise a_i, copy the current
 * string and flip the letter at index a_i between 'a' and 'b': the first a_i
 * letters still agree and position a_i now differs, so the longest common
 * prefix is exactly a_i (a_i <= 50 < 200, so the index always exists).
 */

// #include <stdio.h>
#include "array2_ext_def.h"
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P025_1384A_common_prefixes_lib */
/*@ Extern Coq
      (Spec : list Z -> list(list Z) -> Prop)
*/
/*@ Extern Coq
      (InitialRowProgress : Z -> Z -> list(list(option Z)) -> Prop)
      (ProducedRows : list Z -> Z -> list(list(option Z)) -> Prop)
      (CopyProgress : list Z -> Z -> Z -> list(list(option Z)) -> Prop)
*/

#define LEN 200

/* solver: pure.  Writes n+1 strings of length LEN into out[][], consecutive
 * ones having longest common prefix a[i]. */
static void solver(const int *a, int n, char out[][LEN + 1])
/* QCP_INSERT_BEGIN:shard09-P025-solver-contract */
/*@ With (prefix_lengths : list Z)
    Require
      1 <= n && n <= 100 && (forall i, (0 <= i && i < n) => (0 <= prefix_lengths[i] && prefix_lengths[i] <= 50)) &&
      n == Zlength(prefix_lengths) && IntArray::full(a, n, prefix_lengths) * CharArray2::undef_full(out, n + 1, 201)
    Ensure
      exists (out_spec : list(list Z)),
        Spec(prefix_lengths, out_spec) &&
        Zlength(out_spec) == n + 1 && (forall i, (0 <= i && i < n + 1) => Zlength(out_spec[i]) == 200) && exists (out_rows : list(list Z)), Zlength(out_rows) == n + 1 && (forall i, (0 <= i && i < n + 1) => out_rows[i] == app(out_spec[i], cons(0, nil))) && IntArray::full(a, n, prefix_lengths) * CharArray2::full(out, n + 1, 201, out_rows)
*/
/* QCP_INSERT_END:shard09-P025-solver-contract */
{
    /*@ Inv Assert
          exists rows,
            n == n@pre && a == a@pre && out == out@pre &&
            1 <= n@pre && n@pre <= 100 &&
            n@pre == Zlength(prefix_lengths) &&
            (forall i, (0 <= i && i < n@pre) =>
              (0 <= prefix_lengths[i] && prefix_lengths[i] <= 50)) &&
            0 <= j && j <= LEN &&
            InitialRowProgress(n@pre, j, rows) &&
            IntArray::full(a@pre, n@pre, prefix_lengths) *
            CharArray2::mixed_full(out@pre, n@pre + 1, 201, rows)
    */
    for (int j = 0; j < LEN; j++)
        out[0][j] = 'a';
    out[0][LEN] = '\0';
    /*@ Inv Assert
          exists rows,
            n == n@pre && a == a@pre && out == out@pre &&
            1 <= n@pre && n@pre <= 100 &&
            n@pre == Zlength(prefix_lengths) &&
            (forall r, (0 <= r && r < n@pre) =>
              (0 <= prefix_lengths[r] && prefix_lengths[r] <= 50)) &&
            0 <= i && i <= n@pre &&
            ProducedRows(prefix_lengths, i + 1, rows) &&
            IntArray::full(a@pre, n@pre, prefix_lengths) *
            CharArray2::mixed_full(out@pre, n@pre + 1, 201, rows)
    */
    for (int i = 0; i < n; i++) {
        /*@ Inv Assert
              exists rows,
                n == n@pre && a == a@pre && out == out@pre &&
                1 <= n@pre && n@pre <= 100 &&
                n@pre == Zlength(prefix_lengths) &&
                (forall r, (0 <= r && r < n@pre) =>
                  (0 <= prefix_lengths[r] && prefix_lengths[r] <= 50)) &&
                0 <= i && i < n@pre &&
                0 <= j && j <= 201 &&
                CopyProgress(prefix_lengths, i, j, rows) &&
                IntArray::full(a@pre, n@pre, prefix_lengths) *
                CharArray2::mixed_full(out@pre, n@pre + 1, 201, rows)
        */
        for (int j = 0; j <= LEN; j++)
            out[i + 1][j] = out[i][j];
        int k = a[i];
        /*@ Assert
              exists rows,
                n == n@pre && a == a@pre && out == out@pre &&
                1 <= n@pre && n@pre <= 100 &&
                n@pre == Zlength(prefix_lengths) &&
                (forall r, (0 <= r && r < n@pre) =>
                  (0 <= prefix_lengths[r] && prefix_lengths[r] <= 50)) &&
                0 <= i && i < n@pre &&
                k == prefix_lengths[i] && 0 <= k && k <= 50 &&
                CopyProgress(prefix_lengths, i, 201, rows) &&
                IntArray::full(a@pre, n@pre, prefix_lengths) *
                CharArray2::mixed_full(out@pre, n@pre + 1, 201, rows)
        */
        out[i + 1][k] = out[i][k] == 'a' ? 'b' : 'a';
    }
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static int a[105];
//     static char out[106][LEN + 1];
//     while (t--) {
//         int n;
//         scanf("%d", &n);
//         for (int i = 0; i < n; i++)
//             scanf("%d", &a[i]);
//         solver(a, n, out);
//         for (int i = 0; i <= n; i++)
//             puts(out[i]);
//     }
//     return 0;
// }
