/*
 * Codeforces 1266/C - Diverse Matrix  (rating 1400, CONSTRUCTIVE)
 *
 * The r+c gcds are distinct positive integers, so the magnitude is at least
 * r+c; a[i][j] = (c+i)*j attains it when r >= 2: row i has gcd (c+i) because
 * gcd(1..c) = 1, and column j has gcd j because consecutive integers c+1..c+r
 * are coprime as a set.  A single row (r = 1) instead uses a[1][j] = j+1, and
 * the 1x1 case is impossible since its two gcds coincide.
 */

// #include <stdio.h>
#include "array2_ext_def.h"

/* solver: pure.  Fills m[i][j] (row-major, c columns) with a diverse matrix of
 * minimum magnitude; returns 0 if none exists. */
/* QCP_INSERT_BEGIN:shard09-P037-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P037_1266C_diverse_matrix_lib */
/*@ Extern Coq
      (Spec : Z -> Z -> option (list (list Z)) -> Prop)
*/
/* QCP_INSERT_END:shard09-P037-solver-support */
/*@ Extern Coq
      (ConstructionPrefix : Z -> Z -> list (list (option Z)) -> Z -> Prop)
*/
static int solver(int r, int c, int *m)
/* QCP_INSERT_BEGIN:shard09-P037-solver-contract */
/*@ Require
      1 <= r && r <= 500 && 1 <= c && c <= 500 &&
      IntArray2::undef_full(m, r, c)
    Ensure
      exists (out_spec : option (list (list Z))),
        Spec(r@pre, c@pre, out_spec) &&
        ((out_spec == None && __return == 0 &&
          IntArray2::undef_full(m, r, c)) ||
         (exists (matrix : list (list Z)),
            out_spec == Some(matrix) && __return == 1 &&
            IntArray2::full(m, r, c, matrix)))
*/
/* QCP_INSERT_END:shard09-P037-solver-contract */
{
    if (r == 1 && c == 1)
        return 0;
    /*@ IntArray2::undef_full(m@pre, r@pre, c@pre)
        which implies
        exists rows,
          ConstructionPrefix(r@pre, c@pre, rows, 0) &&
          IntArray2::mixed_full(m@pre, r@pre, c@pre, rows)
    */
    if (r == 1) {
        /*@ Assert
            exists rows,
              r == r@pre && c == c@pre && m == m@pre &&
              r@pre == 1 && 2 <= c@pre && c@pre <= 500 &&
              ConstructionPrefix(r@pre, c@pre, rows, 0) &&
              IntArray::mixed_full(m@pre, c@pre, rows[0])
        */
        /*@ Inv Assert
            exists rows,
              r == r@pre && c == c@pre && m == m@pre &&
              r@pre == 1 && 2 <= c@pre && c@pre <= 500 &&
              1 <= j && j <= c@pre + 1 &&
              0 <= j - 1 && j - 1 <= c@pre &&
              ConstructionPrefix(r@pre, c@pre, rows, j - 1) &&
              IntArray::mixed_full(m@pre, c@pre, rows[0])
        */
        for (int j = 1; j <= c; j++)
            m[j - 1] = j + 1;             /* cols 2..c+1, row gcd 1 */
        return 1;
    }
    /*@ Inv Assert
        exists rows,
          r == r@pre && c == c@pre && m == m@pre &&
          2 <= r@pre && r@pre <= 500 &&
          1 <= c@pre && c@pre <= 500 &&
          1 <= i && i <= r@pre + 1 &&
          0 <= (i - 1) * c@pre &&
          (i - 1) * c@pre <= r@pre * c@pre &&
          r@pre * c@pre <= 250000 &&
          ConstructionPrefix(r@pre, c@pre, rows,
                             (i - 1) * c@pre) &&
          IntArray2::mixed_full(m@pre, r@pre, c@pre, rows)
    */
    for (int i = 1; i <= r; i++)
        /*@ Inv Assert
            exists rows,
              r == r@pre && c == c@pre && m == m@pre &&
              2 <= r@pre && r@pre <= 500 &&
              1 <= c@pre && c@pre <= 500 &&
              1 <= i && i <= r@pre &&
              1 <= j && j <= c@pre + 1 &&
              0 <= (i - 1) * c@pre + (j - 1) &&
              (i - 1) * c@pre + (j - 1) <= r@pre * c@pre &&
              r@pre * c@pre <= 250000 &&
              1 <= (c@pre + i) * j &&
              (j <= c@pre => (c@pre + i) * j <= 500000) &&
              ConstructionPrefix(r@pre, c@pre, rows,
                                 (i - 1) * c@pre + (j - 1)) &&
              IntArray2::mixed_full(m@pre, r@pre, c@pre, rows)
        */
        for (int j = 1; j <= c; j++)
            m[(i - 1) * c + (j - 1)] = (c + i) * j;
    return 1;
}

// int main(void)
// {
//     int r, c;
//     if (scanf("%d %d", &r, &c) != 2)
//         return 0;
//     static int m[500 * 500];
//     if (!solver(r, c, m)) {
//         puts("0");
//         return 0;
//     }
//     for (int i = 0; i < r; i++)
//         for (int j = 0; j < c; j++)
//             printf("%d%c", m[i * c + j], j + 1 == c ? '\n' : ' ');
//     return 0;
// }
