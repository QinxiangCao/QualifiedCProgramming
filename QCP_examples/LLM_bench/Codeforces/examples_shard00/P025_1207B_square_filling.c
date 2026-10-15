/* Codeforces 1207/B - Square Filling */
// #include <stdio.h>
#include "array2_ext_def.h"

typedef struct
{
    int r, c;
} Operation;

/* QCP_INSERT_BEGIN:P025_1207B_square_filling.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Spec : Z -> Z -> list (list Z) -> option (list (Z * Z)) -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P025_1207B_square_filling_lib */
/* QCP_INSERT_END:P025_1207B_square_filling.support */
/*@ Extern Coq
      (ScanOperations : Z -> Z -> list (list Z) -> Z -> Z -> list (Z * Z) -> Prop)
      (made_state : list (Z * Z) -> list Z)
      (staged_ops : list (Z * Z) -> list (option Z))
      (CheckedPrefix : Z -> Z -> list (list Z) -> list (Z * Z) -> Z -> Z -> Prop)
*/
static int solver(int n, int m, const int a[50][50],
                  Operation *ops) /* QCP_INSERT_BEGIN:P025_1207B_square_filling.contract */

/*@ With (matrix : list (list Z))
             (matrix_mem : list (list (option Z)))
    Require
      2 <= n && n <= 50 &&
      2 <= m && m <= 50 &&
      Zlength(matrix) == n &&
      (forall i, (0 <= i && i < n) => Zlength(matrix[i]) == m) &&
      (forall i j, (0 <= i && i < n && 0 <= j && j < m) =>
        ((Znth(j, Znth(i, matrix, nil), 0) == 0) ||
         (Znth(j, Znth(i, matrix, nil), 0) == 1))) &&
      Zlength(matrix_mem) == 50 &&
      (forall i, (0 <= i && i < 50) =>
        Zlength(Znth(i, matrix_mem, nil)) == 50) &&
      (forall i, (0 <= i && i < n) =>
        (forall j, (0 <= j && j < m) =>
          Znth(j, Znth(i, matrix_mem, nil), None) ==
            Some(Znth(j, Znth(i, matrix, nil), 0)))) &&
      IntArray2::mixed_full(a, 50, 50, matrix_mem) *
      IntArray::undef_full(ops, 5000)
    Ensure
      exists ops_mem,
        ((__return == -1 && Spec(n, m, matrix, None)) ||
         (exists result,
            Spec(n, m, matrix, Some(result)) && __return == Zlength(result) &&
            (forall i, (0 <= i && i < __return) =>
              (ops_mem[2 * i] == Some(fst(result[i]) + 1) &&
               ops_mem[2 * i + 1] == Some(snd(result[i]) + 1))))) &&
        IntArray2::mixed_full(a, 50, 50, matrix_mem) *
        IntArray::mixed_full(ops, 5000, ops_mem)
*/
/* QCP_INSERT_END:P025_1207B_square_filling.contract */

{
    int made[50 * 50] = {0}, count = 0;
    /*@ IntArray::undef_full(ops@pre, 5000)
        which implies
        IntArray::mixed_full(ops@pre, 5000, staged_ops(nil))
    */
    /*@ Inv Assert
          exists result,
            n == n@pre && m == m@pre && a == a@pre && ops == ops@pre &&
            2 <= n@pre && n@pre <= 50 &&
            2 <= m@pre && m@pre <= 50 &&
            Zlength(matrix) == n@pre &&
            (forall row, (0 <= row && row < n@pre) =>
              Zlength(matrix[row]) == m@pre) &&
            (forall row col,
              (0 <= row && row < n@pre && 0 <= col && col < m@pre) =>
                ((Znth(col, Znth(row, matrix, nil), 0) == 0) ||
                 (Znth(col, Znth(row, matrix, nil), 0) == 1))) &&
            Zlength(matrix_mem) == 50 &&
            (forall row, (0 <= row && row < 50) =>
              Zlength(Znth(row, matrix_mem, nil)) == 50) &&
            (forall row, (0 <= row && row < n@pre) =>
              (forall col, (0 <= col && col < m@pre) =>
                Znth(col, Znth(row, matrix_mem, nil), None) ==
                  Some(Znth(col, Znth(row, matrix, nil), 0)))) &&
            0 <= i && i <= n@pre - 1 &&
            count == Zlength(result) && 0 <= count &&
            count <= i * (m@pre - 1) && count <= 2500 &&
            ScanOperations(n@pre, m@pre, matrix, i, 0, result) &&
            Zlength(made_state(result)) == 2500 &&
            Zlength(staged_ops(result)) == 5000 &&
            IntArray2::mixed_full(a@pre, 50, 50, matrix_mem) *
            IntArray::full(made, 2500, made_state(result)) *
            IntArray::mixed_full(ops@pre, 5000, staged_ops(result))
    */
    for (int i = 0; i + 1 < n; ++i)
        /*@ Inv Assert
              exists result,
                n == n@pre && m == m@pre && a == a@pre && ops == ops@pre &&
                2 <= n@pre && n@pre <= 50 &&
                2 <= m@pre && m@pre <= 50 &&
                Zlength(matrix) == n@pre &&
                (forall row, (0 <= row && row < n@pre) =>
                  Zlength(matrix[row]) == m@pre) &&
                (forall row col,
                  (0 <= row && row < n@pre && 0 <= col && col < m@pre) =>
                    ((Znth(col, Znth(row, matrix, nil), 0) == 0) ||
                     (Znth(col, Znth(row, matrix, nil), 0) == 1))) &&
                Zlength(matrix_mem) == 50 &&
                (forall row, (0 <= row && row < 50) =>
                  Zlength(Znth(row, matrix_mem, nil)) == 50) &&
                (forall row, (0 <= row && row < n@pre) =>
                  (forall col, (0 <= col && col < m@pre) =>
                    Znth(col, Znth(row, matrix_mem, nil), None) ==
                      Some(Znth(col, Znth(row, matrix, nil), 0)))) &&
                0 <= i && i < n@pre - 1 &&
                0 <= j && j <= m@pre - 1 &&
                count == Zlength(result) && 0 <= count &&
                count <= i * (m@pre - 1) + j && count <= 2500 &&
                ScanOperations(n@pre, m@pre, matrix, i, j, result) &&
                Zlength(made_state(result)) == 2500 &&
                Zlength(staged_ops(result)) == 5000 &&
                IntArray2::mixed_full(a@pre, 50, 50, matrix_mem) *
                IntArray::full(made, 2500, made_state(result)) *
                IntArray::mixed_full(ops@pre, 5000, staged_ops(result))
        */
        for (int j = 0; j + 1 < m; ++j)
        {
            if (a[i][j] && a[i + 1][j] && a[i][j + 1] && a[i + 1][j + 1])
            {
                /*@ 0 <= 2 * count && 2 * count + 1 < 5000 by local */
                ((int *)ops)[2 * count] = i + 1;
                ((int *)ops)[2 * count + 1] = j + 1;
                count++;
                /*@ 0 <= i * 50 + j && i * 50 + j < 2500 &&
                0 <= (i + 1) * 50 + j && (i + 1) * 50 + j < 2500 &&
                0 <= i * 50 + (j + 1) && i * 50 + (j + 1) < 2500 &&
                0 <= (i + 1) * 50 + (j + 1) &&
                  (i + 1) * 50 + (j + 1) < 2500 by local */
                made[i * 50 + j] = 1;
                made[(i + 1) * 50 + j] = 1;
                made[i * 50 + (j + 1)] = 1;
                made[(i + 1) * 50 + (j + 1)] = 1;
            }
        }
    /*@ Inv Assert
          exists result,
            n == n@pre && m == m@pre && a == a@pre && ops == ops@pre &&
            2 <= n@pre && n@pre <= 50 &&
            2 <= m@pre && m@pre <= 50 &&
            Zlength(matrix) == n@pre &&
            (forall row, (0 <= row && row < n@pre) =>
              Zlength(matrix[row]) == m@pre) &&
            (forall row col,
              (0 <= row && row < n@pre && 0 <= col && col < m@pre) =>
                ((Znth(col, Znth(row, matrix, nil), 0) == 0) ||
                 (Znth(col, Znth(row, matrix, nil), 0) == 1))) &&
            Zlength(matrix_mem) == 50 &&
            (forall row, (0 <= row && row < 50) =>
              Zlength(Znth(row, matrix_mem, nil)) == 50) &&
            (forall row, (0 <= row && row < n@pre) =>
              (forall col, (0 <= col && col < m@pre) =>
                Znth(col, Znth(row, matrix_mem, nil), None) ==
                  Some(Znth(col, Znth(row, matrix, nil), 0)))) &&
            0 <= i && i <= n@pre &&
            count == Zlength(result) && 0 <= count &&
            count <= (n@pre - 1) * (m@pre - 1) && count <= 2500 &&
            ScanOperations(n@pre, m@pre, matrix, n@pre - 1, 0, result) &&
            CheckedPrefix(n@pre, m@pre, matrix, result, i, 0) &&
            Zlength(made_state(result)) == 2500 &&
            Zlength(staged_ops(result)) == 5000 &&
            IntArray2::mixed_full(a@pre, 50, 50, matrix_mem) *
            IntArray::full(made, 2500, made_state(result)) *
            IntArray::mixed_full(ops@pre, 5000, staged_ops(result))
    */
    for (int i = 0; i < n; ++i)
        /*@ Inv Assert
              exists result,
                n == n@pre && m == m@pre && a == a@pre && ops == ops@pre &&
                2 <= n@pre && n@pre <= 50 &&
                2 <= m@pre && m@pre <= 50 &&
                Zlength(matrix) == n@pre &&
                (forall row, (0 <= row && row < n@pre) =>
                  Zlength(matrix[row]) == m@pre) &&
                (forall row col,
                  (0 <= row && row < n@pre && 0 <= col && col < m@pre) =>
                    ((Znth(col, Znth(row, matrix, nil), 0) == 0) ||
                     (Znth(col, Znth(row, matrix, nil), 0) == 1))) &&
                Zlength(matrix_mem) == 50 &&
                (forall row, (0 <= row && row < 50) =>
                  Zlength(Znth(row, matrix_mem, nil)) == 50) &&
                (forall row, (0 <= row && row < n@pre) =>
                  (forall col, (0 <= col && col < m@pre) =>
                    Znth(col, Znth(row, matrix_mem, nil), None) ==
                      Some(Znth(col, Znth(row, matrix, nil), 0)))) &&
                0 <= i && i < n@pre && 0 <= j && j <= m@pre &&
                count == Zlength(result) && 0 <= count &&
                count <= (n@pre - 1) * (m@pre - 1) && count <= 2500 &&
                ScanOperations(n@pre, m@pre, matrix, n@pre - 1, 0, result) &&
                CheckedPrefix(n@pre, m@pre, matrix, result, i, j) &&
                Zlength(made_state(result)) == 2500 &&
                Zlength(staged_ops(result)) == 5000 &&
                IntArray2::mixed_full(a@pre, 50, 50, matrix_mem) *
                IntArray::full(made, 2500, made_state(result)) *
                IntArray::mixed_full(ops@pre, 5000, staged_ops(result))
        */
        for (int j = 0; j < m; ++j)
            if (a[i][j] != made[i * 50 + j])
                return -1;
    return count;
}

// int main(void)
// {
//     int n, m, a[50][50]; Operation ops[2500];
//     if (scanf("%d %d", &n, &m) != 2) return 0;
//     for (int i = 0; i < n; ++i)
//         for (int j = 0; j < m; ++j) scanf("%d", &a[i][j]);
//     int count = solver(n, m, a, ops);
//     if (count < 0) { puts("-1"); return 0; }
//     printf("%d\n", count);
//     for (int i = 0; i < count; ++i) printf("%d %d\n", ops[i].r, ops[i].c);
//     return 0;
// }
