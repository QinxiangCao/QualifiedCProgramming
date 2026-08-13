#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq
      (StackSequenceCount : Z -> Z -> Prop)
      (StackCellBound : Z -> Z -> Z -> Prop)
      (StackCellCorrect : Z -> Z -> Z -> Z -> Prop)
      (StackRowsDone : Z -> list Z -> Z -> Prop)
      (StackRowProgress : Z -> list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.catalan_numbers.catalan_numbers_lib */

int id(int n, int x, int y)
/*@ Require
      0 <= n && n <= 7 &&
      0 <= x && x <= n &&
      0 <= y && y <= n + 1
    Ensure
      __return == x * (n + 1) + y &&
      0 <= __return && __return <= (n + 1) * (n + 1)
 */
{
    return x * (n + 1)  + y;
}

int solve(int n, int *f)
/*@ Require
      0 <= n && n <= 7 &&
      IntArray::undef_full(f, (n + 1) * (n + 1))
    Ensure
      exists table,
      StackSequenceCount(n, __return) &&
      StackRowsDone(n, table, n + 1) &&
      IntArray::full(f, (n + 1) * (n + 1), table)
 */
{
    /*@ Inv Assert
        exists table,
        n == n@pre && f == f@pre &&
        0 <= n@pre && n@pre <= 7 &&
        0 <= i && i <= n@pre + 1 &&
        StackRowsDone(n@pre, table, i) &&
        IntArray::seg(f, 0, i * (n@pre + 1), table) *
        IntArray::undef_seg(f, i * (n@pre + 1),
          (n@pre + 1) * (n@pre + 1))
     */
    for (int i = 0; i <= n; i++) {
        /*@ Inv Assert
            exists table,
            n == n@pre && f == f@pre &&
            0 <= n@pre && n@pre <= 7 &&
            0 <= i && i <= n@pre &&
            0 <= j && j <= n@pre + 1 &&
            StackRowProgress(n@pre, table, i, j) &&
            IntArray::seg(f, 0, i * (n@pre + 1) + j, table) *
            IntArray::undef_seg(f, i * (n@pre + 1) + j,
              (n@pre + 1) * (n@pre + 1))
         */
        for (int j = 0; j <= n; j++) {
            if (i == 0) {
                f[id(n, i, j)] = 1;
            }
            else if (j == 0) {
                /*@ Assert
                    exists table,
                    n == n@pre && f == f@pre &&
                    0 <= n@pre && n@pre <= 7 &&
                    1 <= i && i <= n@pre &&
                    j == 0 &&
                    0 <= i * (n@pre + 1) + j &&
                    i * (n@pre + 1) + j <
                      (n@pre + 1) * (n@pre + 1) &&
                    0 <= (i - 1) * (n@pre + 1) + (j + 1) &&
                    (i - 1) * (n@pre + 1) + (j + 1) <
                      i * (n@pre + 1) + j &&
                    StackRowProgress(n@pre, table, i, j) &&
                    IntArray::seg(f, 0, i * (n@pre + 1) + j, table) *
                    IntArray::undef_seg(f, i * (n@pre + 1) + j,
                      (n@pre + 1) * (n@pre + 1))
                 */
                f[id(n, i, j)] = f[id(n, i-1, j+1)];
            }
            else {
                /*@ Assert
                    exists table,
                    n == n@pre && f == f@pre &&
                    0 <= n@pre && n@pre <= 7 &&
                    1 <= i && i <= n@pre &&
                    1 <= j && j <= n@pre &&
                    0 <= i * (n@pre + 1) + j &&
                    i * (n@pre + 1) + j <
                      (n@pre + 1) * (n@pre + 1) &&
                    0 <= (i - 1) * (n@pre + 1) + (j + 1) &&
                    (i - 1) * (n@pre + 1) + (j + 1) <
                      i * (n@pre + 1) + j &&
                    0 <= i * (n@pre + 1) + (j - 1) &&
                    i * (n@pre + 1) + (j - 1) <
                      i * (n@pre + 1) + j &&
                    StackRowProgress(n@pre, table, i, j) &&
                    IntArray::seg(f, 0, i * (n@pre + 1) + j, table) *
                    IntArray::undef_seg(f, i * (n@pre + 1) + j,
                      (n@pre + 1) * (n@pre + 1))
                 */
                f[id(n, i, j)] = f[id(n, i-1, j+1)] + f[id(n, i, j-1)];
            }
            /*@ Assert
                exists table,
                n == n@pre && f == f@pre &&
                0 <= n@pre && n@pre <= 7 &&
                0 <= i && i <= n@pre &&
                0 <= j && j <= n@pre &&
                StackCellBound(i, j, table[i * (n@pre + 1) + j]) &&
                StackCellCorrect(n@pre, i, j,
                  table[i * (n@pre + 1) + j]) &&
                StackRowProgress(n@pre, table, i, j + 1) &&
                IntArray::seg(f, 0, i * (n@pre + 1) + j + 1, table) *
                IntArray::undef_seg(f, i * (n@pre + 1) + j + 1,
                  (n@pre + 1) * (n@pre + 1))
             */
        }
        /*@ Assert
            exists table,
            n == n@pre && f == f@pre &&
            0 <= n@pre && n@pre <= 7 &&
            0 <= i && i <= n@pre &&
            StackRowsDone(n@pre, table, i + 1) &&
            IntArray::seg(f, 0, (i + 1) * (n@pre + 1), table) *
            IntArray::undef_seg(f, (i + 1) * (n@pre + 1),
              (n@pre + 1) * (n@pre + 1))
         */
    }
    /*@ Assert
        exists table,
        n == n@pre && f == f@pre &&
        0 <= n@pre && n@pre <= 7 &&
        0 <= n@pre * (n@pre + 1) &&
        n@pre * (n@pre + 1) <
          (n@pre + 1) * (n@pre + 1) &&
        StackRowsDone(n@pre, table, n@pre + 1) &&
        StackSequenceCount(n@pre,
          table[n@pre * (n@pre + 1)]) &&
        IntArray::full(f, (n@pre + 1) * (n@pre + 1), table)
     */
    return f[id(n, n, 0)];
}
