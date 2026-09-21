#include "int_array_def.h"

/*@ Extern Coq
      (StackSequenceCount : Z -> Z -> Prop)
      (StackTablePrefix : Z -> list Z -> Z -> Prop)
      (Zpower : Z -> Z -> Z)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.catalan_numbers.catalan_numbers_lib */

int id(int n, int x, int y)
/*@ Require
      0 <= n && n <= 7 &&
      0 <= x && x <= n &&
      0 <= y && y <= n + 1
    Ensure __return == x * (n + 1) + y
 */
{
    return x * (n + 1)  + y;
}

/* Count distinct output sequences obtained from input 1..n by legal stack operations. */
int solve(int n)
/*@ Require
      0 <= n && n <= 7
    Ensure
      StackSequenceCount(n, __return)
 */
{
    int f[64];
    /*@ Inv Assert
        exists table,
        n == n@pre &&
        0 <= n@pre && n@pre <= 7 &&
        0 <= i && i <= n@pre + 1 &&
        StackTablePrefix(n@pre, table, i * (n@pre + 1)) &&
        (forall r c, 0 <= r && r <= n@pre &&
          0 <= c && c <= n@pre && r * (n@pre + 1) + c < i * (n@pre + 1) =>
          0 <= table[r * (n@pre + 1) + c] &&
          table[r * (n@pre + 1) + c] <= Zpower(2, 2 * r + c)) &&
        IntArray::seg(f, 0, i * (n@pre + 1), table) *
        IntArray::undef_seg(f, i * (n@pre + 1), (n@pre + 1) * (n@pre + 1)) *
        IntArray::undef_seg(f, (n@pre + 1) * (n@pre + 1), 64)
     */
    for (int i = 0; i <= n; i++) {
        /*@ Inv Assert
            exists table,
            n == n@pre &&
            0 <= n@pre && n@pre <= 7 &&
            0 <= i && i <= n@pre &&
            0 <= j && j <= n@pre + 1 &&
            StackTablePrefix(n@pre, table, i * (n@pre + 1) + j) &&
            (forall r c, 0 <= r && r <= n@pre &&
              0 <= c && c <= n@pre && r * (n@pre + 1) + c < i * (n@pre + 1) + j =>
              0 <= table[r * (n@pre + 1) + c] &&
              table[r * (n@pre + 1) + c] <= Zpower(2, 2 * r + c)) &&
            IntArray::seg(f, 0, i * (n@pre + 1) + j, table) *
            IntArray::undef_seg(f, i * (n@pre + 1) + j, (n@pre + 1) * (n@pre + 1)) *
        IntArray::undef_seg(f, (n@pre + 1) * (n@pre + 1), 64)
     */
        for (int j = 0; j <= n; j++) {
            if (i == 0) {
                f[id(n, i, j)] = 1;
            }
            else if (j == 0) {
                /*@ Assert
                    exists table,
                    n == n@pre &&
                    0 <= n@pre && n@pre <= 7 &&
                    1 <= i && i <= n@pre &&
                    j == 0 &&
                    0 <= i * (n@pre + 1) + j &&
                    i * (n@pre + 1) + j <
                      (n@pre + 1) * (n@pre + 1) &&
                    0 <= (i - 1) * (n@pre + 1) + (j + 1) &&
                    (i - 1) * (n@pre + 1) + (j + 1) <
                      i * (n@pre + 1) + j &&
                    StackTablePrefix(n@pre, table, i * (n@pre + 1) + j) &&
                    (forall r c, 0 <= r && r <= n@pre &&
                      0 <= c && c <= n@pre && r * (n@pre + 1) + c < i * (n@pre + 1) + j =>
                      0 <= table[r * (n@pre + 1) + c] &&
                      table[r * (n@pre + 1) + c] <= Zpower(2, 2 * r + c)) &&
                    IntArray::seg(f, 0, i * (n@pre + 1) + j, table) *
                    IntArray::undef_seg(f, i * (n@pre + 1) + j,
                      (n@pre + 1) * (n@pre + 1)) *
        IntArray::undef_seg(f, (n@pre + 1) * (n@pre + 1), 64)
     */
                f[id(n, i, j)] = f[id(n, i-1, j+1)];
            }
            else {
                /*@ Assert
                    exists table,
                    n == n@pre &&
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
                    StackTablePrefix(n@pre, table, i * (n@pre + 1) + j) &&
                    (forall r c, 0 <= r && r <= n@pre &&
                      0 <= c && c <= n@pre && r * (n@pre + 1) + c < i * (n@pre + 1) + j =>
                      0 <= table[r * (n@pre + 1) + c] &&
                      table[r * (n@pre + 1) + c] <= Zpower(2, 2 * r + c)) &&
                    IntArray::seg(f, 0, i * (n@pre + 1) + j, table) *
                    IntArray::undef_seg(f, i * (n@pre + 1) + j,
                      (n@pre + 1) * (n@pre + 1)) *
        IntArray::undef_seg(f, (n@pre + 1) * (n@pre + 1), 64)
     */
                f[id(n, i, j)] = f[id(n, i-1, j+1)] + f[id(n, i, j-1)];
            }
        }
    }
    /*@ Assert
        exists table,
        n == n@pre &&
        0 <= n@pre && n@pre <= 7 &&
        0 <= n@pre * (n@pre + 1) &&
        n@pre * (n@pre + 1) <
          (n@pre + 1) * (n@pre + 1) &&
        StackSequenceCount(n@pre,
          table[n@pre * (n@pre + 1)]) &&
        IntArray::full(f, (n@pre + 1) * (n@pre + 1), table) *
        IntArray::undef_seg(f, (n@pre + 1) * (n@pre + 1), 64)
     */
    int result = f[id(n, n, 0)];
    /*@ Assert
      n == n@pre &&
        StackSequenceCount(n@pre, result) &&
        IntArray::undef_full(f, 64)
     */
    return result;
}
