/*
 * Codeforces 411/B - Multi-core Processor  (rating 1600, IMPLEMENTATION)
 *
 * Simulate cycle by cycle: within a cycle, count the live cores addressing
 * each cell.  A cell with two or more writers locks (with its writers), and a
 * write to an already locked cell locks that single core.
 */

// #include <stdio.h>
// #include <string.h>
#include "array2_ext_def.h"
static void *memset(void *dst, int c, unsigned long n)
/*@ Require
      0 <= n && c == 0 && 
      UCharArray::undef_full(dst, n)
    Ensure
      __return == dst && 
      UCharArray::full(dst, n, repeat_Z(0, n))
*/;


#define MAXN 105

/* solver: pure.  x[i][j] instructions -> lock[i] = locking cycle or 0. */
/* QCP_INSERT_BEGIN:shard09-P049-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P049_411B_multi_core_processor_lib */
/*@ Extern Coq
      (Pre : Z -> list(list Z) -> Prop)
      (Spec : Z -> list(list Z) -> list Z -> Prop)
      (concat : {A} -> list (list A) -> list A)
*/
/* QCP_INSERT_END:shard09-P049-solver-support */
/*@ Extern Coq
      (LockTimesThrough : list(list Z) -> list Z -> Z -> Prop)
      (DeadCellsThrough : list(list Z) -> list Z -> Z -> Z -> list Z -> Prop)
      (DeadCellsBefore : list(list Z) -> list Z -> Z -> Z -> list Z -> Prop)
      (DirectLockScan : list(list Z) -> list Z -> Z -> Z -> Prop)
      (WriterCounts : list(list Z) -> list Z -> Z -> Z -> Z -> list Z -> Prop)
      (CellMarksPrefix : list(list Z) -> list Z -> list Z -> Z -> Z -> Z -> list Z -> Prop)
      (CollisionClosurePrefix : list(list Z) -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (IntArray::seg_shape : Z -> Z -> Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (aligned_4 : Z -> Prop)
*/
static void solver(int n, int m, int k, const int x[][MAXN], int *lock)
/* QCP_INSERT_BEGIN:shard09-P049-solver-contract */
/*@ With (ins : list(list Z)) (xrows : list(list Z))
    Require
      1 <= k && k <= 100 &&
      Pre(k, ins) && 1 <= n && n <= 100 && 1 <= m && m <= 100 && (forall j, (0 <= j && j < n * m) => (0 <= concat(ins)[j] && concat(ins)[j] <= k)) &&
      n == Zlength(ins) && (forall i, (0 <= i && i < n) => Zlength(ins[i]) == m) && Zlength(xrows) == n && (forall i, (0 <= i && i < n) => (Zlength(xrows[i]) == 105 && sublist(0, m, xrows[i]) == ins[i])) && IntArray2::full(x, n, 105, xrows) * IntArray::undef_full(lock, n)
    Ensure
      exists (out : list Z),
        Spec(k@pre, ins, out) &&
        Zlength(out) == n && IntArray2::full(x, n, 105, xrows) * IntArray::full(lock, n, out)
*/
/* QCP_INSERT_END:shard09-P049-solver-contract */
{
    int cell_locked[MAXN] = {0};
    int writers[MAXN], first[MAXN];
    /*@ Inv Assert
          n == n@pre && m == m@pre && k == k@pre && x == x@pre && lock == lock@pre &&
          1 <= k@pre && k@pre <= 100 && Pre(k@pre, ins) &&
          1 <= n@pre && n@pre <= 100 && 1 <= m@pre && m@pre <= 100 &&
          (forall q, (0 <= q && q < n@pre * m@pre) =>
             (0 <= concat(ins)[q] && concat(ins)[q] <= k@pre)) &&
          n@pre == Zlength(ins) &&
          (forall r, (0 <= r && r < n@pre) => Zlength(ins[r]) == m@pre) &&
          Zlength(xrows) == n@pre &&
          (forall r, (0 <= r && r < n@pre) =>
             (Zlength(xrows[r]) == 105 && sublist(0, m@pre, xrows[r]) == ins[r])) &&
          0 <= i && i <= n@pre &&
          IntArray2::full(x@pre, n@pre, 105, xrows) *
          IntArray::seg(lock@pre, 0, i, repeat_Z(0, i)) *
          IntArray::undef_seg(lock@pre, i, n@pre) *
          IntArray::full(cell_locked, 105, repeat_Z(0, 105)) *
          IntArray::undef_full(writers, 105) *
          IntArray::undef_full(first, 105)
    */
    for (int i = 0; i < n; i++)
        lock[i] = 0;
    /*@ Inv Assert
          exists (locks : list Z) (dead : list Z),
          n == n@pre && m == m@pre && k == k@pre && x == x@pre && lock == lock@pre &&
          1 <= k@pre && k@pre <= 100 && Pre(k@pre, ins) &&
          1 <= n@pre && n@pre <= 100 && 1 <= m@pre && m@pre <= 100 &&
          (forall q, (0 <= q && q < n@pre * m@pre) =>
             (0 <= concat(ins)[q] && concat(ins)[q] <= k@pre)) &&
          n@pre == Zlength(ins) &&
          (forall r, (0 <= r && r < n@pre) => Zlength(ins[r]) == m@pre) &&
          Zlength(xrows) == n@pre &&
          (forall r, (0 <= r && r < n@pre) =>
             (Zlength(xrows[r]) == 105 && sublist(0, m@pre, xrows[r]) == ins[r])) &&
          0 <= j && j <= m@pre &&
          LockTimesThrough(ins, locks, j) &&
          DeadCellsThrough(ins, locks, k@pre, j, dead) &&
          IntArray2::full(x@pre, n@pre, 105, xrows) *
          IntArray::full(lock@pre, n@pre, locks) *
          IntArray::full(cell_locked, 105, dead) *
          IntArray::undef_full(writers, 105) *
          IntArray::undef_full(first, 105)
    */
    for (int j = 0; j < m; j++) {
        /*@ Assert
              exists (locks : list Z) (dead : list Z),
              n == n@pre && m == m@pre && k == k@pre && x == x@pre && lock == lock@pre &&
              1 <= k@pre && k@pre <= 100 && Pre(k@pre, ins) &&
              1 <= n@pre && n@pre <= 100 && 1 <= m@pre && m@pre <= 100 &&
              (forall q, (0 <= q && q < n@pre * m@pre) =>
                 (0 <= concat(ins)[q] && concat(ins)[q] <= k@pre)) &&
              n@pre == Zlength(ins) &&
              (forall r, (0 <= r && r < n@pre) => Zlength(ins[r]) == m@pre) &&
              Zlength(xrows) == n@pre &&
              (forall r, (0 <= r && r < n@pre) =>
                 (Zlength(xrows[r]) == 105 && sublist(0, m@pre, xrows[r]) == ins[r])) &&
              0 <= j && j < m@pre &&
              LockTimesThrough(ins, locks, j) &&
              DeadCellsThrough(ins, locks, k@pre, j, dead) &&
              aligned_4(pointer_offset(writers, 0, sizeof(int), int)) &&
              IntArray2::full(x@pre, n@pre, 105, xrows) *
              IntArray::full(lock@pre, n@pre, locks) *
              IntArray::full(cell_locked, 105, dead) *
              UCharArray::undef_full(
                pointer_offset(writers, 0, sizeof(int), int),
                sizeof(int) * (k@pre + 1)) *
              IntArray::undef_seg(writers, k@pre + 1, 105) *
              IntArray::undef_full(first, 105)
        */
        memset(writers, 0, sizeof(int) * (k + 1));
        /*@ Assert
              exists (locks : list Z) (dead : list Z),
              n == n@pre && m == m@pre && k == k@pre && x == x@pre && lock == lock@pre &&
              1 <= k@pre && k@pre <= 100 && Pre(k@pre, ins) &&
              1 <= n@pre && n@pre <= 100 && 1 <= m@pre && m@pre <= 100 &&
              (forall q, (0 <= q && q < n@pre * m@pre) =>
                 (0 <= concat(ins)[q] && concat(ins)[q] <= k@pre)) &&
              n@pre == Zlength(ins) &&
              (forall r, (0 <= r && r < n@pre) => Zlength(ins[r]) == m@pre) &&
              Zlength(xrows) == n@pre &&
              (forall r, (0 <= r && r < n@pre) =>
                 (Zlength(xrows[r]) == 105 && sublist(0, m@pre, xrows[r]) == ins[r])) &&
              0 <= j && j < m@pre &&
              LockTimesThrough(ins, locks, j) &&
              DeadCellsThrough(ins, locks, k@pre, j, dead) &&
              IntArray2::full(x@pre, n@pre, 105, xrows) *
              IntArray::full(lock@pre, n@pre, locks) *
              IntArray::full(cell_locked, 105, dead) *
              IntArray::seg(writers, 0, k@pre + 1, repeat_Z(0, k@pre + 1)) *
              IntArray::undef_seg(writers, k@pre + 1, 105) *
              IntArray::undef_full(first, 105)
        */
        /*@ Inv Assert
              exists (locks : list Z) (dead : list Z),
              n == n@pre && m == m@pre && k == k@pre && x == x@pre && lock == lock@pre &&
              1 <= k@pre && k@pre <= 100 && Pre(k@pre, ins) &&
              1 <= n@pre && n@pre <= 100 && 1 <= m@pre && m@pre <= 100 &&
              (forall q, (0 <= q && q < n@pre * m@pre) =>
                 (0 <= concat(ins)[q] && concat(ins)[q] <= k@pre)) &&
              n@pre == Zlength(ins) &&
              (forall r, (0 <= r && r < n@pre) => Zlength(ins[r]) == m@pre) &&
              Zlength(xrows) == n@pre &&
              (forall r, (0 <= r && r < n@pre) =>
                 (Zlength(xrows[r]) == 105 && sublist(0, m@pre, xrows[r]) == ins[r])) &&
              0 <= j && j < m@pre && 1 <= c && c <= k@pre + 1 &&
              LockTimesThrough(ins, locks, j) &&
              DeadCellsThrough(ins, locks, k@pre, j, dead) &&
              IntArray2::full(x@pre, n@pre, 105, xrows) *
              IntArray::full(lock@pre, n@pre, locks) *
              IntArray::full(cell_locked, 105, dead) *
              IntArray::seg(writers, 0, k@pre + 1, repeat_Z(0, k@pre + 1)) *
              IntArray::undef_seg(writers, k@pre + 1, 105) *
              IntArray::undef_seg(first, 0, 1) *
              IntArray::seg(first, 1, c, repeat_Z(-1, c - 1)) *
              IntArray::undef_seg(first, c, 105)
        */
        for (int c = 1; c <= k; c++)
            first[c] = -1;
        /*@ Inv Assert
              exists (locks : list Z) (dead : list Z) (counts : list Z) (firsts : list Z),
              n == n@pre && m == m@pre && k == k@pre && x == x@pre && lock == lock@pre &&
              1 <= k@pre && k@pre <= 100 && Pre(k@pre, ins) &&
              1 <= n@pre && n@pre <= 100 && 1 <= m@pre && m@pre <= 100 &&
              (forall q, (0 <= q && q < n@pre * m@pre) =>
                 (0 <= concat(ins)[q] && concat(ins)[q] <= k@pre)) &&
              n@pre == Zlength(ins) &&
              (forall r, (0 <= r && r < n@pre) => Zlength(ins[r]) == m@pre) &&
              Zlength(xrows) == n@pre &&
              (forall r, (0 <= r && r < n@pre) =>
                 (Zlength(xrows[r]) == 105 && sublist(0, m@pre, xrows[r]) == ins[r])) &&
              0 <= j && j < m@pre && 0 <= i && i <= n@pre &&
              DeadCellsBefore(ins, locks, k@pre, j + 1, dead) &&
              DirectLockScan(ins, locks, j + 1, i) &&
              WriterCounts(ins, locks, j + 1, i, k@pre, counts) &&
              IntArray2::full(x@pre, n@pre, 105, xrows) *
              IntArray::full(lock@pre, n@pre, locks) *
              IntArray::full(cell_locked, 105, dead) *
              IntArray::seg(writers, 0, k@pre + 1, counts) *
              IntArray::undef_seg(writers, k@pre + 1, 105) *
              IntArray::undef_seg(first, 0, 1) *
              IntArray::seg(first, 1, k@pre + 1, firsts) *
              IntArray::undef_seg(first, k@pre + 1, 105)
        */
        for (int i = 0; i < n; i++) {
            if (lock[i] || x[i][j] == 0)
                continue;
            int c = x[i][j];
            /*@ 1 <= c && c <= k@pre */
            if (cell_locked[c]) {
                lock[i] = j + 1;           /* writing to a dead cell */
                continue;
            }
            writers[c] = writers[c] + 1;
            if (first[c] < 0)
                first[c] = i;
        }
        /*@ Inv Assert
              exists (locks : list Z) (dead : list Z) (counts : list Z) (firsts : list Z),
              n == n@pre && m == m@pre && k == k@pre && x == x@pre && lock == lock@pre &&
              1 <= k@pre && k@pre <= 100 && Pre(k@pre, ins) &&
              1 <= n@pre && n@pre <= 100 && 1 <= m@pre && m@pre <= 100 &&
              (forall q, (0 <= q && q < n@pre * m@pre) =>
                 (0 <= concat(ins)[q] && concat(ins)[q] <= k@pre)) &&
              n@pre == Zlength(ins) &&
              (forall r, (0 <= r && r < n@pre) => Zlength(ins[r]) == m@pre) &&
              Zlength(xrows) == n@pre &&
              (forall r, (0 <= r && r < n@pre) =>
                 (Zlength(xrows[r]) == 105 && sublist(0, m@pre, xrows[r]) == ins[r])) &&
              0 <= j && j < m@pre && 1 <= c && c <= k@pre + 1 &&
              WriterCounts(ins, locks, j + 1, n@pre, k@pre, counts) &&
              CellMarksPrefix(ins, locks, counts, k@pre, j + 1, c, dead) &&
              CollisionClosurePrefix(ins, locks, counts, j + 1, c, 0) &&
              IntArray2::full(x@pre, n@pre, 105, xrows) *
              IntArray::full(lock@pre, n@pre, locks) *
              IntArray::full(cell_locked, 105, dead) *
              IntArray::seg(writers, 0, k@pre + 1, counts) *
              IntArray::undef_seg(writers, k@pre + 1, 105) *
              IntArray::undef_seg(first, 0, 1) *
              IntArray::seg(first, 1, k@pre + 1, firsts) *
              IntArray::undef_seg(first, k@pre + 1, 105)
        */
        for (int c = 1; c <= k; c++)
            if (writers[c] >= 2) {
                cell_locked[c] = 1;
                /*@ Inv Assert
                      exists (locks : list Z) (dead : list Z) (counts : list Z) (firsts : list Z),
                      n == n@pre && m == m@pre && k == k@pre && x == x@pre && lock == lock@pre &&
                      1 <= k@pre && k@pre <= 100 && Pre(k@pre, ins) &&
                      1 <= n@pre && n@pre <= 100 && 1 <= m@pre && m@pre <= 100 &&
                      (forall q, (0 <= q && q < n@pre * m@pre) =>
                         (0 <= concat(ins)[q] && concat(ins)[q] <= k@pre)) &&
                      n@pre == Zlength(ins) &&
                      (forall r, (0 <= r && r < n@pre) => Zlength(ins[r]) == m@pre) &&
                      Zlength(xrows) == n@pre &&
                      (forall r, (0 <= r && r < n@pre) =>
                         (Zlength(xrows[r]) == 105 && sublist(0, m@pre, xrows[r]) == ins[r])) &&
                      0 <= j && j < m@pre && 1 <= c && c <= k@pre &&
                      2 <= counts[c] && 0 <= i && i <= n@pre &&
                      WriterCounts(ins, locks, j + 1, n@pre, k@pre, counts) &&
                      CellMarksPrefix(ins, locks, counts, k@pre, j + 1, c + 1, dead) &&
                      CollisionClosurePrefix(ins, locks, counts, j + 1, c, i) &&
                      IntArray2::full(x@pre, n@pre, 105, xrows) *
                      IntArray::full(lock@pre, n@pre, locks) *
                      IntArray::full(cell_locked, 105, dead) *
                      IntArray::seg(writers, 0, k@pre + 1, counts) *
                      IntArray::undef_seg(writers, k@pre + 1, 105) *
                      IntArray::undef_seg(first, 0, 1) *
                      IntArray::seg(first, 1, k@pre + 1, firsts) *
                      IntArray::undef_seg(first, k@pre + 1, 105)
                */
                for (int i = 0; i < n; i++)
                    if (!lock[i] && x[i][j] == c)
                        lock[i] = j + 1;
            }
    }
}

// int main(void)
// {
//     int n, m, k;
//     if (scanf("%d %d %d", &n, &m, &k) != 3)
//         return 0;
//     static int x[MAXN][MAXN], lock[MAXN];
//     for (int i = 0; i < n; i++)
//         for (int j = 0; j < m; j++)
//             scanf("%d", &x[i][j]);
//     solver(n, m, k, x, lock);
//     for (int i = 0; i < n; i++)
//         printf("%d\n", lock[i]);
//     return 0;
// }
