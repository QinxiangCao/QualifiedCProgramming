/*
 * Codeforces 985/A - Chess Placing  (rating 1100, IMPLEMENTATION)
 *
 * The pieces must land on the n/2 black cells (1,3,5,...) or the n/2 white
 * cells (2,4,6,...).  Pieces never need to cross, so matching the sorted
 * pieces to the sorted targets in order is optimal; take the cheaper colour.
 */

// #include <stdio.h>
// #include <stdlib.h>

/* QCP_INSERT_BEGIN:shard09-P023-solver-support */
/*@ Import Coq Require Import AUXLib.MonotonicList */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P023_985A_chess_placing_lib */
/*@ Extern Coq
      (Permutation : list Z -> list Z -> Prop)
      (Pre : Z -> list Z -> Prop)
      (Spec : Z -> list Z -> Z -> Prop)
      (mono_nondec : list Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P023-solver-support */

/*@ Extern Coq (Z::abs : Z -> Z) */
/*@ Extern Coq (ChessCostPrefix : list Z -> Z -> Z -> Z -> Prop) */

void quicksort(int *arr, int n)
/*@ With (l : list Z)
    Require
      0 <= n && n <= 50000 &&
      IntArray::full(arr, n, l)
    Ensure
      exists l1,
        Permutation(l, l1) &&
        mono_nondec(l1) &&
        IntArray::full(arr, n, l1)
*/
;

// static int cmp_int(const void *a, const void *b)
// {
//     int x = *(const int *)a, y = *(const int *)b;
//     return (x > y) - (x < y);
// }

static int iabs(int x)
/*@ Require
      -100 <= x && x <= 100 && emp
    Ensure
      __return == Z::abs(x@pre) && emp
*/
{
    return x < 0 ? -x : x;
}

/* solver: minimum moves to gather the pieces on one colour.  Sorts p[]. */
static long long solver(int *p, int half)
/* QCP_INSERT_BEGIN:shard09-P023-solver-contract */
/*@ With (positions : list Z)
    Require
      2 <= 2 * half && 2 * half <= 100 &&
      Pre(2 * half, positions) && (forall i, (0 <= i && i < half) => (1 <= positions[i] && positions[i] <= 2 * half)) &&
      half == Zlength(positions) && IntArray::full(p, half, positions)
    Ensure
      Spec(2 * half, positions, __return) &&
      exists (p_after : list Z), Permutation(positions, p_after) && IntArray::full(p, half, p_after)
*/
/* QCP_INSERT_END:shard09-P023-solver-contract */
{
    // qsort(p, half, sizeof *p, cmp_int);
    quicksort(p, half) /*@ where l = positions */;
    long long odd = 0, even = 0;
    /*@ Inv Assert
          exists sorted,
            p == p@pre && half == half@pre &&
            2 <= 2 * half@pre && 2 * half@pre <= 100 &&
            Pre(2 * half@pre, positions) &&
            half@pre == Zlength(positions) &&
            Zlength(sorted) == half@pre &&
            (forall k, (0 <= k && k < half@pre) =>
              (1 <= sorted[k] && sorted[k] <= 2 * half@pre)) &&
            Permutation(positions, sorted) && mono_nondec(sorted) &&
            0 <= i && i <= half@pre &&
            0 <= odd && odd <= 100 * i &&
            0 <= even && even <= 100 * i &&
            ChessCostPrefix(sorted, i, odd, even) &&
            IntArray::full(p, half@pre, sorted)
    */
    for (int i = 0; i < half; i++) {
        odd += iabs(p[i] - (2 * i + 1));       /* black cells 1,3,5,... */
        even += iabs(p[i] - (2 * i + 2));      /* white cells 2,4,6,... */
    }
    return odd < even ? odd : even;
}

// int main(void)
// {
//     int n;
//     if (scanf("%d", &n) != 1)
//         return 0;
//     static int p[55];
//     int half = n / 2;
//     for (int i = 0; i < half; i++)
//         scanf("%d", &p[i]);
//     printf("%lld\n", solver(p, half));
//     return 0;
// }
