/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib
*/

/*
 * Codeforces 1288/D - Minimax Problem  (rating 2000, BINARY SEARCH)
 *
 * Binary search the answer x.  Each array becomes an m-bit mask marking the
 * positions where it reaches x; the pair works iff the two masks cover all m
 * positions.  With m <= 8 there are only 256 masks, so keep one representative
 * of each and test all pairs.
 */

// #include <stdio.h>
#include "array2_ext_def.h"

/* QCP_INSERT_BEGIN:shard09-P066-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib */
/*@ Extern Coq
      (fst : {A B} -> A * B -> A)
      (snd : {A B} -> A * B -> B)
      (Pre : list(list Z) -> Prop)
      (concat : {A} -> list (list A) -> list A)
      (Spec : list(list Z) -> Z*Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P066-solver-support */

/*@ Extern Coq
      (PairAtLeast : list(list Z) -> Z -> Z -> Z -> Prop)
      (FeasibleAtThreshold : list(list Z) -> Z -> Prop)
      (IntArray::mixed_full : Z -> Z -> list(option Z) -> Assertion)
*/

/*@ Extern Coq
      (RowMaskPrefix : list(list Z) -> Z -> Z -> Z -> Z -> Prop)
      (RepresentativePrefix : list(list Z) -> Z -> Z -> Z -> list Z -> Prop)
      (NoCoverPrefix : list Z -> Z -> Z -> Z -> Prop)
      (SolverSearchMeaning : list(list Z) -> Z -> Z -> Z -> Z -> Prop)
*/

/* feasible: is some pair of arrays >= x in every position?  Stores the winning
 * indices in *bi, *bj. */
static int feasible(const int *a, int n, int m, int x, int *rep, int *bi, int *bj)
/*@ With (rows : list(list Z)) (old_bi old_bj : list(option Z))
    Require
      Pre(rows) &&
      1 <= n && n <= 300000 && 1 <= m && m <= 8 &&
      0 <= x && x <= 1000000000 &&
      (forall k, (0 <= k && k < n * m) => (0 <= concat(rows)[k] && concat(rows)[k] <= 1000000000)) &&
      n == Zlength(rows) && m == Zlength(rows[0]) &&
      Zlength(old_bi) == 1 && Zlength(old_bj) == 1 &&
      IntArray2::full(a, n, m, rows) *
      IntArray::full_shape(rep, 256) *
      IntArray::mixed_full(bi, 1, old_bi) *
      IntArray::mixed_full(bj, 1, old_bj)
    Ensure
      exists (reps : list Z),
        Zlength(reps) == 256 &&
        (((__return == 1 &&
           exists i j,
             PairAtLeast(rows, x, i, j) &&
             IntArray::full(bi, 1, cons(i + 1, nil)) *
             IntArray::full(bj, 1, cons(j + 1, nil))) ||
          (__return == 0 && (! FeasibleAtThreshold(rows, x)) &&
           IntArray::mixed_full(bi, 1, old_bi) *
           IntArray::mixed_full(bj, 1, old_bj))) &&
         IntArray2::full(a, n, m, rows) *
         IntArray::full(rep, 256, reps))
*/
{
    int full = (1 << m) - 1;
    /*@ Inv Assert
          exists (reps : list Z),
            a == a@pre && n == n@pre && m == m@pre &&
            x == x@pre && rep == rep@pre && bi == bi@pre && bj == bj@pre &&
            Pre(rows) &&
            1 <= n@pre && n@pre <= 300000 &&
            1 <= m@pre && m@pre <= 8 &&
            0 <= x@pre && x@pre <= 1000000000 &&
            n@pre == Zlength(rows) && m@pre == Zlength(rows[0]) &&
            Zlength(old_bi) == 1 && Zlength(old_bj) == 1 &&
            full == (1 << m@pre) - 1 && 0 <= full && full <= 255 &&
            0 <= s && s <= full + 1 &&
            Zlength(reps) == 256 &&
            (forall q, (0 <= q && q < s) => reps[q] == -1) &&
            IntArray2::full(a@pre, n@pre, m@pre, rows) *
            IntArray::full(rep@pre, 256, reps) *
            IntArray::mixed_full(bi@pre, 1, old_bi) *
            IntArray::mixed_full(bj@pre, 1, old_bj)
     */
    for (int s = 0; s <= full; s++)
        rep[s] = -1;
    /*@ Inv Assert
          exists (reps : list Z),
            a == a@pre && n == n@pre && m == m@pre &&
            x == x@pre && rep == rep@pre && bi == bi@pre && bj == bj@pre &&
            Pre(rows) &&
            1 <= n@pre && n@pre <= 300000 &&
            1 <= m@pre && m@pre <= 8 &&
            0 <= x@pre && x@pre <= 1000000000 &&
            n@pre == Zlength(rows) && m@pre == Zlength(rows[0]) &&
            Zlength(old_bi) == 1 && Zlength(old_bj) == 1 &&
            full == (1 << m@pre) - 1 && 0 <= full && full <= 255 &&
            0 <= i && i <= n@pre && Zlength(reps) == 256 &&
            RepresentativePrefix(rows, x@pre, m@pre, i, reps) &&
            (forall q, (0 <= q && q <= full) =>
               (-1 <= reps[q] && reps[q] < i)) &&
            IntArray2::full(a@pre, n@pre, m@pre, rows) *
            IntArray::full(rep@pre, 256, reps) *
            IntArray::mixed_full(bi@pre, 1, old_bi) *
            IntArray::mixed_full(bj@pre, 1, old_bj)
     */
    for (int i = 0; i < n; i++) {
        int mask = 0;
        /*@ Inv Assert
              exists (reps : list Z),
                a == a@pre && n == n@pre && m == m@pre &&
                x == x@pre && rep == rep@pre && bi == bi@pre && bj == bj@pre &&
                Pre(rows) &&
                1 <= n@pre && n@pre <= 300000 &&
                1 <= m@pre && m@pre <= 8 &&
                0 <= x@pre && x@pre <= 1000000000 &&
                n@pre == Zlength(rows) && m@pre == Zlength(rows[0]) &&
                Zlength(old_bi) == 1 && Zlength(old_bj) == 1 &&
                full == (1 << m@pre) - 1 && 0 <= full && full <= 255 &&
                0 <= i && i < n@pre && 0 <= j && j <= m@pre &&
                0 <= i * m@pre + j && i * m@pre + j <= n@pre * m@pre &&
                0 <= mask && mask <= full && Zlength(reps) == 256 &&
                RepresentativePrefix(rows, x@pre, m@pre, i, reps) &&
                RowMaskPrefix(rows, x@pre, i, j, mask) &&
                (forall q, (0 <= q && q <= full) =>
                   (-1 <= reps[q] && reps[q] < i)) &&
                IntArray2::full(a@pre, n@pre, m@pre, rows) *
                IntArray::full(rep@pre, 256, reps) *
                IntArray::mixed_full(bi@pre, 1, old_bi) *
                IntArray::mixed_full(bj@pre, 1, old_bj)
         */
        for (int j = 0; j < m; j++)
            if (a[i * m + j] >= x)
                mask |= 1 << j;
        if (rep[mask] < 0)
            rep[mask] = i;
    }
    /*@ Inv Assert
          exists (reps : list Z),
            a == a@pre && n == n@pre && m == m@pre &&
            x == x@pre && rep == rep@pre && bi == bi@pre && bj == bj@pre &&
            Pre(rows) &&
            1 <= n@pre && n@pre <= 300000 &&
            1 <= m@pre && m@pre <= 8 &&
            0 <= x@pre && x@pre <= 1000000000 &&
            n@pre == Zlength(rows) && m@pre == Zlength(rows[0]) &&
            Zlength(old_bi) == 1 && Zlength(old_bj) == 1 &&
            full == (1 << m@pre) - 1 && 0 <= full && full <= 255 &&
            0 <= s && s <= full + 1 && Zlength(reps) == 256 &&
            RepresentativePrefix(rows, x@pre, m@pre, n@pre, reps) &&
            NoCoverPrefix(reps, full, s, 0) &&
            (forall q, (0 <= q && q <= full) =>
               (-1 <= reps[q] && reps[q] < n@pre)) &&
            IntArray2::full(a@pre, n@pre, m@pre, rows) *
            IntArray::full(rep@pre, 256, reps) *
            IntArray::mixed_full(bi@pre, 1, old_bi) *
            IntArray::mixed_full(bj@pre, 1, old_bj)
     */
    for (int s = 0; s <= full; s++) {
        if (rep[s] < 0)
            continue;
        /*@ Inv Assert
              exists (reps : list Z),
                a == a@pre && n == n@pre && m == m@pre &&
                x == x@pre && rep == rep@pre && bi == bi@pre && bj == bj@pre &&
                Pre(rows) &&
                1 <= n@pre && n@pre <= 300000 &&
                1 <= m@pre && m@pre <= 8 &&
                0 <= x@pre && x@pre <= 1000000000 &&
                n@pre == Zlength(rows) && m@pre == Zlength(rows[0]) &&
                Zlength(old_bi) == 1 && Zlength(old_bj) == 1 &&
                full == (1 << m@pre) - 1 && 0 <= full && full <= 255 &&
                0 <= s && s <= full && 0 <= u && u <= full + 1 &&
                Zlength(reps) == 256 &&
                0 <= reps[s] && reps[s] < n@pre &&
                RepresentativePrefix(rows, x@pre, m@pre, n@pre, reps) &&
                NoCoverPrefix(reps, full, s, u) &&
                (forall q, (0 <= q && q <= full) =>
                   (-1 <= reps[q] && reps[q] < n@pre)) &&
                IntArray2::full(a@pre, n@pre, m@pre, rows) *
                IntArray::full(rep@pre, 256, reps) *
                IntArray::mixed_full(bi@pre, 1, old_bi) *
                IntArray::mixed_full(bj@pre, 1, old_bj)
        */
        for (int u = 0; u <= full; u++)
            if (rep[u] >= 0 && (s | u) == full) {
                /*@ IntArray::mixed_full(bi@pre, 1, old_bi) *
                    IntArray::mixed_full(bj@pre, 1, old_bj)
                    which implies
                    undef_data_at(bi@pre, int) *
                    undef_data_at(bj@pre, int)
                 */
                *bi = rep[s] + 1;
                *bj = rep[u] + 1;
                return 1;
            }
    }
    return 0;
}

/* solver: indices maximising min_k max(a_i[k], a_j[k]). */
static void solver(const int *a, int n, int m, int *rep, int *bi, int *bj)
/* QCP_INSERT_BEGIN:shard09-P066-solver-contract */
/*@ With (rows : list(list Z))
    Require
      Pre(rows) && 1 <= n && n <= 300000 && (forall i, (0 <= i && i < n) => (1 <= m && m <= 8)) && (forall k, (0 <= k && k < n * m) => (0 <= concat(rows)[k] && concat(rows)[k] <= 1000000000)) &&
      n == Zlength(rows) && m == Zlength(rows[0]) && IntArray2::full(a, n, m, rows) * IntArray::full_shape(rep, 256) * IntArray::undef_full(bi, 1) * IntArray::undef_full(bj, 1)
    Ensure
      exists (out : Z*Z),
        Spec(rows, out) &&
        IntArray2::full(a, n, m, rows) * IntArray::full_shape(rep, 256) * IntArray::full(bi, 1, cons(fst(out), nil)) * IntArray::full(bj, 1, cons(snd(out), nil))
*/
/* QCP_INSERT_END:shard09-P066-solver-contract */
{
    int lo = 0, hi = 1000000000;
    /*@ IntArray::undef_full(bi@pre, 1) * IntArray::undef_full(bj@pre, 1)
        which implies
        undef_data_at(bi@pre, int) * undef_data_at(bj@pre, int)
     */
    *bj = 1;
    *bi = *bj;
    /*@ Inv Assert
          exists cur_i cur_j,
            a == a@pre && n == n@pre && m == m@pre &&
            rep == rep@pre && bi == bi@pre && bj == bj@pre &&
            Pre(rows) &&
            1 <= n@pre && n@pre <= 300000 &&
            1 <= m@pre && m@pre <= 8 &&
            n@pre == Zlength(rows) && m@pre == Zlength(rows[0]) &&
            (forall k, (0 <= k && k < n@pre * m@pre) =>
               (0 <= concat(rows)[k] && concat(rows)[k] <= 1000000000)) &&
            0 <= lo && lo <= hi && hi <= 1000000000 &&
            0 <= cur_i && cur_i < n@pre &&
            0 <= cur_j && cur_j < n@pre &&
            SolverSearchMeaning(rows, lo, hi, cur_i, cur_j) &&
            IntArray2::full(a@pre, n@pre, m@pre, rows) *
            IntArray::full_shape(rep@pre, 256) *
            IntArray::full(bi@pre, 1, cons(cur_i + 1, nil)) *
            IntArray::full(bj@pre, 1, cons(cur_j + 1, nil))
     */
    while (lo < hi) {
        int mid = lo + (hi - lo + 1) / 2;
        int ci, cj;
        /*@ undef_data_at(&ci, int) * undef_data_at(&cj, int)
            which implies
            exists (ci_cells cj_cells : list(option Z)),
              Zlength(ci_cells) == 1 && Zlength(cj_cells) == 1 &&
              IntArray::mixed_full(&ci, 1, ci_cells) *
              IntArray::mixed_full(&cj, 1, cj_cells)
         */
        if (feasible(a, n, m, mid, rep, &ci, &cj)
              /*@ where rows = rows */) {
            /*@ exists (ci_values cj_values old_is old_js : list Z),
                  Zlength(ci_values) == 1 && Zlength(cj_values) == 1 &&
                  Zlength(old_is) == 1 && Zlength(old_js) == 1 &&
                  IntArray::full(&ci, 1, ci_values) *
                  IntArray::full(&cj, 1, cj_values) *
                  IntArray::full(bi@pre, 1, old_is) *
                  IntArray::full(bj@pre, 1, old_js)
                which implies
                  store(&ci, int, ci_values[0]) *
                  store(&cj, int, cj_values[0]) *
                  store(bi@pre, int, old_is[0]) *
                  store(bj@pre, int, old_js[0])
             */
            lo = mid;
            *bi = ci;
            *bj = cj;
        } else {
            hi = mid - 1;
            /*@ exists (ci_values cj_values : list(option Z)),
                  IntArray::mixed_full(&ci, 1, ci_values) *
                  IntArray::mixed_full(&cj, 1, cj_values)
                which implies
                  undef_data_at(&ci, int) * undef_data_at(&cj, int)
             */
        }
    }
    if (lo == 0)
        /*@ exists (bi_values bj_values : list Z),
              IntArray::full(bi@pre, 1, bi_values) *
              IntArray::full(bj@pre, 1, bj_values)
            which implies
            exists (bi_cells bj_cells : list(option Z)),
              Zlength(bi_cells) == 1 && Zlength(bj_cells) == 1 &&
              IntArray::mixed_full(bi@pre, 1, bi_cells) *
              IntArray::mixed_full(bj@pre, 1, bj_cells)
         */
        feasible(a, n, m, 0, rep, bi, bj)
          /*@ where rows = rows */;
}

// int main(void)
// {
//     int n, m;
//     if (scanf("%d %d", &n, &m) != 2)
//         return 0;
//     static int a[300005 * 8], rep[256];
//     for (int i = 0; i < n * m; i++)
//         scanf("%d", &a[i]);
//     int bi, bj;
//     solver(a, n, m, rep, &bi, &bj);
//     printf("%d %d\n", bi, bj);
//     return 0;
// }
