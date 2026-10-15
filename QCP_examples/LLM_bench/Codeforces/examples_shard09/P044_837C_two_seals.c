/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P044_837C_two_seals_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P044_837C_two_seals_lib
*/

/*
 * Codeforces 837/C - Two Seals  (rating 1500, BRUTE FORCE)
 *
 * n <= 100, so try every pair of seals and every combination of rotations.
 * Two axis-parallel rectangles fit on the sheet without overlapping iff they
 * can be stacked side by side or one above the other.
 */

// #include <stdio.h>

/* QCP_INSERT_BEGIN:shard09-P044-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P044_837C_two_seals_lib */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Spec : Z*Z -> list(Z*Z) -> Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P044-solver-support */

/*@ Extern Coq
      (FitsDims : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (BestBefore : Z*Z -> list(Z*Z) -> Z -> Z -> Z -> Z -> Z -> Prop)
*/

/* fits: can w1 x h1 and w2 x h2 sit inside a x b without overlapping? */
static int fits(int w1, int h1, int w2, int h2, int a, int b)
/*@ Require
      1 <= w1 && w1 <= 100 && 1 <= h1 && h1 <= 100 &&
      1 <= w2 && w2 <= 100 && 1 <= h2 && h2 <= 100 &&
      1 <= a && a <= 100 && 1 <= b && b <= 100 && emp
    Ensure
      ((__return == 1 && FitsDims(w1, h1, w2, h2, a, b)) ||
       (__return == 0 && (! FitsDims(w1, h1, w2, h2, a, b)))) && emp
*/
{
    if (w1 + w2 <= a && (h1 > h2 ? h1 : h2) <= b)
        return 1;                          /* side by side */
    if (h1 + h2 <= b && (w1 > w2 ? w1 : w2) <= a)
        return 1;                          /* stacked */
    return 0;
}

/* solver: pure.  Largest total area of two non-overlapping seals on a x b. */
static int solver(const int *x, const int *y, int n, int a, int b)
/* QCP_INSERT_BEGIN:shard09-P044-solver-contract */
/*@ With (paper : Z*Z) (seals : list(Z*Z))
    Require
      1 <= fst(paper) && fst(paper) <= 100 && 1 <= snd(paper) && snd(paper) <= 100 &&
      1 <= n && n <= 100 && (forall i, (0 <= i && i < n) => (1 <= fst(seals[i]) && fst(seals[i]) <= 100 && 1 <= snd(seals[i]) && snd(seals[i]) <= 100)) &&
      fst(paper) == a && snd(paper) == b && n == Zlength(seals) && exists (xs_spec : list Z) (ys_spec : list Z), Zlength(xs_spec) == n && Zlength(ys_spec) == n && (forall i, (0 <= i && i < n) => xs_spec[i] == fst(seals[i]) && ys_spec[i] == snd(seals[i])) && IntArray::full(x, n, xs_spec) * IntArray::full(y, n, ys_spec)
    Ensure
      Spec(paper, seals, __return) &&
      exists (xs_spec : list Z) (ys_spec : list Z), Zlength(xs_spec) == n && Zlength(ys_spec) == n && (forall i, (0 <= i && i < n) => xs_spec[i] == fst(seals[i]) && ys_spec[i] == snd(seals[i])) && IntArray::full(x, n, xs_spec) * IntArray::full(y, n, ys_spec)
*/
/* QCP_INSERT_END:shard09-P044-solver-contract */
{
    int best = 0;
    /*@ Inv Assert
          exists (xs_spec : list Z) (ys_spec : list Z),
            x == x@pre && y == y@pre && n == n@pre &&
            a == a@pre && b == b@pre &&
            1 <= fst(paper) && fst(paper) <= 100 &&
            1 <= snd(paper) && snd(paper) <= 100 &&
            1 <= n && n <= 100 &&
            fst(paper) == a && snd(paper) == b &&
            n == Zlength(seals) &&
            Zlength(xs_spec) == n && Zlength(ys_spec) == n &&
            (forall k, (0 <= k && k < n) =>
              (1 <= fst(seals[k]) && fst(seals[k]) <= 100 &&
               1 <= snd(seals[k]) && snd(seals[k]) <= 100 &&
               xs_spec[k] == fst(seals[k]) &&
               ys_spec[k] == snd(seals[k]))) &&
            0 <= i && i <= n && 0 <= best && best <= 20000 &&
            BestBefore(paper, seals, i, i + 1, 0, 0, best) &&
            IntArray::full(x, n, xs_spec) * IntArray::full(y, n, ys_spec)
     */
    for (int i = 0; i < n; i++)
        /*@ Inv Assert
              exists (xs_spec : list Z) (ys_spec : list Z),
                x == x@pre && y == y@pre && n == n@pre &&
                a == a@pre && b == b@pre &&
                1 <= fst(paper) && fst(paper) <= 100 &&
                1 <= snd(paper) && snd(paper) <= 100 &&
                1 <= n && n <= 100 &&
                fst(paper) == a && snd(paper) == b &&
                n == Zlength(seals) &&
                Zlength(xs_spec) == n && Zlength(ys_spec) == n &&
                (forall k, (0 <= k && k < n) =>
                  (1 <= fst(seals[k]) && fst(seals[k]) <= 100 &&
                   1 <= snd(seals[k]) && snd(seals[k]) <= 100 &&
                   xs_spec[k] == fst(seals[k]) &&
                   ys_spec[k] == snd(seals[k]))) &&
                0 <= i && i < n && i + 1 <= j && j <= n &&
                0 <= best && best <= 20000 &&
                BestBefore(paper, seals, i, j, 0, 0, best) &&
                IntArray::full(x, n, xs_spec) * IntArray::full(y, n, ys_spec)
         */
        for (int j = i + 1; j < n; j++)
            /*@ Inv Assert
                  exists (xs_spec : list Z) (ys_spec : list Z),
                    x == x@pre && y == y@pre && n == n@pre &&
                    a == a@pre && b == b@pre &&
                    1 <= fst(paper) && fst(paper) <= 100 &&
                    1 <= snd(paper) && snd(paper) <= 100 &&
                    1 <= n && n <= 100 &&
                    fst(paper) == a && snd(paper) == b &&
                    n == Zlength(seals) &&
                    Zlength(xs_spec) == n && Zlength(ys_spec) == n &&
                    (forall k, (0 <= k && k < n) =>
                      (1 <= fst(seals[k]) && fst(seals[k]) <= 100 &&
                       1 <= snd(seals[k]) && snd(seals[k]) <= 100 &&
                       xs_spec[k] == fst(seals[k]) &&
                       ys_spec[k] == snd(seals[k]))) &&
                    0 <= i && i < j && j < n &&
                    0 <= ri && ri <= 2 &&
                    0 <= best && best <= 20000 &&
                    BestBefore(paper, seals, i, j, ri, 0, best) &&
                    IntArray::full(x, n, xs_spec) * IntArray::full(y, n, ys_spec)
             */
            for (int ri = 0; ri < 2; ri++)
                /*@ Inv Assert
                      exists (xs_spec : list Z) (ys_spec : list Z),
                        x == x@pre && y == y@pre && n == n@pre &&
                        a == a@pre && b == b@pre &&
                        1 <= fst(paper) && fst(paper) <= 100 &&
                        1 <= snd(paper) && snd(paper) <= 100 &&
                        1 <= n && n <= 100 &&
                        fst(paper) == a && snd(paper) == b &&
                        n == Zlength(seals) &&
                        Zlength(xs_spec) == n && Zlength(ys_spec) == n &&
                        (forall k, (0 <= k && k < n) =>
                          (1 <= fst(seals[k]) && fst(seals[k]) <= 100 &&
                           1 <= snd(seals[k]) && snd(seals[k]) <= 100 &&
                           xs_spec[k] == fst(seals[k]) &&
                           ys_spec[k] == snd(seals[k]))) &&
                        0 <= i && i < j && j < n &&
                        0 <= ri && ri < 2 && 0 <= rj && rj <= 2 &&
                        0 <= best && best <= 20000 &&
                        BestBefore(paper, seals, i, j, ri, rj, best) &&
                        IntArray::full(x, n, xs_spec) * IntArray::full(y, n, ys_spec)
                 */
                for (int rj = 0; rj < 2; rj++) {
                    int w1 = ri ? y[i] : x[i], h1 = ri ? x[i] : y[i];
                    int w2 = rj ? y[j] : x[j], h2 = rj ? x[j] : y[j];
                    if (fits(w1, h1, w2, h2, a, b)) {
                        int area = w1 * h1 + w2 * h2;
                        if (area > best)
                            best = area;
                    }
                }
    return best;
}

// int main(void)
// {
//     int n, a, b;
//     if (scanf("%d %d %d", &n, &a, &b) != 3)
//         return 0;
//     static int x[105], y[105];
//     for (int i = 0; i < n; i++)
//         scanf("%d %d", &x[i], &y[i]);
//     printf("%d\n", solver(x, y, n, a, b));
//     return 0;
// }
