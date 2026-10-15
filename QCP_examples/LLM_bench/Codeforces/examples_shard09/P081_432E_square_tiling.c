/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
*/

/*
 * Codeforces 432/E - Square Tiling  (rating 2300, GREEDY)
 *
 * Fill the cells in reading order.  An empty cell takes the smallest letter
 * that clashes with none of its already painted neighbours — squares placed
 * earlier can sit above, to the left, and (having grown downwards) also to the
 * right or below.  Then grow the square while it stays inside the table,
 * covers only empty cells, keeps every neighbouring cell legal, and actually
 * helps: that is, while the next cell of this row would otherwise be forced to
 * take a bigger letter.
 */

// #include <stdio.h>
// #include <stdlib.h>

/* QCP_INSERT_BEGIN:shard09-P081-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib */
/*@ Extern Coq
      (Spec : Z -> Z -> list(list Z) -> Prop)
      (concat : {A} -> list(list A) -> list A)
*/
/* QCP_INSERT_END:shard09-P081-solver-support */

/*@ Extern Coq
      (NeighborConflict : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (LeastLegalColor : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (CanPlace : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/

/*@ Extern Coq
      (CanonicalGrid : list Z -> Prop)
*/

/*@ Extern Coq
      (ZeroPrefix : list Z -> Z -> Prop)
      (NoConflictBelow : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (EmptySquarePrefix : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (HorizontalBoundaryClearPrefix : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (VerticalBoundaryClearPrefix : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (PartialTilingState : Z -> Z -> Z -> list Z -> Prop)
      (NoPlaceableColorBelow : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (GreedySideState : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (PaintRectanglePrefix : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/

/*@ Extern Coq
      (CommittedFrontierState : Z -> Z -> Z -> list Z -> Prop)
      (ChosenSquareState : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/

/*@ Extern Coq
      (SettledSquareState : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (GreedyPlacementTrace : Z -> Z -> Z -> list Z -> Prop)
*/

#define MAXN 105

/* conflicts: is colour c already used by a painted neighbour of (i,j)?
 * left_override replaces the left neighbour when it is about to become c. */
static int conflicts(const char *g, int n, int m,
                     int i, int j, char c, char left_override)
/*@ With (flat : list Z)
    Require
      1 <= n && n <= 100 && 1 <= m && m <= 100 &&
      0 <= i && i < n && 0 <= j && j < m &&
      65 <= c && c <= 90 && 0 <= left_override && left_override <= 90 &&
      Zlength(flat) == n * m && CanonicalGrid(flat) &&
      CharArray::full(g, n * m, flat)
    Ensure
      ((__return == 1 &&
        NeighborConflict(flat, n, m, i, j, c, left_override)) ||
       (__return == 0 &&
        (! NeighborConflict(flat, n, m, i, j, c, left_override)))) &&
      CanonicalGrid(flat) &&
      CharArray::full(g, n * m, flat)
*/
{
    /*@ (i > 0 =>
          (0 <= (i - 1) * m + j && (i - 1) * m + j < n * m)) &&
        (i + 1 < n =>
          (0 <= (i + 1) * m + j && (i + 1) * m + j < n * m)) &&
        (j + 1 < m =>
          (0 <= i * m + j + 1 && i * m + j + 1 < n * m)) &&
        (j > 0 =>
          (0 <= i * m + j - 1 && i * m + j - 1 < n * m)) */
    if (i > 0 && g[(i - 1) * m + j] == c) return 1;
    if (i + 1 < n && g[(i + 1) * m + j] == c) return 1;
    if (j + 1 < m && g[i * m + j + 1] == c) return 1;
    if (j > 0) {
        char left = left_override ? left_override : g[i * m + j - 1];
        if (left == c) return 1;
    } else if (left_override == c) {
        return 1;
    }
    return 0;
}

/* cell_colour: smallest legal letter for the empty cell (i,j). */
static char cell_colour(const char *g, int n, int m,
                        int i, int j, char left_override)
/*@ With (flat : list Z)
    Require
      1 <= n && n <= 100 && 1 <= m && m <= 100 &&
      0 <= i && i < n && 0 <= j && j < m &&
      0 <= left_override && left_override <= 90 &&
      Zlength(flat) == n * m && CanonicalGrid(flat) &&
      CharArray::full(g, n * m, flat)
    Ensure
      LeastLegalColor(flat, n, m, i, j, left_override, __return) &&
      CanonicalGrid(flat) &&
      CharArray::full(g, n * m, flat)
*/
{
    /*@ Inv Assert
          g == g@pre && n == n@pre && m == m@pre &&
          i == i@pre && j == j@pre && left_override == left_override@pre &&
          1 <= n@pre && n@pre <= 100 &&
          1 <= m@pre && m@pre <= 100 &&
          0 <= i@pre && i@pre < n@pre &&
          0 <= j@pre && j@pre < m@pre &&
          0 <= left_override@pre && left_override@pre <= 90 &&
          65 <= c && c <= 91 &&
          Zlength(flat) == n@pre * m@pre &&
          CanonicalGrid(flat) &&
          NoConflictBelow(flat, n@pre, m@pre, i@pre, j@pre,
                          left_override@pre, c) &&
          CharArray::full(g@pre, n@pre * m@pre, flat)
    */
    for (char c = 'A'; c <= 'Z'; c++)
        if (!conflicts(g, n, m, i, j, c, left_override)
              /*@ where flat = flat */)
            return c;
    return 'Z';
}

/* can_place: may a square of side s coloured c start at (i,j)? */
static int can_place(const char *g, int n, int m,
                     int i, int j, int s, char c)
/*@ With (flat : list Z)
    Require
      1 <= n && n <= 100 && 1 <= m && m <= 100 &&
      0 <= i && i < n && 0 <= j && j < m &&
      1 <= s && s <= 101 && 65 <= c && c <= 90 &&
      Zlength(flat) == n * m && CanonicalGrid(flat) &&
      CharArray::full(g, n * m, flat)
    Ensure
      ((__return == 1 && CanPlace(flat, n, m, i, j, s, c)) ||
       (__return == 0 && (! CanPlace(flat, n, m, i, j, s, c)))) &&
      CanonicalGrid(flat) &&
      CharArray::full(g, n * m, flat)
*/
{
    if (i + s > n || j + s > m)
        return 0;
    /*@ Inv Assert
          g == g@pre && n == n@pre && m == m@pre &&
          i == i@pre && j == j@pre && s == s@pre && c == c@pre &&
          1 <= n@pre && n@pre <= 100 &&
          1 <= m@pre && m@pre <= 100 &&
          0 <= i@pre && i@pre < n@pre &&
          0 <= j@pre && j@pre < m@pre &&
          1 <= s@pre && s@pre <= 101 &&
          65 <= c@pre && c@pre <= 90 &&
          i@pre + s@pre <= n@pre && j@pre + s@pre <= m@pre &&
          i@pre <= r && r <= i@pre + s@pre &&
          Zlength(flat) == n@pre * m@pre &&
          CanonicalGrid(flat) &&
          EmptySquarePrefix(flat, m@pre, i@pre, j@pre, s@pre,
                            (r - i@pre) * s@pre) &&
          CharArray::full(g@pre, n@pre * m@pre, flat)
    */
    for (int r = i; r < i + s; r++)
        /*@ Inv Assert
              g == g@pre && n == n@pre && m == m@pre &&
              i == i@pre && j == j@pre && s == s@pre && c == c@pre &&
              1 <= n@pre && n@pre <= 100 &&
              1 <= m@pre && m@pre <= 100 &&
              0 <= i@pre && i@pre < n@pre &&
              0 <= j@pre && j@pre < m@pre &&
              1 <= s@pre && s@pre <= 101 &&
              65 <= c@pre && c@pre <= 90 &&
              i@pre + s@pre <= n@pre && j@pre + s@pre <= m@pre &&
              i@pre <= r && r < i@pre + s@pre &&
              j@pre <= q && q <= j@pre + s@pre &&
              (q < j@pre + s@pre =>
                (0 <= r * m@pre + q && r * m@pre + q < n@pre * m@pre)) &&
              Zlength(flat) == n@pre * m@pre &&
              CanonicalGrid(flat) &&
              EmptySquarePrefix(flat, m@pre, i@pre, j@pre, s@pre,
                                (r - i@pre) * s@pre + (q - j@pre)) &&
              CharArray::full(g@pre, n@pre * m@pre, flat)
        */
        for (int q = j; q < j + s; q++)
            if (g[r * m + q])
                return 0;
    /*@ Inv Assert
          g == g@pre && n == n@pre && m == m@pre &&
          i == i@pre && j == j@pre && s == s@pre && c == c@pre &&
          1 <= n@pre && n@pre <= 100 &&
          1 <= m@pre && m@pre <= 100 &&
          0 <= i@pre && i@pre < n@pre &&
          0 <= j@pre && j@pre < m@pre &&
          1 <= s@pre && s@pre <= 101 &&
          65 <= c@pre && c@pre <= 90 &&
          i@pre + s@pre <= n@pre && j@pre + s@pre <= m@pre &&
          j@pre <= q && q <= j@pre + s@pre &&
          (q < j@pre + s@pre && i@pre > 0 =>
            (0 <= (i@pre - 1) * m@pre + q &&
             (i@pre - 1) * m@pre + q < n@pre * m@pre)) &&
          (q < j@pre + s@pre && i@pre + s@pre < n@pre =>
            (0 <= (i@pre + s@pre) * m@pre + q &&
             (i@pre + s@pre) * m@pre + q < n@pre * m@pre)) &&
          Zlength(flat) == n@pre * m@pre &&
          CanonicalGrid(flat) &&
          EmptySquarePrefix(flat, m@pre, i@pre, j@pre, s@pre,
                            s@pre * s@pre) &&
          HorizontalBoundaryClearPrefix(flat, n@pre, m@pre,
            i@pre, j@pre, s@pre, c@pre, q - j@pre) &&
          CharArray::full(g@pre, n@pre * m@pre, flat)
    */
    for (int q = j; q < j + s; q++) {          /* rows above and below */
        if (i > 0 && g[(i - 1) * m + q] == c) return 0;
        if (i + s < n && g[(i + s) * m + q] == c) return 0;
    }
    /*@ Inv Assert
          g == g@pre && n == n@pre && m == m@pre &&
          i == i@pre && j == j@pre && s == s@pre && c == c@pre &&
          1 <= n@pre && n@pre <= 100 &&
          1 <= m@pre && m@pre <= 100 &&
          0 <= i@pre && i@pre < n@pre &&
          0 <= j@pre && j@pre < m@pre &&
          1 <= s@pre && s@pre <= 101 &&
          65 <= c@pre && c@pre <= 90 &&
          i@pre + s@pre <= n@pre && j@pre + s@pre <= m@pre &&
          i@pre <= r && r <= i@pre + s@pre &&
          (r < i@pre + s@pre && j@pre > 0 =>
            (0 <= r * m@pre + j@pre - 1 &&
             r * m@pre + j@pre - 1 < n@pre * m@pre)) &&
          (r < i@pre + s@pre && j@pre + s@pre < m@pre =>
            (0 <= r * m@pre + j@pre + s@pre &&
             r * m@pre + j@pre + s@pre < n@pre * m@pre)) &&
          Zlength(flat) == n@pre * m@pre &&
          CanonicalGrid(flat) &&
          EmptySquarePrefix(flat, m@pre, i@pre, j@pre, s@pre,
                            s@pre * s@pre) &&
          HorizontalBoundaryClearPrefix(flat, n@pre, m@pre,
            i@pre, j@pre, s@pre, c@pre, s@pre) &&
          VerticalBoundaryClearPrefix(flat, n@pre, m@pre,
            i@pre, j@pre, s@pre, c@pre, r - i@pre) &&
          CharArray::full(g@pre, n@pre * m@pre, flat)
    */
    for (int r = i; r < i + s; r++) {          /* columns left and right */
        if (j > 0 && g[r * m + j - 1] == c) return 0;
        if (j + s < m && g[r * m + j + s] == c) return 0;
    }
    return 1;
}

/* solver: paints the whole n x m table. */
static void solver(int n, int m, char *g)
/* QCP_INSERT_BEGIN:shard09-P081-normalized-solver-contract */
/*@ Require
      1 <= n && n <= 100 && 1 <= m && m <= 100 && CharArray::full_shape(g, n * m)
    Ensure
      exists (out : list(list Z)), Spec(n, m, out) &&
        CharArray::full(g, n * m, concat(out))
*/
/* QCP_INSERT_END:shard09-P081-normalized-solver-contract */
{
    /*@ Inv Assert
          n == n@pre && m == m@pre && g == g@pre &&
          1 <= n@pre && n@pre <= 100 &&
          1 <= m@pre && m@pre <= 100 &&
          0 <= i && i <= n@pre &&
          exists flat,
            Zlength(flat) == n@pre * m@pre &&
            ZeroPrefix(flat, i * m@pre) &&
            CharArray::full(g@pre, n@pre * m@pre, flat)
    */
    for (int i = 0; i < n; i++)
        /*@ Inv Assert
              n == n@pre && m == m@pre && g == g@pre &&
              1 <= n@pre && n@pre <= 100 &&
              1 <= m@pre && m@pre <= 100 &&
              0 <= i && i < n@pre && 0 <= j && j <= m@pre &&
              (j < m@pre =>
                (0 <= i * m@pre + j && i * m@pre + j < n@pre * m@pre)) &&
              exists flat,
                Zlength(flat) == n@pre * m@pre &&
                ZeroPrefix(flat, i * m@pre + j) &&
                CharArray::full(g@pre, n@pre * m@pre, flat)
        */
        for (int j = 0; j < m; j++)
            g[i * m + j] = 0;
    /*@ Inv Assert
          n == n@pre && m == m@pre && g == g@pre &&
          1 <= n@pre && n@pre <= 100 &&
          1 <= m@pre && m@pre <= 100 &&
          0 <= i && i <= n@pre &&
          exists grid,
            Zlength(grid) == n@pre * m@pre &&
            CanonicalGrid(grid) &&
            GreedyPlacementTrace(n@pre, m@pre, i * m@pre, grid) &&
            CharArray::full(g@pre, n@pre * m@pre, grid)
    */
    for (int i = 0; i < n; i++)
        /*@ Inv Assert
              n == n@pre && m == m@pre && g == g@pre &&
              1 <= n@pre && n@pre <= 100 &&
              1 <= m@pre && m@pre <= 100 &&
              0 <= i && i < n@pre && 0 <= j && j <= m@pre &&
              (j < m@pre =>
                (0 <= i * m@pre + j && i * m@pre + j < n@pre * m@pre)) &&
              exists grid,
                Zlength(grid) == n@pre * m@pre &&
                CanonicalGrid(grid) &&
                GreedyPlacementTrace(n@pre, m@pre,
                                     i * m@pre + j, grid) &&
                CharArray::full(g@pre, n@pre * m@pre, grid)
        */
        for (int j = 0; j < m; j++) {
            if (g[i * m + j])
                /*@ Assert
                      n == n@pre && m == m@pre && g == g@pre &&
                      1 <= n@pre && n@pre <= 100 &&
                      1 <= m@pre && m@pre <= 100 &&
                      0 <= i && i < n@pre && 0 <= j && j < m@pre &&
                      exists grid,
                        Zlength(grid) == n@pre * m@pre &&
                        CanonicalGrid(grid) &&
                        GreedyPlacementTrace(n@pre, m@pre,
                                             i * m@pre + j + 1, grid) &&
                        CharArray::full(g@pre, n@pre * m@pre, grid)
                */
                continue;
            char c = 0;
            /*@ Inv Assert
                  n == n@pre && m == m@pre && g == g@pre &&
                  1 <= n@pre && n@pre <= 100 &&
                  1 <= m@pre && m@pre <= 100 &&
                  0 <= i && i < n@pre && 0 <= j && j < m@pre &&
                  65 <= t && t <= 91 && c == 0 &&
                  exists grid,
                    Zlength(grid) == n@pre * m@pre &&
                    CanonicalGrid(grid) &&
                    Znth(i * m@pre + j, grid, 0) == 0 &&
                    GreedyPlacementTrace(n@pre, m@pre,
                                         i * m@pre + j, grid) &&
                    NoPlaceableColorBelow(grid, n@pre, m@pre, i, j, t) &&
                    (exists available,
                       65 <= available && available <= 69 &&
                       CanPlace(grid, n@pre, m@pre, i, j, 1, available)) &&
                    CharArray::full(g@pre, n@pre * m@pre, grid)
            */
            for (char t = 'A'; t <= 'Z'; t++)
                if (can_place(g, n, m, i, j, 1, t)) {
                    c = t;
                    /*@ Assert
                          n == n@pre && m == m@pre && g == g@pre &&
                          1 <= n@pre && n@pre <= 100 &&
                          1 <= m@pre && m@pre <= 100 &&
                          0 <= i && i < n@pre && 0 <= j && j < m@pre &&
                          65 <= t && t <= 91 &&
                          exists grid,
                            Zlength(grid) == n@pre * m@pre &&
                            CanonicalGrid(grid) &&
                            Znth(i * m@pre + j, grid, 0) == 0 &&
                            GreedyPlacementTrace(n@pre, m@pre,
                                                 i * m@pre + j, grid) &&
                            NoPlaceableColorBelow(grid, n@pre, m@pre,
                                                  i, j, c) &&
                            CanPlace(grid, n@pre, m@pre, i, j, 1, c) &&
                            LeastLegalColor(grid, n@pre, m@pre,
                                            i, j, 0, c) &&
                            CharArray::full(g@pre, n@pre * m@pre, grid)
                    */
                    /*@ Branch name colour_found */
                    break;
                }
            /*@ Branch clear unnamed */
            int size = 1;
            /*@ Inv Assert
                  n == n@pre && m == m@pre && g == g@pre &&
                  1 <= n@pre && n@pre <= 100 &&
                  1 <= m@pre && m@pre <= 100 &&
                  0 <= i && i < n@pre && 0 <= j && j < m@pre &&
                  65 <= c && c <= 90 &&
                  1 <= size && size <= n@pre - i && size <= m@pre - j &&
                  exists grid,
                    Zlength(grid) == n@pre * m@pre &&
                    CanonicalGrid(grid) &&
                    Znth(i * m@pre + j, grid, 0) == 0 &&
                    GreedyPlacementTrace(n@pre, m@pre,
                                         i * m@pre + j, grid) &&
                    LeastLegalColor(grid, n@pre, m@pre, i, j, 0, c) &&
                    GreedySideState(grid, n@pre, m@pre, i, j, c, size) &&
                    ChosenSquareState(grid, n@pre, m@pre,
                                      i, j, c, size) &&
                    CharArray::full(g@pre, n@pre * m@pre, grid)
            */
            while (j + size < m && can_place(g, n, m, i, j, size + 1, c)) {
                /* would the next cell of this row settle for something worse? */
                if (cell_colour(g, n, m, i, j + size, c) > c)
                    size++;
                else
                    break;
            }
            /*@ Assert
                  n == n@pre && m == m@pre && g == g@pre &&
                  1 <= n@pre && n@pre <= 100 &&
                  1 <= m@pre && m@pre <= 100 &&
                  0 <= i && i < n@pre && 0 <= j && j < m@pre &&
                  65 <= c && c <= 90 &&
                  1 <= size && size <= n@pre - i && size <= m@pre - j &&
                  exists grid,
                    Zlength(grid) == n@pre * m@pre &&
                    CanonicalGrid(grid) &&
                    Znth(i * m@pre + j, grid, 0) == 0 &&
                    GreedyPlacementTrace(n@pre, m@pre,
                                         i * m@pre + j, grid) &&
                    SettledSquareState(grid, n@pre, m@pre,
                                       i, j, c, size) &&
                    CharArray::full(g@pre, n@pre * m@pre, grid)
            */
            /*@ Inv Assert
                  n == n@pre && m == m@pre && g == g@pre &&
                  1 <= n@pre && n@pre <= 100 &&
                  1 <= m@pre && m@pre <= 100 &&
                  0 <= i && i < n@pre && 0 <= j && j < m@pre &&
                  65 <= c && c <= 90 &&
                  1 <= size && size <= n@pre - i && size <= m@pre - j &&
                  i <= r && r <= i + size &&
                  exists before current,
                    Zlength(before) == n@pre * m@pre &&
                    Zlength(current) == n@pre * m@pre &&
                    CanonicalGrid(before) && CanonicalGrid(current) &&
                    Znth(i * m@pre + j, before, 0) == 0 &&
                    GreedyPlacementTrace(n@pre, m@pre,
                                         i * m@pre + j, before) &&
                    SettledSquareState(before, n@pre, m@pre,
                                       i, j, c, size) &&
                    PaintRectanglePrefix(before, current, m@pre, i, j, size, c,
                                         (r - i) * size) &&
                    CharArray::full(g@pre, n@pre * m@pre, current)
            */
            for (int r = i; r < i + size; r++)
                /*@ Inv Assert
                      n == n@pre && m == m@pre && g == g@pre &&
                      1 <= n@pre && n@pre <= 100 &&
                      1 <= m@pre && m@pre <= 100 &&
                      0 <= i && i < n@pre && 0 <= j && j < m@pre &&
                      65 <= c && c <= 90 &&
                      1 <= size && size <= n@pre - i && size <= m@pre - j &&
                      i <= r && r < i + size && j <= q && q <= j + size &&
                      (q < j + size =>
                        (0 <= r * m@pre + q && r * m@pre + q < n@pre * m@pre)) &&
                      exists before current,
                        Zlength(before) == n@pre * m@pre &&
                        Zlength(current) == n@pre * m@pre &&
                        CanonicalGrid(before) && CanonicalGrid(current) &&
                        Znth(i * m@pre + j, before, 0) == 0 &&
                        GreedyPlacementTrace(n@pre, m@pre,
                                             i * m@pre + j, before) &&
                        SettledSquareState(before, n@pre, m@pre,
                                           i, j, c, size) &&
                        PaintRectanglePrefix(before, current, m@pre, i, j, size, c,
                          (r - i) * size + (q - j)) &&
                        CharArray::full(g@pre, n@pre * m@pre, current)
                */
                for (int q = j; q < j + size; q++)
                    g[r * m + q] = c;
        }
}

// int main(void)
// {
//     int n, m;
//     if (scanf("%d %d", &n, &m) != 2)
//         return 0;
//     char *g = malloc(sizeof(char) * (size_t)n * m);
//     solver(n, m, g);
//     for (int i = 0; i < n; i++) {
//         for (int j = 0; j < m; j++)
//             putchar(g[i * m + j]);
//         putchar('\n');
//     }
//     return 0;
// }
