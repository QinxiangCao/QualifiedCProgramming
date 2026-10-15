/* Codeforces 690/D1 - The Wall (easy) */
// #include <stdio.h>
#include "array2_ext_def.h"

/* QCP_INSERT_BEGIN:P029_690D1_the_wall_easy.support */
/*@ Extern Coq
      (Spec : Z -> Z -> list (list Z) -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P029_690D1_the_wall_easy_lib */
/* QCP_INSERT_END:P029_690D1_the_wall_easy.support */
/*@ Extern Coq
      (Pre : Z -> Z -> list (list Z) -> Prop)
      (WallColumnsAfterRows : list (list Z) -> Z -> list Z -> Prop)
      (WallColumnsDuringRow : list (list Z) -> Z -> Z -> list Z -> Prop)
      (SegmentCountPrefix : list (list Z) -> Z -> Z -> Prop)
*/
static int solver(const char grid[][105], int r, int c)/* QCP_INSERT_BEGIN:P029_690D1_the_wall_easy.contract */

/*@ With (grid_data : list (list Z))
             (grid_mem : list (list (option Z)))
    Require
      1 <= r && r <= 100 &&
      1 <= c && c <= 100 &&
      Zlength(grid_data) == r &&
      (forall i, (0 <= i && i < r) => Zlength(grid_data[i]) == c) &&
      (forall i j, (0 <= i && i < r && 0 <= j && j < c) =>
        ((Znth(j, Znth(i, grid_data, nil), 0) == 66) ||
         (Znth(j, Znth(i, grid_data, nil), 0) == 46))) &&
      Zlength(grid_mem) == r &&
      (forall i, (0 <= i && i < r) =>
        (Zlength(Znth(i, grid_mem, nil)) == 105 &&
         (forall j, (0 <= j && j < c) =>
           Znth(j, Znth(i, grid_mem, nil), None) ==
             Some(Znth(j, Znth(i, grid_data, nil), 0))) &&
         Znth(c, Znth(i, grid_mem, nil), None) == Some(0))) &&
      CharArray2::mixed_full(grid, r, 105, grid_mem)
    Ensure
      Spec(r, c, grid_data, __return) &&
      CharArray2::mixed_full(grid, r, 105, grid_mem)
*/
/* QCP_INSERT_END:P029_690D1_the_wall_easy.contract */

{
    int occupied[100] = {0};
    /*@ Inv Assert
          exists occupied_data,
            grid == grid@pre && r == r@pre && c == c@pre &&
            1 <= r@pre && r@pre <= 100 &&
            1 <= c@pre && c@pre <= 100 &&
            Pre(r@pre, c@pre, grid_data) &&
            Zlength(grid_mem) == r@pre &&
            (forall row, (0 <= row && row < r@pre) =>
              (Zlength(Znth(row, grid_mem, nil)) == 105 &&
               (forall col, (0 <= col && col < c@pre) =>
                 Znth(col, Znth(row, grid_mem, nil), None) ==
                   Some(Znth(col, Znth(row, grid_data, nil), 0))) &&
               Znth(c@pre, Znth(row, grid_mem, nil), None) == Some(0))) &&
            0 <= i && i <= r@pre &&
            WallColumnsAfterRows(grid_data, i, occupied_data) &&
            CharArray2::mixed_full(grid@pre, r@pre, 105, grid_mem) *
            IntArray::full(occupied, 100, occupied_data)
    */
    for (int i = 0; i < r; ++i)
        /*@ Inv Assert
              exists occupied_data,
                grid == grid@pre && r == r@pre && c == c@pre &&
                1 <= r@pre && r@pre <= 100 &&
                1 <= c@pre && c@pre <= 100 &&
                Pre(r@pre, c@pre, grid_data) &&
                Zlength(grid_mem) == r@pre &&
                (forall row, (0 <= row && row < r@pre) =>
                  (Zlength(Znth(row, grid_mem, nil)) == 105 &&
                   (forall col, (0 <= col && col < c@pre) =>
                     Znth(col, Znth(row, grid_mem, nil), None) ==
                       Some(Znth(col, Znth(row, grid_data, nil), 0))) &&
                   Znth(c@pre, Znth(row, grid_mem, nil), None) == Some(0))) &&
                0 <= i && i < r@pre &&
                0 <= j && j <= c@pre &&
                WallColumnsDuringRow(grid_data, i, j, occupied_data) &&
                CharArray2::mixed_full(grid@pre, r@pre, 105, grid_mem) *
                IntArray::full(occupied, 100, occupied_data)
        */
        for (int j = 0; j < c; ++j) {
            /*@ 0 <= i && i < r@pre && 0 <= j && j < c@pre &&
                Znth(j, Znth(i, grid_mem, nil), None) ==
                  Some(Znth(j, Znth(i, grid_data, nil), 0)) &&
                CharArray2::mixed_full(grid@pre, r@pre, 105, grid_mem)
                which implies
                0 <= i && i < r@pre && 0 <= j && j < c@pre &&
                Znth(j, Znth(i, grid_mem, nil), None) ==
                  Some(Znth(j, Znth(i, grid_data, nil), 0)) &&
                CharArray::mixed_full(grid@pre + i, 105,
                                      Znth(i, grid_mem, nil)) *
                CharArray2::mixed_missing_i(grid@pre, i, 0, r@pre, 105,
                                             grid_mem)
            */
            /*@ Assert
                  exists occupied_data cell,
                    grid == grid@pre && r == r@pre && c == c@pre &&
                    1 <= r@pre && r@pre <= 100 &&
                    1 <= c@pre && c@pre <= 100 &&
                    Pre(r@pre, c@pre, grid_data) &&
                    Zlength(grid_mem) == r@pre &&
                    (forall row, (0 <= row && row < r@pre) =>
                      (Zlength(Znth(row, grid_mem, nil)) == 105 &&
                       (forall col, (0 <= col && col < c@pre) =>
                         Znth(col, Znth(row, grid_mem, nil), None) ==
                           Some(Znth(col, Znth(row, grid_data, nil), 0))) &&
                       Znth(c@pre, Znth(row, grid_mem, nil), None) == Some(0))) &&
                    0 <= i && i < r@pre &&
                    0 <= j && j < c@pre &&
                    WallColumnsDuringRow(grid_data, i, j, occupied_data) &&
                    cell == Znth(j, Znth(i, grid_data, nil), 0) &&
                    Znth(j, Znth(i, grid_mem, nil), None) == Some(cell) &&
                    store(pointer_offset(grid@pre + i, j,
                                         sizeof(char), signed char),
                          char, cell) *
                    CharArray::mixed_missing_i(grid@pre + i, j, 0, 105,
                                                Znth(i, grid_mem, nil)) *
                    CharArray2::mixed_missing_i(grid@pre, i, 0, r@pre, 105,
                                                 grid_mem) *
                    IntArray::full(occupied, 100, occupied_data)
            */
            if (grid[i][j] == 'B') occupied[j] = 1;
            /*@ Assert
                  exists occupied_data,
                    grid == grid@pre && r == r@pre && c == c@pre &&
                    1 <= r@pre && r@pre <= 100 &&
                    1 <= c@pre && c@pre <= 100 &&
                    Pre(r@pre, c@pre, grid_data) &&
                    Zlength(grid_mem) == r@pre &&
                    (forall row, (0 <= row && row < r@pre) =>
                      (Zlength(Znth(row, grid_mem, nil)) == 105 &&
                       (forall col, (0 <= col && col < c@pre) =>
                         Znth(col, Znth(row, grid_mem, nil), None) ==
                           Some(Znth(col, Znth(row, grid_data, nil), 0))) &&
                       Znth(c@pre, Znth(row, grid_mem, nil), None) == Some(0))) &&
                    0 <= i && i < r@pre &&
                    0 <= j && j < c@pre &&
                    WallColumnsDuringRow(grid_data, i, j + 1, occupied_data) &&
                    CharArray2::mixed_full(grid@pre, r@pre, 105, grid_mem) *
                    IntArray::full(occupied, 100, occupied_data)
            */
        }
    int segments = 0;
    /*@ Inv Assert
          exists occupied_data,
            grid == grid@pre && r == r@pre && c == c@pre &&
            1 <= r@pre && r@pre <= 100 &&
            1 <= c@pre && c@pre <= 100 &&
            Pre(r@pre, c@pre, grid_data) &&
            Zlength(grid_mem) == r@pre &&
            (forall row, (0 <= row && row < r@pre) =>
              (Zlength(Znth(row, grid_mem, nil)) == 105 &&
               (forall col, (0 <= col && col < c@pre) =>
                 Znth(col, Znth(row, grid_mem, nil), None) ==
                   Some(Znth(col, Znth(row, grid_data, nil), 0))) &&
               Znth(c@pre, Znth(row, grid_mem, nil), None) == Some(0))) &&
            0 <= j && j <= c@pre &&
            0 <= segments && segments <= j &&
            WallColumnsAfterRows(grid_data, r@pre, occupied_data) &&
            SegmentCountPrefix(grid_data, j, segments) &&
            CharArray2::mixed_full(grid@pre, r@pre, 105, grid_mem) *
            IntArray::full(occupied, 100, occupied_data)
    */
    for (int j = 0; j < c; ++j)
        if (occupied[j] && (j == 0 || !occupied[j - 1])) ++segments;
    return segments;
}

// int main(void)
// {
//     int r, c; char grid[100][105];
//     if (scanf("%d %d", &r, &c) != 2) return 0;
//     for (int i = 0; i < r; ++i) scanf("%104s", grid[i]);
//     printf("%d\n", solver(grid, r, c));
//     return 0;
// }
