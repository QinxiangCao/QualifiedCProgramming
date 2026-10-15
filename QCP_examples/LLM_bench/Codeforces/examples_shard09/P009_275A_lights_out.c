/*
 * Codeforces 275/A - Lights Out  (rating 900, IMPLEMENTATION)
 *
 * Only the parity of each press count matters.  A light ends up on iff it was
 * toggled an even number of times, i.e. the sum of presses on itself and its
 * four side-adjacent cells is even (all lights start on).
 */

// #include <stdio.h>
#include "array2_ext_def.h"
/*@ Extern Coq
      (Spec : list (list Z) -> list (list Z) -> Prop)
      (lights_di : list Z)
      (lights_dj : list Z)
      (TogglePrefix : list (list Z) -> Z -> Z -> Z -> Z -> Prop)
      (staged_output : list (list Z) -> Z -> list (list (option Z)))
      (out_grid : list (list Z) -> list (list Z))
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P009_275A_lights_out_lib */

/* solver: pure.  press[3][3] press counts -> out[3][3] final states 0/1. */
static void solver(const int press[3][3], int out[3][3])
/* QCP_INSERT_BEGIN:shard09-P009-solver-contract */
/*@ With (g : list (list Z))
    Require
      Zlength(g) == 3 && (forall i, (0 <= i && i < 3) => Zlength(g[i]) == 3) && (forall i, (0 <= i && i < 3) => (forall k, (0 <= k && k < 3) => (0 <= g[i][k] && g[i][k] <= 100))) &&
      IntArray2::full(press, 3, 3, g) * IntArray2::undef_full(out, 3, 3)
    Ensure
      exists (out_spec : list (list Z)),
        Spec(g, out_spec) &&
        IntArray2::full(press, 3, 3, g) * IntArray2::full(out, 3, 3, out_spec)
*/
/* QCP_INSERT_END:shard09-P009-solver-contract */
{
    const int di[5] = {0, -1, 1, 0, 0};
    const int dj[5] = {0, 0, 0, -1, 1};
    /*@ IntArray2::undef_full(out@pre, 3, 3)
        which implies
        IntArray2::mixed_full(out@pre, 3, 3, staged_output(g, 0))
    */
    /*@ Inv Assert
        press == press@pre && out == out@pre &&
          Zlength(g) == 3 &&
          (forall (r: Z), (0 <= r && r < 3) => Zlength(g[r]) == 3) &&
          (forall (r: Z) (c: Z),
            (0 <= r && r < 3 && 0 <= c && c < 3) =>
              (0 <= g[r][c] && g[r][c] <= 100)) &&
          0 <= i && i <= 3 &&
          IntArray::full(di, 5, lights_di) *
          IntArray::full(dj, 5, lights_dj) *
          IntArray2::full(press@pre, 3, 3, g) *
          IntArray2::mixed_full(out@pre, 3, 3, staged_output(g, 3 * i))
    */
    for (int i = 0; i < 3; i++)
        /*@ Inv Assert
            press == press@pre && out == out@pre &&
              Zlength(g) == 3 &&
              (forall (r: Z), (0 <= r && r < 3) => Zlength(g[r]) == 3) &&
              (forall (r: Z) (c: Z),
                (0 <= r && r < 3 && 0 <= c && c < 3) =>
                  (0 <= g[r][c] && g[r][c] <= 100)) &&
              0 <= i && i < 3 && 0 <= j && j <= 3 &&
              IntArray::full(di, 5, lights_di) *
              IntArray::full(dj, 5, lights_dj) *
              IntArray2::full(press@pre, 3, 3, g) *
              IntArray2::mixed_full(out@pre, 3, 3, staged_output(g, 3 * i + j))
        */
        for (int j = 0; j < 3; j++) {
            int tog = 0;
            /*@ Inv Assert
                press == press@pre && out == out@pre &&
                  Zlength(g) == 3 &&
                  (forall (r: Z), (0 <= r && r < 3) => Zlength(g[r]) == 3) &&
                  (forall (r: Z) (c: Z),
                    (0 <= r && r < 3 && 0 <= c && c < 3) =>
                      (0 <= g[r][c] && g[r][c] <= 100)) &&
                  0 <= i && i < 3 && 0 <= j && j < 3 &&
                  0 <= d && d <= 5 && 0 <= tog && tog <= 500 &&
                  TogglePrefix(g, i, j, d, tog) &&
                  IntArray::full(di, 5, lights_di) *
                  IntArray::full(dj, 5, lights_dj) *
                  IntArray2::full(press@pre, 3, 3, g) *
                  IntArray2::mixed_full(out@pre, 3, 3, staged_output(g, 3 * i + j))
            */
            for (int d = 0; d < 5; d++) {
                int ni = i + di[d], nj = j + dj[d];
                if (ni >= 0 && ni < 3 && nj >= 0 && nj < 3)
                    tog += press[ni][nj];
            }
            out[i][j] = (tog % 2 == 0);       /* started on */
        }
}

// int main(void)
// {
//     int press[3][3], out[3][3];
//     for (int i = 0; i < 3; i++)
//         for (int j = 0; j < 3; j++)
//             if (scanf("%d", &press[i][j]) != 1)
//                 return 0;
//     solver(press, out);
//     for (int i = 0; i < 3; i++) {
//         for (int j = 0; j < 3; j++)
//             putchar('0' + out[i][j]);
//         putchar('\n');
//     }
//     return 0;
// }
