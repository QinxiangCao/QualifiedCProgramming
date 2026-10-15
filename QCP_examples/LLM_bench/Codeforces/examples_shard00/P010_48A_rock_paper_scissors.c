/* Codeforces 48/A - Rock-paper-scissors */
// #include <stdio.h>
#include "string.h"
#include "array2_ext_def.h"

/*@ Extern Coq
      (rock : list Z)
      (paper : list Z)
      (scissors : list Z)
      (Gesture : list Z -> Prop)
      (Beats : list Z -> list Z -> Prop)
      (Pre : list Z -> list Z -> list Z -> Prop)
*/

static int beats(const char g[3][16], int ia, int ib)
/*@ With (players : list (list Z))
         (game_mem : list (list (option Z)))
    Require
      0 <= ia && ia < 3 && 0 <= ib && ib < 3 && ia != ib &&
      Zlength(players) == 3 &&
      Pre(Znth(0, players, nil), Znth(1, players, nil), Znth(2, players, nil)) &&
      Zlength(game_mem) == 3 &&
      (forall row, (0 <= row && row < 3) =>
        (0 < Zlength(Znth(row, players, nil)) &&
         Zlength(Znth(row, players, nil)) < 16 &&
         Zlength(Znth(row, game_mem, nil)) == 16 &&
         (forall col, (0 <= col && col < Zlength(Znth(row, players, nil))) =>
           Znth(col, Znth(row, game_mem, nil), None) ==
             Some(Znth(col, Znth(row, players, nil), 0))) &&
         Znth(Zlength(Znth(row, players, nil)),
              Znth(row, game_mem, nil), None) == Some(0))) &&
      CharArray2::mixed_full(g, 3, 16, game_mem)
    Ensure
      0 <= __return && __return <= 1 &&
      (__return != 0 => Beats(Znth(ia, players, nil), Znth(ib, players, nil))) &&
      (__return == 0 => ! Beats(Znth(ia, players, nil), Znth(ib, players, nil))) &&
      CharArray2::mixed_full(g, 3, 16, game_mem)
*/
{
    char ac = g[ia][0];
    char bc = g[ib][0];
    return (ac == 'r' && bc == 's') ||
           (ac == 's' && bc == 'p') ||
           (ac == 'p' && bc == 'r');
}

/* QCP_INSERT_BEGIN:P010_48A_rock_paper_scissors.support */
/*@ Extern Coq
      (Pre : list Z -> list Z -> list Z -> Prop)
      (Spec : list Z -> list Z -> list Z -> list Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P010_48A_rock_paper_scissors_lib */
/* QCP_INSERT_END:P010_48A_rock_paper_scissors.support */
static char solver(const char g[3][16])/* QCP_INSERT_BEGIN:P010_48A_rock_paper_scissors.contract */

/*@ With (players : list (list Z))
             (game_mem : list (list (option Z)))
    Require
      Zlength(players) == 3 &&
      Pre(Znth(0, players, nil), Znth(1, players, nil), Znth(2, players, nil)) &&
      Zlength(game_mem) == 3 &&
      (forall i, (0 <= i && i < 3) =>
        (Zlength(Znth(i, players, nil)) < 16 &&
         Zlength(Znth(i, game_mem, nil)) == 16 &&
         (forall j, (0 <= j && j < Zlength(Znth(i, players, nil))) =>
           Znth(j, Znth(i, game_mem, nil), None) ==
             Some(Znth(j, Znth(i, players, nil), 0))) &&
         Znth(Zlength(Znth(i, players, nil)), Znth(i, game_mem, nil), None) == Some(0))) &&
      CharArray2::mixed_full(g, 3, 16, game_mem)
    Ensure
      exists result,
        Spec(Znth(0, players, nil), Znth(1, players, nil),
             Znth(2, players, nil), result) && __return == result[0] &&
        CharArray2::mixed_full(g, 3, 16, game_mem)
*/
/* QCP_INSERT_END:P010_48A_rock_paper_scissors.contract */

{
    /*@ Inv Assert
          g == g@pre &&
          0 <= i && i <= 3 &&
          Zlength(players) == 3 &&
          Pre(Znth(0, players, nil), Znth(1, players, nil), Znth(2, players, nil)) &&
          Zlength(game_mem) == 3 &&
          (forall row, (0 <= row && row < 3) =>
            (Zlength(Znth(row, players, nil)) < 16 &&
             Zlength(Znth(row, game_mem, nil)) == 16 &&
             (forall col, (0 <= col && col < Zlength(Znth(row, players, nil))) =>
               Znth(col, Znth(row, game_mem, nil), None) ==
                 Some(Znth(col, Znth(row, players, nil), 0))) &&
             Znth(Zlength(Znth(row, players, nil)),
                  Znth(row, game_mem, nil), None) == Some(0))) &&
          (forall k, (0 <= k && k < i) =>
            !(Beats(Znth(k, players, nil), Znth((k + 1) % 3, players, nil)) &&
              Beats(Znth(k, players, nil), Znth((k + 2) % 3, players, nil)))) &&
          CharArray2::mixed_full(g, 3, 16, game_mem)
    */
    for (int i = 0; i < 3; ++i)
        if (beats(g, i, (i + 1) % 3)
              /*@ where players = players, game_mem = game_mem */ &&
            beats(g, i, (i + 2) % 3)
              /*@ where players = players, game_mem = game_mem */)
            return i == 0 ? 'F' : (i == 1 ? 'M' : 'S');
    return '?';
}

// int main(void)
// {
//     char g[3][16];
//     if (scanf("%15s %15s %15s", g[0], g[1], g[2]) != 3) return 0;
//     printf("%c\n", solver(g));
//     return 0;
// }
