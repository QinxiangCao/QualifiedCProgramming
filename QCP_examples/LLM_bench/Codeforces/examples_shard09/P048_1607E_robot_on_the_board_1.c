/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P048_1607E_robot_on_the_board_1_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P048_1607E_robot_on_the_board_1_lib
*/

/*
 * Codeforces 1607/E - Robot on the Board 1  (rating 1600, IMPLEMENTATION)
 *
 * Track the robot's offset from its start and the running min/max of that
 * offset.  A prefix is survivable iff its row span is < n and column span < m;
 * take the longest such prefix and place the start so the visited window sits
 * flush inside the board.
 */

// #include <stdio.h>

/* QCP_INSERT_BEGIN:shard09-P048-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P048_1607E_robot_on_the_board_1_lib */
/*@ Extern Coq
      (fst : {A B} -> A * B -> A)
      (snd : {A B} -> A * B -> B)
      (Spec : Z -> Z -> list Z -> Z*Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P048-solver-support */

/*@ Extern Coq
      (PrefixWindow : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (WindowFits : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (OptimalPrefixWindow : Z -> Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
*/

/* solver: pure.  Best starting cell (1-based) for command string s. */
static void solver(const char *s, int n, int m, int *row, int *col)
/* QCP_INSERT_BEGIN:shard09-P048-solver-contract */
/*@ With (moves : list Z)
    Require
      1 <= n && n <= 1000000 && 1 <= m && m <= 1000000 &&
      1 <= Zlength(moves) && Zlength(moves) <= 1000000 && (forall i, (0 <= i && i < Zlength(moves)) => (moves[i] == 76 || moves[i] == 82 || moves[i] == 68 || moves[i] == 85)) &&
      CharArray::full(s, Zlength(moves) + 1, app(moves, cons(0, nil))) * IntArray::undef_full(row, 1) * IntArray::undef_full(col, 1)
    Ensure
      exists (out : Z*Z),
        Spec(n, m, moves, out) &&
        CharArray::full(s, Zlength(moves) + 1, app(moves, cons(0, nil))) * IntArray::full(row, 1, cons(fst(out), nil)) * IntArray::full(col, 1, cons(snd(out), nil))
*/
/* QCP_INSERT_END:shard09-P048-solver-contract */
{
    int r = 0, c = 0;
    int minr = 0, maxr = 0, minc = 0, maxc = 0;
    int br = 0, bc = 0;                    /* answer for the longest prefix */
    /*@ IntArray::undef_full(row, 1) * IntArray::undef_full(col, 1)
        which implies
        undef_data_at(row, int) * undef_data_at(col, int)
    */
    *row = 1 - br;
    *col = 1 - bc;
    /*@ Inv Assert
        s == s@pre && n == n@pre && m == m@pre &&
        row == row@pre && col == col@pre &&
        1 <= n && n <= 1000000 && 1 <= m && m <= 1000000 &&
        1 <= Zlength(moves) && Zlength(moves) <= 1000000 &&
        (forall k,
          (0 <= k && k < Zlength(moves)) =>
          (moves[k] == 76 || moves[k] == 82 || moves[k] == 68 || moves[k] == 85)) &&
        0 <= i && i <= Zlength(moves) &&
        -i <= r && r <= i && -i <= c && c <= i &&
        -i <= minr && minr <= 0 && 0 <= maxr && maxr <= i &&
        -i <= minc && minc <= 0 && 0 <= maxc && maxc <= i &&
        br == 0 && bc == 0 &&
        PrefixWindow(moves, i, r, c, minr, maxr, minc, maxc) &&
        WindowFits(n, m, minr, maxr, minc, maxc) &&
        CharArray::full(s, Zlength(moves) + 1, app(moves, cons(0, nil))) *
        IntArray::full(row, 1, cons(1, nil)) *
        IntArray::full(col, 1, cons(1, nil))
    */
    for (int i = 0; s[i]; i++) {
        switch (s[i]) {
        case 'U': r--; break;
        case 'D': r++; break;
        case 'L': c--; break;
        default:  c++; break;
        }
        int nminr = r < minr ? r : minr, nmaxr = r > maxr ? r : maxr;
        int nminc = c < minc ? c : minc, nmaxc = c > maxc ? c : maxc;
        /*@ Assert
            exists oldr oldc,
              s == s@pre && n == n@pre && m == m@pre &&
              row == row@pre && col == col@pre &&
              1 <= n && n <= 1000000 && 1 <= m && m <= 1000000 &&
              1 <= Zlength(moves) && Zlength(moves) <= 1000000 &&
              (forall k,
                (0 <= k && k < Zlength(moves)) =>
                (moves[k] == 76 || moves[k] == 82 || moves[k] == 68 || moves[k] == 85)) &&
              0 <= i && i < Zlength(moves) &&
              -(i + 1) <= r && r <= i + 1 &&
              -(i + 1) <= c && c <= i + 1 &&
              -i <= minr && minr <= 0 && 0 <= maxr && maxr <= i &&
              -i <= minc && minc <= 0 && 0 <= maxc && maxc <= i &&
              -(i + 1) <= nminr && nminr <= 0 &&
              0 <= nmaxr && nmaxr <= i + 1 &&
              -(i + 1) <= nminc && nminc <= 0 &&
              0 <= nmaxc && nmaxc <= i + 1 &&
              br == 0 && bc == 0 &&
              PrefixWindow(moves, i, oldr, oldc, minr, maxr, minc, maxc) &&
              WindowFits(n, m, minr, maxr, minc, maxc) &&
              PrefixWindow(moves, i + 1, r, c, nminr, nmaxr, nminc, nmaxc) &&
              CharArray::full(s, Zlength(moves) + 1, app(moves, cons(0, nil))) *
              IntArray::full(row, 1, cons(1, nil)) *
              IntArray::full(col, 1, cons(1, nil))
        */
        if (nmaxr - nminr >= n || nmaxc - nminc >= m)
            break;                         /* this command would break it */
        minr = nminr; maxr = nmaxr;
        minc = nminc; maxc = nmaxc;
    }
    /*@ Assert
        s == s@pre && n == n@pre && m == m@pre &&
        row == row@pre && col == col@pre &&
        1 <= n && n <= 1000000 && 1 <= m && m <= 1000000 &&
        1 <= Zlength(moves) && Zlength(moves) <= 1000000 &&
        (forall k,
          (0 <= k && k < Zlength(moves)) =>
          (moves[k] == 76 || moves[k] == 82 || moves[k] == 68 || moves[k] == 85)) &&
        -Zlength(moves) <= r && r <= Zlength(moves) &&
        -Zlength(moves) <= c && c <= Zlength(moves) &&
        -Zlength(moves) <= minr && minr <= 0 &&
        0 <= maxr && maxr <= Zlength(moves) &&
        -Zlength(moves) <= minc && minc <= 0 &&
        0 <= maxc && maxc <= Zlength(moves) &&
        br == 0 && bc == 0 &&
        OptimalPrefixWindow(n, m, moves, minr, maxr, minc, maxc) &&
        CharArray::full(s, Zlength(moves) + 1, app(moves, cons(0, nil))) *
        IntArray::full(row, 1, cons(1, nil)) *
        IntArray::full(col, 1, cons(1, nil))
    */
    /*@ IntArray::full(row, 1, cons(1, nil)) *
        IntArray::full(col, 1, cons(1, nil))
        which implies
        store(row, int, 1) * store(col, int, 1)
    */
    br = minr;
    bc = minc;
    *row = 1 - br;                         /* shift the window to the top-left */
    *col = 1 - bc;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static char s[1000006];
//     while (t--) {
//         int n, m, row, col;
//         scanf("%d %d %1000005s", &n, &m, s);
//         solver(s, n, m, &row, &col);
//         printf("%d %d\n", row, col);
//     }
//     return 0;
// }
