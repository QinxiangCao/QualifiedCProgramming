/* Codeforces 1941/D - Rudolf and the Ball Game */
// #include <stdio.h>
#include "string.h"

/* QCP_INSERT_BEGIN:P028_1941D_rudolf_and_the_ball_game.support */
/*@ Extern Coq
      (fst : {A} {B} -> A * B -> A)
      (snd : {A} {B} -> A * B -> B)
      (Spec : Z -> Z -> list (Z * Z) -> list Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
      (IntArray::undef_full : Z -> Z -> Assertion)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (CharArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P028_1941D_rudolf_and_the_ball_game_lib */
/* QCP_INSERT_END:P028_1941D_rudolf_and_the_ball_game.support */
static int solver(int n, int m, int start, const int *distance, const char *direction,
                  int *holders) /* QCP_INSERT_BEGIN:P028_1941D_rudolf_and_the_ball_game.contract */

/*@ With (throws : list (Z * Z))
             (distance_data direction_data : list Z)
    Require
      2 <= n && n <= 1000 &&
      1 <= Zlength(throws) && Zlength(throws) <= 1000 &&
      1 <= start && start <= n &&
      (forall i, (0 <= i && i < Zlength(throws)) => ((1 <= fst(throws[i]) && fst(throws[i]) < n) && ((snd(throws[i]) == 48) || (snd(throws[i]) == 49) || (snd(throws[i]) == 63)))) &&
      m == Zlength(throws) &&
      Zlength(distance_data) == m && Zlength(direction_data) == m &&
      (forall i, (0 <= i && i < m) =>
        (distance_data[i] == fst(throws[i]) &&
         direction_data[i] == snd(throws[i]))) &&
      IntArray::full(distance, m, distance_data) *
      IntArray::undef_seg(distance, m, 1000) *
      CharArray::full(direction, m, direction_data) *
      CharArray::undef_seg(direction, m, 1000) *
      IntArray::undef_full(holders, 1000)
    Ensure
      exists out,
        Spec(n, start, throws, out) &&
        __return == Zlength(out) &&
        IntArray::full(distance, m, distance_data) *
        IntArray::undef_seg(distance, m, 1000) *
        CharArray::full(direction, m, direction_data) *
        CharArray::undef_seg(direction, m, 1000) *
        IntArray::full(holders, Zlength(out), out) *
        IntArray::undef_seg(holders, Zlength(out), 1000)
*/
/* QCP_INSERT_END:P028_1941D_rudolf_and_the_ball_game.contract */

{
    unsigned char cur[1000] = {0}, next[1000];
    cur[start - 1] = 1;
    for (int move = 0; move < m; ++move)
    {
        int r = distance[move];
        char c = direction[move];
        memset(next, 0, (size_t)n);
        for (int p = 0; p < n; ++p)
            if (cur[p])
            {
                if (c != '1')
                    next[(p + r) % n] = 1;
                if (c != '0')
                    next[(p - r % n + n) % n] = 1;
            }
        memcpy(cur, next, (size_t)n);
    }
    int count = 0;
    for (int i = 0; i < n; ++i)
        if (cur[i])
            holders[count++] = i + 1;
    return count;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n, m, x, distance[1000], holders[1000]; char direction[1000];
//         scanf("%d %d %d", &n, &m, &x);
//         for (int move = 0; move < m; ++move) {
//             scanf("%d %c", &distance[move], &direction[move]);
//         }
//         int count = solver(n, m, x, distance, direction, holders);
//         printf("%d\n", count);
//         for (int i = 0; i < count; ++i) printf("%d ", holders[i]);
//         putchar('\n');
//     }
//     return 0;
// }
