/*
 * Codeforces 2042/B - Game with Colored Marbles  (rating 900, GAMES)
 *
 * A colour with two or more marbles is worth exactly 1 to Alice: she can
 * always grab one, and Bob can always deny her the rest.  Colours with a single
 * marble are worth 2 each and are contested one at a time, so Alice secures
 * ceil(u/2) of them.
 *
 * solver() takes one whole test case (all marble colours) and returns the score.
 */

// #include <stdio.h>
// #include <string.h>

/* QCP_INSERT_BEGIN:shard03-P009-solver-support */

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard03.P009_2042B_game_with_colored_marbles_lib */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
*/

/* QCP_INSERT_END:shard03-P009-solver-support */
static void *memset(void *dst, int c, unsigned long n)
/*@ Require
      0 <= n && c == 0 && 
      UCharArray::undef_full(dst, n)
    Ensure
      __return == dst && 
      UCharArray::full(dst, n, repeat_Z(0, n))
*/;

static int cnt[1005];

/* solver: reads no input.  Alice's optimal score for the colours c[0..n-1].
 * Writes the file-scope work array `cnt`. */

static int solver(const int *c, int n)
/* QCP_INSERT_BEGIN:shard03-P009-solver-contract */
/*@ With (colours : list Z)
    Require
      1 <= n && n <= 1000 && n == Zlength(colours) &&
      (forall i, (0 <= i && i < n) => (1 <= colours[i] && colours[i] <= n)) &&
      IntArray::full(c, n, colours) * IntArray::undef_full(cnt, n + 2)
    Ensure
      Spec(colours, __return) &&
      IntArray::full(c, n, colours) * IntArray::full_shape(cnt, n + 2)
*/
/* QCP_INSERT_END:shard03-P009-solver-contract */
{
    memset(cnt, 0, sizeof(int) * (n + 2));
    for (int i = 0; i < n; i++)
        cnt[c[i]]++;
    int unique = 0, shared = 0;
    for (int v = 1; v <= n; v++) {
        if (cnt[v] == 1)
            unique++;
        else if (cnt[v] > 1)
            shared++;
    }
    return 2 * ((unique + 1) / 2) + shared;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static int c[1005];
//     while (t--) {
//         int n;
//         scanf("%d", &n);
//         for (int i = 0; i < n; i++)
//             scanf("%d", &c[i]);
//         printf("%d\n", solver(c, n));
//     }
//     return 0;
// }
