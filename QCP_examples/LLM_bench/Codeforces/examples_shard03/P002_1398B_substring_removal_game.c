/*
 * Codeforces 1398/B - Substring Removal Game  (rating 800, GREEDY)
 *
 * Deleting zeros never scores, so both players race for the blocks of ones.
 * A whole block is always taken at once — leaving part of it only hands the
 * rest to the opponent — so the blocks are consumed largest first, alternating,
 * and Alice collects the 1st, 3rd, 5th ... largest.
 *
 * solver() takes one whole test case (the binary string) and returns Alice's
 * final score; main() only reads and prints.
 */

#include <stdio.h>
#include <stdlib.h>
/* QCP_INSERT_BEGIN:shard03-P002-solver-support */

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard03.P002_1398B_substring_removal_game */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
*/

/* QCP_INSERT_END:shard03-P002-solver-support */

static int cmp_desc(const void *x, const void *y)
{
    int a = *(const int *)x, b = *(const int *)y;
    return (a < b) - (a > b);
}

/* solver: pure.  Alice's score on the binary string s of length n. */
static int solver(const char *s, int n)
/* QCP_INSERT_BEGIN:shard03-P002-solver-contract */
/*@ With (str : list Z)
    Require
      1 <= n && n <= 100 && n == Zlength(str) &&
      (forall i, (0 <= i && i < n) => (str[i] == 48 || str[i] == 49)) &&
      CharArray::full(s, n, str)
    Ensure
      Spec(str, __return) &&
      CharArray::full(s, n, str)
*/
/* QCP_INSERT_END:shard03-P002-solver-contract */
{
    int blocks[105], nb = 0;
    for (int i = 0; i < n; ) {
        if (s[i] != '1') {
            i++;
            continue;
        }
        int j = i;
        while (j < n && s[j] == '1')
            j++;
        blocks[nb] = j - i;
        nb++;
        i = j;
    }
    qsort(blocks, nb, sizeof *blocks, cmp_desc);
    int score = 0;
    for (int i = 0; i < nb; i += 2)       /* Alice moves first */
        score += blocks[i];
    return score;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         char s[105];
//         int n = 0;
//         scanf("%104s", s);
//         while (s[n])
//             n++;
//         printf("%d\n", solver(s, n));
//     }
//     return 0;
// }
