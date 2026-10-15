/*
 * Codeforces 1900/A - Cover in Water  (rating 800, CONSTRUCTIVE)
 *
 * Three consecutive empty cells act as a reusable pump: water at both ends of
 * the triple makes the middle fill by itself, so one unit is always free to be
 * carried on with action 2, sweeping the whole row.  Two cells are not enough —
 * nothing sits between them — so the answer is 2 exactly when some empty run
 * reaches length 3; otherwise every empty cell must be filled by hand.
 *
 * solver() takes one whole test case (the row) and returns the action count.
 */

// #include <stdio.h>
/* QCP_INSERT_BEGIN:shard03-P005-solver-support */

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard03.P005_1900A_cover_in_water_lib */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
*/

/* QCP_INSERT_END:shard03-P005-solver-support */

/* solver: pure.  Minimum number of type-1 actions for the row s of length n. */
static int solver(const char *s, int n)
/* QCP_INSERT_BEGIN:shard03-P005-solver-contract */
/*@ With (cells : list Z)
    Require
      1 <= n && n <= 100 && n == Zlength(cells) &&
      (forall i, (0 <= i && i < n) => (cells[i] == 46 || cells[i] == 35)) &&
      CharArray::full(s, n, cells)
    Ensure
      Spec(cells, __return) &&
      CharArray::full(s, n, cells)
*/
/* QCP_INSERT_END:shard03-P005-solver-contract */
{
    int empty = 0, run = 0, pump = 0;
    for (int i = 0; i < n; i++) {
        if (s[i] == '.') {
            empty++;
            run++;
            if (run >= 3)
                pump = 1;
        } else {
            run = 0;
        }
    }
    return pump ? 2 : empty;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         int n;
//         char s[105];
//         scanf("%d %104s", &n, s);
//         printf("%d\n", solver(s, n));
//     }
//     return 0;
// }
