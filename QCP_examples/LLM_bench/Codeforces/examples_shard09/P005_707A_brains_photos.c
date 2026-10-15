/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_lib
*/

/*
 * Codeforces 707/A - Brain's Photos  (rating 800, IMPLEMENTATION)
 *
 * The photo is coloured iff at least one pixel is cyan, magenta or yellow;
 * white / grey / black alone make it black-and-white.
 */

// #include <stdio.h>
/*@ Extern Coq (bool :: *) */
/*@ Extern Coq
      (Spec : list (list Z) -> bool -> Prop)
      (SolverReturnBridge : bool -> Z -> Prop)
      (concat : {A} -> list (list A) -> list A)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P005_707A_brains_photos_lib */

/* solver: pure.  px holds n*m pixel letters; 1 if the photo is coloured. */

static int solver(const char *px, int n, int m)
/* QCP_INSERT_BEGIN:shard09-P005-solver-contract */
/*@ With (photo : list (list Z))
    Require
      1 <= n && n <= 100 &&
      1 <= m && m <= 100 &&
      n == Zlength(photo) &&
      (forall i, (0 <= i && i < n) => Zlength(photo[i]) == m) &&
      (forall i, (0 <= i && i < n) =>
        (forall j, (0 <= j && j < m) =>
          (photo[i][j] == 67 || photo[i][j] == 77 ||
           photo[i][j] == 89 || photo[i][j] == 87 ||
           photo[i][j] == 71 || photo[i][j] == 66))) &&
      CharArray::full(px, n * m, concat(photo))
    Ensure
      exists (out : bool),
        Spec(photo, out) &&
        SolverReturnBridge(out, __return) && CharArray::full(px, n * m, concat(photo))
*/
/* QCP_INSERT_END:shard09-P005-solver-contract */
{
    /*@ Inv Assert
          px == px@pre && n == n@pre && m == m@pre &&
          n@pre == Zlength(photo) &&
          1 <= n@pre && n@pre <= 100 &&
          1 <= m@pre && m@pre <= 100 &&
          (forall r, (0 <= r && r < n@pre) =>
            Zlength(photo[r]) == m@pre) &&
          (forall r, (0 <= r && r < n@pre) =>
            (forall c, (0 <= c && c < m@pre) =>
              (photo[r][c] == 67 || photo[r][c] == 77 ||
               photo[r][c] == 89 || photo[r][c] == 87 ||
               photo[r][c] == 71 || photo[r][c] == 66))) &&
          Zlength(concat(photo)) == n@pre * m@pre &&
          0 <= i && i <= n@pre * m@pre &&
          (forall k, (0 <= k && k < i) =>
            concat(photo)[k] != 67 &&
            concat(photo)[k] != 77 &&
            concat(photo)[k] != 89) &&
          CharArray::full(
            px@pre, n@pre * m@pre, concat(photo))
    */
    for (int i = 0; i < n * m; i++)
        if (px[i] == 'C' || px[i] == 'M' || px[i] == 'Y')
            return 1;
    return 0;
}

// int main(void)
// {
//     int n, m;
//     if (scanf("%d %d", &n, &m) != 2)
//         return 0;
//     static char px[10005];
//     for (int i = 0; i < n * m; i++)
//         scanf(" %c", &px[i]);
//     puts(solver(px, n, m) ? "#Color" : "#Black&White");
//     return 0;
// }
