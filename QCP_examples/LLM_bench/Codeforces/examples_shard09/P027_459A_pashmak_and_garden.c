/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_lib
*/

/*
 * Codeforces 459/A - Pashmak and Garden  (rating 1200, IMPLEMENTATION)
 *
 * Two vertices of an axis-parallel square are either on a common side (they
 * share x or share y, and the square extends sideways by the side length) or
 * they are diagonal (|dx| == |dy|, and the other two corners swap coordinates).
 * Anything else is impossible.
 */

// #include <stdio.h>
// #include <stdlib.h>
/*@ Extern Coq
      (Pre : Z -> Z -> Z -> Z -> Prop)
      (NoCompletion : Z -> Z -> Z -> Z -> Prop)
      (CompletesSquare : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P027_459A_pashmak_and_garden_lib */

/*@ Extern Coq (Z::abs : Z -> Z) */

static int iabs(int x)
/*@ Require
      -200 <= x && x <= 200 && emp
    Ensure
      __return == Z::abs(x@pre) && emp
 */
{
    return x < 0 ? -x : x;
}

/* solver: pure.  Fills out[4] with x3,y3,x4,y4 and returns 1, or returns 0 if
 * no square exists. */
static int solver(int x1, int y1, int x2, int y2, int *out)
/* QCP_INSERT_BEGIN:shard09-P027-solver-contract */
/*@ Require
      -100 <= x1 && x1 <= 100 &&
      -100 <= y1 && y1 <= 100 &&
      -100 <= x2 && x2 <= 100 &&
      -100 <= y2 && y2 <= 100 &&
      Pre(x1, y1, x2, y2) &&
      IntArray::undef_full(out, 4)
    Ensure
      (__return == 0 &&
       NoCompletion(x1@pre, y1@pre, x2@pre, y2@pre) &&
       IntArray::undef_full(out@pre, 4)) ||
      (exists (x3 : Z) (y3 : Z) (x4 : Z) (y4 : Z),
       __return == 1 &&
       CompletesSquare(x1@pre, y1@pre, x2@pre, y2@pre, x3, y3, x4, y4) &&
       IntArray::full(out@pre, 4, cons(x3, cons(y3, cons(x4, cons(y4, nil))))))
*/
/* QCP_INSERT_END:shard09-P027-solver-contract */
{
    if (x1 == x2) {                       /* vertical side, length |dy| */
        int d = iabs(y1 - y2);
        out[0] = x1 + d; out[1] = y1;
        out[2] = x2 + d; out[3] = y2;
        return 1;
    }
    if (y1 == y2) {                       /* horizontal side */
        int d = iabs(x1 - x2);
        out[0] = x1; out[1] = y1 + d;
        out[2] = x2; out[3] = y2 + d;
        return 1;
    }
    if (iabs(x1 - x2) == iabs(y1 - y2)) {   /* diagonal */
        out[0] = x1; out[1] = y2;
        out[2] = x2; out[3] = y1;
        return 1;
    }
    return 0;
}

// int main(void)
// {
//     int x1, y1, x2, y2, out[4];
//     if (scanf("%d %d %d %d", &x1, &y1, &x2, &y2) != 4)
//         return 0;
//     if (solver(x1, y1, x2, y2, out))
//         printf("%d %d %d %d\n", out[0], out[1], out[2], out[3]);
//     else
//         puts("-1");
//     return 0;
// }
