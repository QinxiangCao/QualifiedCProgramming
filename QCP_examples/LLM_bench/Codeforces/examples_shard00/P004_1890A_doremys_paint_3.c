/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P004_1890A_doremys_paint_3_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P004_1890A_doremys_paint_3_lib
*/

/* Codeforces 1890/A - Doremy's Paint 3 */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P004_1890A_doremys_paint_3.support */
/*@ Extern Coq
      (Spec : list Z -> Z -> Prop)
      (IntArray::full : Z -> Z -> list Z -> Assertion)
      (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P004_1890A_doremys_paint_3_lib */
/*@ Extern Coq
      (PaintScanState : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/
/* QCP_INSERT_END:P004_1890A_doremys_paint_3.support */
static int solver(const int *a, int n) /* QCP_INSERT_BEGIN:P004_1890A_doremys_paint_3.contract */

/*@ With (input : list Z)
    Require
      n == Zlength(input) &&
      2 <= Zlength(input) && Zlength(input) <= 100 &&
      (forall idx, (0 <= idx && idx < Zlength(input)) =>
        (1 <= input[idx] && input[idx] <= 100000)) &&
      IntArray::full(a, n, input) * IntArray::undef_seg(a, n, 100)
    Ensure
      Spec(input, __return) &&
      IntArray::full(a, n, input) * IntArray::undef_seg(a, n, 100)
*/
/* QCP_INSERT_END:P004_1890A_doremys_paint_3.contract */

{
    int x = a[0], y = -1, cx = 0, cy = 0;
    /*@ Inv Assert
          a == a@pre && n == n@pre &&
          n == Zlength(input) &&
          2 <= n && n <= 100 &&
          0 <= i && i <= n &&
          (forall idx, (0 <= idx && idx < n) =>
            (1 <= input[idx] && input[idx] <= 100000)) &&
          PaintScanState(input, i, x, y, cx, cy) &&
          IntArray::full(a, n, input) * IntArray::undef_seg(a, n, 100)
    */
    for (int i = 0; i < n; ++i)
    {
        if (a[i] == x)
            ++cx;
        else if (y == -1 || a[i] == y)
        {
            y = a[i];
            ++cy;
        }
        else
            return 0;
    }
    return cy == 0 || (cx - cy <= 1 && cy - cx <= 1);
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n, a[100]; scanf("%d", &n);
//         for (int i = 0; i < n; ++i) scanf("%d", &a[i]);
//         puts(solver(a, n) ? "YES" : "NO");
//     }
//     return 0;
// }
