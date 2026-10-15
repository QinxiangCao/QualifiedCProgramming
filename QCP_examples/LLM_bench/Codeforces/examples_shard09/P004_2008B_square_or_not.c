/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P004_2008B_square_or_not_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P004_2008B_square_or_not_lib
*/

/*
 * Codeforces 2008/B - Square or Not  (rating 800, STRINGS)
 *
 * The matrix is square iff n is a perfect square r*r and the string, read as
 * an r x r grid, is 1 exactly on the border and 0 strictly inside.
 */

// #include <stdio.h>
/*@ Extern Coq 
        (Pre : list Z -> Prop)
        (Spec : list Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P004_2008B_square_or_not_lib */


/* solver: pure.  1 if s (length n) can come from a square beautiful matrix. */
static int solver(const char *s, int n)
/* QCP_INSERT_BEGIN:shard09-P004-solver-contract */
/*@ With (bits : list Z)
    Require
      2 <= n && n <= 200000 &&
      Zlength(bits) == n &&
      (forall i, (0 <= i && i < n) =>
        (bits[i] == 48 || bits[i] == 49)) &&
      Pre(bits) &&
      CharArray::full(s, n, bits)
    Ensure
      Spec(bits, __return) &&
      CharArray::full(s, n, bits)
*/
/* QCP_INSERT_END:shard09-P004-solver-contract */
{
    int r = 0;
    /*@ Inv Assert
          s == s@pre && n == n@pre &&
          2 <= n@pre && n@pre <= 200000 &&
          Zlength(bits) == n@pre &&
          (forall k, (0 <= k && k < n@pre) =>
            (bits[k] == 48 || bits[k] == 49)) &&
          Pre(bits) &&
          0 <= r && r <= 447 &&
          r * r <= n@pre &&
          CharArray::full(s@pre, n@pre, bits)
    */
    while ((r + 1) * (r + 1) <= n)
        r++;
    if (r * r != n)
        return 0;
    /*@ Inv Assert
          s == s@pre && n == n@pre &&
          2 <= n@pre && n@pre <= 200000 &&
          Zlength(bits) == n@pre &&
          (forall k, (0 <= k && k < n@pre) =>
            (bits[k] == 48 || bits[k] == 49)) &&
          Pre(bits) &&
          1 <= r && r <= 447 &&
          r * r == n@pre &&
          0 <= i && i <= r &&
          (forall (x : Z) (y : Z),
            (0 <= x && x < i && 0 <= y && y < r) =>
              (((x == 0 || x == r - 1 || y == 0 || y == r - 1) &&
                bits[x * r + y] == 49) ||
               ((x != 0 && x != r - 1 && y != 0 && y != r - 1) &&
                bits[x * r + y] == 48))) &&
          CharArray::full(s@pre, n@pre, bits)
    */
    for (int i = 0; i < r; i++)
        /*@ Inv Assert
              s == s@pre && n == n@pre &&
              2 <= n@pre && n@pre <= 200000 &&
              Zlength(bits) == n@pre &&
              (forall k, (0 <= k && k < n@pre) =>
                (bits[k] == 48 || bits[k] == 49)) &&
              Pre(bits) &&
              1 <= r && r <= 447 &&
              r * r == n@pre &&
              0 <= i && i < r &&
              0 <= j && j <= r &&
              (forall (x : Z) (y : Z),
                (0 <= x && x < i && 0 <= y && y < r) =>
                  (((x == 0 || x == r - 1 || y == 0 || y == r - 1) &&
                    bits[x * r + y] == 49) ||
                   ((x != 0 && x != r - 1 && y != 0 && y != r - 1) &&
                    bits[x * r + y] == 48))) &&
              (forall y,
                (0 <= y && y < j) =>
                  (((i == 0 || i == r - 1 || y == 0 || y == r - 1) &&
                    bits[i * r + y] == 49) ||
                   ((i != 0 && i != r - 1 && y != 0 && y != r - 1) &&
                    bits[i * r + y] == 48))) &&
              CharArray::full(s@pre, n@pre, bits)
        */
        for (int j = 0; j < r; j++) {
            int border = (i == 0 || i == r - 1 || j == 0 || j == r - 1);
            char want = border ? '1' : '0';
            /*@ 0 <= i * r + j && i * r + j < n by local */
            if (s[i * r + j] != want)
                return 0;
        }
    return 1;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         int n;
//         static char s[200005];
//         scanf("%d %200004s", &n, s);
//         puts(solver(s, n) ? "Yes" : "No");
//     }
//     return 0;
// }
