/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P021_602A_two_bases_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P021_602A_two_bases_lib
*/

/*
 * Codeforces 602/A - Two Bases  (rating 1100, IMPLEMENTATION)
 *
 * Both numbers have at most 10 digits in a base below 40, so their values fit
 * comfortably in a 64-bit integer (40^10 < 1.1e16); convert and compare.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Pre : Z -> Z -> list Z -> list Z -> Prop)
      (Spec : Z -> Z -> list Z -> list Z -> Z -> Prop)
      (SolverReturnBridge : Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P021_602A_two_bases_lib */
/*@ Extern Coq
      (numeral : Z -> list Z -> Z)
      (Z::pow : Z -> Z -> Z)
*/

/* solver: pure.  Value of the digit string d[0..n-1] (most significant first)
 * read in base b. */
static long long numeral_value(const int *d, int n, int b)
/*@ With (digits : list Z)
    Require
      1 <= n && n <= 10 &&
      2 <= b && b <= 40 &&
      n == Zlength(digits) &&
      (forall k, (0 <= k && k < n) =>
        (0 <= digits[k] && digits[k] < b)) &&
      IntArray::full(d, n, digits)
    Ensure
      __return == numeral(b, digits) &&
      IntArray::full(d, n, digits)
*/
{
    long long v = 0;
    /*@ Inv Assert
          d == d@pre && n == n@pre && b == b@pre &&
          1 <= n@pre && n@pre <= 10 &&
          2 <= b@pre && b@pre <= 40 &&
          n@pre == Zlength(digits) &&
          (forall k, (0 <= k && k < n@pre) =>
            (0 <= digits[k] && digits[k] < b@pre)) &&
          0 <= i && i <= n@pre &&
          v == numeral(b@pre, sublist(0, i, digits)) &&
          0 <= v && v <= Z::pow(40, i) - 1 &&
          IntArray::full(d@pre, n@pre, digits)
    */
    for (int i = 0; i < n; i++)
        v = v * b + d[i];
    return v;
}

/* solver: complete case.  Return the ASCII comparison character required by
 * the statement, so its result has exactly the boundary of Spec. */
static int solver(int bx, int basey, const int *x, int n,
                  const int *y, int m)
/* QCP_INSERT_BEGIN:shard09-P021-normalized-solver-contract */
/*@ With (x_digits : list Z) (y_digits : list Z)
    Require
      1 <= n && n <= 10 && 1 <= m && m <= 10 &&
      2 <= bx && bx <= 40 && 2 <= basey && basey <= 40 &&
      (forall i, (0 <= i && i < n) => (0 <= x_digits[i] && x_digits[i] < bx)) &&
      (forall i, (0 <= i && i < m) => (0 <= y_digits[i] && y_digits[i] < basey)) &&
      Pre(bx, basey, x_digits, y_digits) && n == Zlength(x_digits) && m == Zlength(y_digits) && IntArray::full(x, n, x_digits) * IntArray::full(y, m, y_digits)
    Ensure
      Spec(bx, basey, x_digits, y_digits, __return) && IntArray::full(x, n, x_digits) * IntArray::full(y, m, y_digits)
*/
/* QCP_INSERT_END:shard09-P021-normalized-solver-contract */
{
    long long vx = numeral_value(x, n, bx) /*@ where digits = x_digits */;
    long long vy = numeral_value(y, m, basey) /*@ where digits = y_digits */;
    return vx < vy ? '<' : vx > vy ? '>' : '=';
}

// int main(void)
// {
//     int n, bx, m, by;
//     static int x[15], y[15];
//     if (scanf("%d %d", &n, &bx) != 2)
//         return 0;
//     for (int i = 0; i < n; i++)
//         scanf("%d", &x[i]);
//     scanf("%d %d", &m, &by);
//     for (int i = 0; i < m; i++)
//         scanf("%d", &y[i]);
//     putchar(solver(bx, by, x, n, y, m));
//     putchar('\n');
//     return 0;
// }
