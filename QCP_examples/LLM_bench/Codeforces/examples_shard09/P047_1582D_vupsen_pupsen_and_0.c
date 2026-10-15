/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P047_1582D_vupsen_pupsen_and_0_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P047_1582D_vupsen_pupsen_and_0_lib
*/

/*
 * Codeforces 1582/D - Vupsen, Pupsen and 0  (rating 1600, CONSTRUCTIVE)
 *
 * Pair the entries up: (a, b) is cancelled by (b/g, -a/g) with g = gcd, which
 * is non-zero and keeps the values small.  An odd length leaves a leading
 * triple: pick two of its three entries whose sum is non-zero, say a1 + a2,
 * and answer (a3, a3, -(a1+a2)) — always non-zero and summing to 0.
 */

// #include <stdio.h>
// #include <stdlib.h>

/* QCP_INSERT_BEGIN:shard09-P047-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P047_1582D_vupsen_pupsen_and_0_lib */
/*@ Extern Coq
      (Spec : list Z -> list Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P047-solver-support */

/*@ Extern Coq
      (Z::abs : Z -> Z)
      (GcdValue : Z -> Z -> Z)
      (OutputPrefix : list Z -> list Z -> Z -> Prop)
*/


static long long llabs(long long x)
/*@ Require
      -10000 <= x && x <= 10000 && emp
    Ensure
      __return == Z::abs(x@pre) && emp
*/
{
    return x < 0 ? -x : x;
}


static long long gcdll(long long a, long long b)
/*@ Require
      1 <= a && a <= 10000 && 1 <= b && b <= 10000 && emp
    Ensure
      __return == GcdValue(a@pre, b@pre) && emp
*/
{
    /*@ Inv Assert
      1 <= a && a <= 10000 &&
      0 <= b && b <= 10000 &&
      GcdValue(a, b) == GcdValue(a@pre, b@pre) && emp
    */
    while (b) {
        long long r = a % b;
        a = b;
        b = r;
    }
    return a < 0 ? -a : a;
}

/* pair_fill: cancels the pair (a, b) into b_out[0], b_out[1]. */
static void pair_fill(long long a, long long b, long long *out)
/*@ Require
      -10000 <= a && a <= 10000 && a != 0 &&
      -10000 <= b && b <= 10000 && b != 0 &&
      Int64Array::undef_full(out, 2)
    Ensure
      exists (pair_out : list Z),
        OutputPrefix(cons(a@pre, cons(b@pre, nil)), pair_out, 0) &&
        Int64Array::full(out, 2, pair_out)
*/
{
    long long g = gcdll(llabs(a), llabs(b));
    out[0] = b / g;
    out[1] = -a / g;
}

/* solver: pure.  Fills b[0..n-1] with a non-zero array orthogonal to a[]. */
static void solver(const int *a, int n, long long *b)
/* QCP_INSERT_BEGIN:shard09-P047-solver-contract */
/*@ With (values : list Z)
    Require
      2 <= n && n <= 100000 && (forall i, (0 <= i && i < n) => (-10000 <= values[i] && values[i] <= 10000 && values[i] != 0)) &&
      n == Zlength(values) && IntArray::full(a, n, values) * Int64Array::undef_full(b, n)
    Ensure
      exists (out : list Z),
        Spec(values, out) &&
        IntArray::full(a, n, values) * Int64Array::full(b, n, out)
*/
/* QCP_INSERT_END:shard09-P047-solver-contract */
{
    int start = 0;
    if (n % 2) {                           /* consume a leading triple */
        /*@ 3 <= n by local */
        long long x = a[0], y = a[1], z = a[2];
        if (x + y != 0) {
            b[0] = z; b[1] = z; b[2] = -(x + y);
        } else if (x + z != 0) {
            b[0] = y;
            b[2] = y;
            /*@ Assert
              a == a@pre && n == n@pre && b == b@pre && start == 0 &&
              3 <= n@pre && n@pre <= 100000 &&
              n@pre == Zlength(values) && n@pre % 2 != 0 &&
              (forall j,
                (0 <= j && j < n@pre) =>
                (-10000 <= values[j] && values[j] <= 10000 && values[j] != 0)) &&
              x == values[0] && y == values[1] && z == values[2] &&
              x + y == 0 && x + z != 0 &&
              IntArray::full(a@pre, n@pre, values) *
              Int64Array::seg(b@pre, 0, 1, cons(y, nil)) *
              Int64Array::undef_seg(b@pre, 1, 2) *
              Int64Array::seg(b@pre, 2, 3, cons(y, nil)) *
              Int64Array::undef_seg(b@pre, 3, n@pre)
            */
            b[1] = -(x + z);
        } else {
            b[1] = x; b[2] = x; b[0] = -(y + z);
        }
        start = 3;
    }
    /*@ Assert
      exists (written : list Z),
        a == a@pre && n == n@pre && b == b@pre &&
        2 <= n@pre && n@pre <= 100000 &&
        n@pre == Zlength(values) &&
        (forall j,
          (0 <= j && j < n@pre) =>
          (-10000 <= values[j] && values[j] <= 10000 && values[j] != 0)) &&
        (start == 0 || start == 3) &&
        0 <= start && start <= n@pre &&
        n@pre % 2 == start % 2 &&
        OutputPrefix(sublist(0, start, values), written,
                     (10000 * start) / 3) &&
        IntArray::full(a@pre, n@pre, values) *
        Int64Array::seg(b@pre, 0, start, written) *
        Int64Array::undef_seg(b@pre, start, n@pre)
    */
    /*@ Inv Assert
      exists (written : list Z),
        a == a@pre && n == n@pre && b == b@pre &&
        2 <= n@pre && n@pre <= 100000 &&
        n@pre == Zlength(values) &&
        (forall j,
          (0 <= j && j < n@pre) =>
          (-10000 <= values[j] && values[j] <= 10000 && values[j] != 0)) &&
        (start == 0 || start == 3) &&
        0 <= start && start <= i && i <= n@pre &&
        n@pre % 2 == start % 2 &&
        (i - start) % 2 == 0 &&
        OutputPrefix(sublist(0, i, values), written,
                     (10000 * start) / 3) &&
        IntArray::full(a@pre, n@pre, values) *
        Int64Array::seg(b@pre, 0, i, written) *
        Int64Array::undef_seg(b@pre, i, n@pre)
    */
    for (int i = start; i + 1 < n; i += 2) {
        /*@ Assert
          exists (written : list Z),
            a == a@pre && n == n@pre && b == b@pre &&
            2 <= n@pre && n@pre <= 100000 &&
            n@pre == Zlength(values) &&
            (forall j,
              (0 <= j && j < n@pre) =>
              (-10000 <= values[j] && values[j] <= 10000 && values[j] != 0)) &&
            (start == 0 || start == 3) &&
            0 <= start && start <= i && i + 1 < n@pre &&
            n@pre % 2 == start % 2 &&
            (i - start) % 2 == 0 &&
            OutputPrefix(sublist(0, i, values), written,
                         (10000 * start) / 3) &&
            IntArray::full(a@pre, n@pre, values) *
            Int64Array::seg(b@pre, 0, i, written) *
            Int64Array::undef_full(b@pre + i * sizeof(long long), 2) *
            Int64Array::undef_seg(b@pre, i + 2, n@pre)
        */
        pair_fill(a[i], a[i + 1], b + i);
    }
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     static int a[100005];
//     static long long b[100005];
//     while (t--) {
//         int n;
//         scanf("%d", &n);
//         for (int i = 0; i < n; i++)
//             scanf("%d", &a[i]);
//         solver(a, n, b);
//         for (int i = 0; i < n; i++)
//             printf("%lld%c", b[i], i + 1 == n ? '\n' : ' ');
//     }
//     return 0;
// }
