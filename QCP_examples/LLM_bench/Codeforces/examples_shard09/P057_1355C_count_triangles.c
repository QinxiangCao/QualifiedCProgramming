/*
 * Codeforces 1355/C - Count Triangles  (rating 1800, MATH)
 *
 * With A <= x <= B <= y <= C <= z <= D the only binding triangle inequality is
 * x + y > z.  Group the pairs by their sum s = x + y (at most 1e6 values):
 * the number of pairs with that sum is a simple interval intersection, and
 * each admits every z in [C, min(D, s-1)].
 */

// #include <stdio.h>

/* QCP_INSERT_BEGIN:shard09-P057-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P057_1355C_count_triangles_lib */
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Z -> Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P057-solver-support */

/*@ Extern Coq
      (TrianglePrefix : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (Z::max : Z -> Z -> Z)
      (Z::min : Z -> Z -> Z)
*/

/* solver: pure.  Number of non-degenerate triangles in the given ranges. */
static long long solver(long long A, long long B, long long C, long long D)
/* QCP_INSERT_BEGIN:shard09-P057-solver-contract */
/*@
    Require
      1 <= A && A <= B && B <= C && C <= D && D <= 500000 &&
      emp
    Ensure
      Spec(A, B, C, D, __return) &&
      emp
*/
/* QCP_INSERT_END:shard09-P057-solver-contract */
{
    long long total = 0;
    /*@ Inv Assert
          A == A@pre && B == B@pre && C == C@pre && D == D@pre &&
          1 <= A@pre && A@pre <= B@pre && B@pre <= C@pre &&
          C@pre <= D@pre && D@pre <= 500000 &&
          A@pre + B@pre <= s && s <= B@pre + C@pre + 1 &&
          0 <= total &&
          total <= (s - (A@pre + B@pre)) * 250000000000 &&
          TrianglePrefix(A@pre, B@pre, C@pre, D@pre, s, total) &&
          emp
    */
    for (long long s = A + B; s <= B + C; s++) {
        long long xlo = A > s - C ? A : s - C;     /* x >= A and y = s-x <= C */
        long long xhi = B < s - B ? B : s - B;     /* x <= B and y = s-x >= B */
        /*@ Assert
              A == A@pre && B == B@pre && C == C@pre && D == D@pre &&
              1 <= A@pre && A@pre <= B@pre && B@pre <= C@pre &&
              C@pre <= D@pre && D@pre <= 500000 &&
              A@pre + B@pre <= s && s <= B@pre + C@pre &&
              0 <= total &&
              total <= (s - (A@pre + B@pre)) * 250000000000 &&
              xlo == Z::max(A@pre, s - C@pre) &&
              xhi == Z::min(B@pre, s - B@pre) &&
              xlo <= xhi &&
              TrianglePrefix(A@pre, B@pre, C@pre, D@pre, s, total) &&
              emp
        */
        if (xlo > xhi)
            continue;
        long long pairs = xhi - xlo + 1;
        long long zhi = D < s - 1 ? D : s - 1;
        /*@ Assert
              A == A@pre && B == B@pre && C == C@pre && D == D@pre &&
              1 <= A@pre && A@pre <= B@pre && B@pre <= C@pre &&
              C@pre <= D@pre && D@pre <= 500000 &&
              A@pre + B@pre <= s && s <= B@pre + C@pre &&
              0 <= total &&
              total <= (s - (A@pre + B@pre)) * 250000000000 &&
              xlo == Z::max(A@pre, s - C@pre) &&
              xhi == Z::min(B@pre, s - B@pre) &&
              xlo <= xhi &&
              pairs == xhi - xlo + 1 &&
              1 <= pairs && pairs <= 500000 &&
              zhi == Z::min(D@pre, s - 1) &&
              TrianglePrefix(A@pre, B@pre, C@pre, D@pre, s, total) &&
              emp
        */
        if (zhi < C)
            continue;
        total += pairs * (zhi - C + 1);
    }
    return total;
}

// int main(void)
// {
//     long long A, B, C, D;
//     if (scanf("%lld %lld %lld %lld", &A, &B, &C, &D) != 4)
//         return 0;
//     printf("%lld\n", solver(A, B, C, D));
//     return 0;
// }
