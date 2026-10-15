/*
 * Codeforces 1538/F - Interesting Function  (rating 1500, MATH)
 *
 * Going from 0 to x, the last digit changes on every step, the tens digit on
 * every tenth step, and so on, so the total number of changed digits is
 * sum_d floor(x / 10^d).  The answer is that count for r minus the one for l.
 */

// #include <stdio.h>

/* QCP_INSERT_BEGIN:shard09-P041-solver-support */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P041_1538F_interesting_function_lib */
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Prop)
*/
/* QCP_INSERT_END:shard09-P041-solver-support */

/*@ Extern Coq
      (DecimalPlacePrefix : Z -> Z -> Z -> Prop)
      (DecimalPrefixTotal : Z -> Z -> Prop)
*/

/* solver: pure.  Total digits changed while counting from 0 up to x. */
static long long changed_upto(long long x)
/*@ Require
      1 <= x && x <= 1000000000 && emp
    Ensure
      0 <= __return && __return <= 1111111111 &&
      DecimalPrefixTotal(x@pre, __return) && emp
*/
{
    long long total = 0;
    /*@ Inv Assert
          x == x@pre &&
          1 <= x@pre && x@pre <= 1000000000 &&
          1 <= p && p <= 10000000000 &&
          0 <= total && total <= 1111111111 &&
          DecimalPlacePrefix(x@pre, p, total) && emp
    */
    for (long long p = 1; p <= x; p *= 10)
        total += x / p;
    return total;
}

/* solver: complete interval case. */
static long long solver(long long l, long long r)
/* QCP_INSERT_BEGIN:shard09-P041-normalized-solver-contract */
/*@ Require
      1 <= l && l < r && r <= 1000000000 &&
      emp
    Ensure
      Spec(l, r, __return) && emp
*/
/* QCP_INSERT_END:shard09-P041-normalized-solver-contract */
{
    return changed_upto(r) - changed_upto(l);
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         long long l, r;
//         scanf("%lld %lld", &l, &r);
//         printf("%lld\n", solver(l, r));
//     }
//     return 0;
// }
