/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P014_1765E_exchange_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P014_1765E_exchange_lib
*/

/*
 * Codeforces 1765/E - Exchange  (rating 1000, MATH)
 *
 * Selling a gold coin yields a silver, buying one costs b.  If a > b a single
 * gold coin can be cycled (sell for a, buy back for b) for a net profit of
 * a-b silver per round, so one quest reaches any target.  Otherwise cycling
 * never gains anything and the best plan is to sell every coin once, needing
 * ceil(n/a) quests.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P014_1765E_exchange_lib */

/* solver: pure.  Minimum number of quests to end up with >= n silver. */
static long long solver(long long n, long long a, long long b)
/* QCP_INSERT_BEGIN:shard09-P014-solver-contract */
/*@
    Require
      1 <= n && n <= 10000000 && 1 <= a && a <= 50 && 1 <= b && b <= 50 &&
      emp
    Ensure
      Spec(n, a, b, __return) &&
      emp
*/
/* QCP_INSERT_END:shard09-P014-solver-contract */
{
    if (a > b)
        return 1;
    return (n + a - 1) / a;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         long long n, a, b;
//         scanf("%lld %lld %lld", &n, &a, &b);
//         printf("%lld\n", solver(n, a, b));
//     }
//     return 0;
// }
