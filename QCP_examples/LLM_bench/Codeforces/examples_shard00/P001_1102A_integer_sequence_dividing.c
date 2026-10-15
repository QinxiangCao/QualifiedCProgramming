/* Codeforces 1102/A - Integer Sequence Dividing */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P001_1102A_integer_sequence_dividing.support */
/*@ Extern Coq
      (Spec : Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P001_1102A_integer_sequence_dividing_lib */
/* QCP_INSERT_END:P001_1102A_integer_sequence_dividing.support */
static long long solver(long long n)/* QCP_INSERT_BEGIN:P001_1102A_integer_sequence_dividing.contract */

/*@ Require
      1 <= n && n <= 2000000000
    Ensure
      Spec(n, __return)
*/
/* QCP_INSERT_END:P001_1102A_integer_sequence_dividing.contract */

{
    return (n * (n + 1) / 2) & 1LL;
}

// int main(void)
// {
//     long long n;
//     if (scanf("%lld", &n) == 1) printf("%lld\n", solver(n));
//     return 0;
// }
