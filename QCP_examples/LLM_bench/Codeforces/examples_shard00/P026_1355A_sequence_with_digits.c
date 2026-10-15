/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_lib
*/

/* Codeforces 1355/A - Sequence with Digits */
// #include <stdio.h>

/*@ Extern Coq
      (DigitRecurrenceStep : Z -> Z -> Prop)
      (DigitScanState : Z -> Z -> Z -> Z -> Prop)
      (SequencePrefix : Z -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_lib */

static long long step(long long x)
/*@ Require
      1 <= x && x <= 1810000000000000000 && emp
    Ensure
      0 <= __return && __return <= 81 &&
      DigitRecurrenceStep(x@pre, x@pre + __return) && emp
*/
{
    int mn = 9, mx = 0;
    /*@ Inv Assert
          1 <= x@pre && x@pre <= 1810000000000000000 &&
          0 <= x && x <= x@pre &&
          0 <= mn && mn <= 9 &&
          0 <= mx && mx <= 9 &&
          DigitScanState(x@pre, x, mn, mx)
    */
    while (x)
    {
        int d = (int)(x % 10);
        x /= 10;
        if (d < mn)
            mn = d;
        if (d > mx)
            mx = d;
    }
    return (long long)mn * mx;
}

/* QCP_INSERT_BEGIN:P026_1355A_sequence_with_digits.support */
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P026_1355A_sequence_with_digits_lib */
/* QCP_INSERT_END:P026_1355A_sequence_with_digits.support */
static long long solver(long long a,
                        long long k) /* QCP_INSERT_BEGIN:P026_1355A_sequence_with_digits.contract */

/*@ With (a1 : Z)
    Require
      1 <= a1 && a1 <= 1000000000000000000 &&
      1 <= k && k <= 10000000000000000 &&
      a == a1
    Ensure
      Spec(a1, k, __return)
*/
/* QCP_INSERT_END:P026_1355A_sequence_with_digits.contract */

{
    /*@ Inv Assert
          a@pre == a1 && k == k@pre &&
          1 <= a1 && a1 <= 1000000000000000000 &&
          1 <= k@pre && k@pre <= 10000000000000000 &&
          1 <= i && i <= k@pre &&
          a1 <= a &&
          a <= a1 + 81 * (i - 1) &&
          a <= 1810000000000000000 &&
          SequencePrefix(a1, i, a)
    */
    for (long long i = 1; i < k; ++i)
    {
        long long add = step(a);
        if (!add)
            /*@ Assert
                  a@pre == a1 && k == k@pre &&
                  1 <= a1 && a1 <= 1000000000000000000 &&
                  1 <= k@pre && k@pre <= 10000000000000000 &&
                  1 <= i && i < k@pre &&
                  add == 0 &&
                  a1 <= a && a <= a1 + 81 * (i - 1) &&
                  a <= 1810000000000000000 &&
                  SequencePrefix(a1, i, a) &&
                  Spec(a1, k@pre, a)
            */
            break;
        a += add;
    }
    return a;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         long long a, k; scanf("%lld %lld", &a, &k);
//         printf("%lld\n", solver(a, k));
//     }
//     return 0;
// }
