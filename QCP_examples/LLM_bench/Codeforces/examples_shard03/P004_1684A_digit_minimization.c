/*
 * Codeforces 1684/A - Digit Minimization  (rating 800, GAMES)
 *
 * With more than two digits Alice has enough turns to carry any digit she
 * likes into the first position before the number shrinks to one digit, so the
 * answer is the smallest digit.  With exactly two digits she must swap, and
 * Bob then deletes the new last digit, leaving the original second digit.
 *
 * solver() takes one whole test case (the decimal string) and returns the
 * remaining digit.
 */

// #include <stdio.h>
/* QCP_INSERT_BEGIN:shard03-P004-solver-support */

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard03.P004_1684A_digit_minimization_lib */
/*@ Extern Coq
      (DecimalDigits : Z -> list Z -> Prop)
      (DigitsAsChars : list Z -> list Z)
      (Spec : Z -> Z -> Prop)
*/

/* QCP_INSERT_END:shard03-P004-solver-support */

/* solver: pure.  The final digit for the number given as the string s. */
static char solver(const char *s, int n)
/* QCP_INSERT_BEGIN:shard03-P004-solver-contract */
/*@ With (num : Z) (ds : list Z)
    Require
      10 <= num && num <= 1000000000 &&
      DecimalDigits(num, ds) &&
      2 <= n && n <= 10 && n == Zlength(ds) &&
      (forall i, (0 <= i && i < n) => (0 <= ds[i] && ds[i] <= 9)) &&
      (forall i, (0 <= i && i < n) => ds[i] != 0) &&
      CharArray::full(s, n, DigitsAsChars(ds))
    Ensure
      exists (d : Z),
        Spec(num, d) &&
        __return == d + 48 &&
        CharArray::full(s, n, DigitsAsChars(ds))
*/
/* QCP_INSERT_END:shard03-P004-solver-contract */
{
    if (n == 2)
        return s[1];
    char best = s[0];
    for (int i = 1; i < n; i++)
        if (s[i] < best)
            best = s[i];
    return best;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         char s[16];
//         int n = 0;
//         scanf("%15s", s);
//         while (s[n])
//             n++;
//         printf("%c\n", solver(s, n));
//     }
//     return 0;
// }
