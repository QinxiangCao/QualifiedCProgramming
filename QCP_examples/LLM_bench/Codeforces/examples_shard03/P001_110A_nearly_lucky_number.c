/*
 * Codeforces 110/A - Nearly Lucky Number  (rating 800, VERDICT)
 *
 * A number is "nearly lucky" if the count of lucky digits (4 or 7) in its
 * decimal representation is itself a lucky number (a positive number whose
 * digits are all 4 or 7).
 */

// #include <stdio.h>
/* QCP_INSERT_BEGIN:shard03-P001-solver-support */

/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard03.P001_110A_nearly_lucky_number_lib */
/*@ Extern Coq
      (DecimalDigits : Z -> list Z -> Prop)
      (DigitsAsChars : list Z -> list Z)
      (Spec : Z -> Z -> Prop)
*/

/* QCP_INSERT_END:shard03-P001-solver-support */

/* ---- solver: pure, no I/O ----------------------------------------------- *
 * Takes the number as a decimal string (n can be up to 10^18, so we never
 * need its numeric value -- only its digits). Returns 1 if nearly lucky,
 * else 0. main() turns that into "YES"/"NO".
 */
static int solver(const char *digits)
/* QCP_INSERT_BEGIN:shard03-P001-solver-contract */
/*@ With (n : Z) (ds : list Z)
    Require
      1 <= n && n <= 1000000000000000000 &&
      DecimalDigits(n, ds) &&
      1 <= Zlength(ds) && Zlength(ds) <= 19 &&
      (forall i, (0 <= i && i < Zlength(ds)) => (0 <= ds[i] && ds[i] <= 9)) &&
      CharArray::full(digits, Zlength(ds) + 1, app(DigitsAsChars(ds), cons(0, nil)))
    Ensure
      Spec(n, __return) &&
      CharArray::full(digits, Zlength(ds) + 1, app(DigitsAsChars(ds), cons(0, nil)))
*/
/* QCP_INSERT_END:shard03-P001-solver-contract */
{
    int lucky_count = 0;
    for (int i = 0; digits[i] != '\0'; i++)
        if (digits[i] == '4' || digits[i] == '7')
            lucky_count++;

    if (lucky_count == 0)
        return 0;

    /* is lucky_count itself a lucky number? */
    for (int c = lucky_count; c > 0; c /= 10) {
        int d = c % 10;
        if (d != 4 && d != 7)
            return 0;
    }
    return 1;
}

// int main(void)
// {
//     char digits[32];
//     if (scanf("%31s", digits) != 1)
//         return 0;

//     printf("%s\n", solver(digits) ? "YES" : "NO");
//     return 0;
// }
