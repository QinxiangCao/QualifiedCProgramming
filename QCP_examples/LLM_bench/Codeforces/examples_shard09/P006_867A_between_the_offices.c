/*
 * Codeforces 867/A - Between the Offices  (rating 800, VERDICT)
 *
 * Given a chronological string of 'S' (Seattle) and 'F' (San Francisco),
 * decide whether there were more Seattle->SanFrancisco flights than the
 * reverse. That happens iff the first day is 'S' and the last day is 'F'.
 */

// #include <stdio.h>
// #include <string.h>
/*@ Extern Coq (bool :: *) */
/*@ Extern Coq
      (Spec : list Z -> bool -> Prop)
      (VerdictCode : bool -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P006_867A_between_the_offices_lib */


/* solver: pure. Returns 1 (YES) if first=='S' and last=='F', else 0. */
static int solver(const char *s, int n)
/*@ With (days : list Z)
    Require
      n == Zlength(days) &&
      2 <= n &&
      n <= 100 &&
      (forall i, (0 <= i && i < n) => days[i] == 83 || days[i] == 70) &&
      CharArray::full(s, n + 1, app(days, cons(0, nil)))
    Ensure exists answer,
      Spec(days, answer) &&
      VerdictCode(answer, __return) &&
      CharArray::full(
        s, n + 1, app(days, cons(0, nil)))
*/
{
    /*@
      Znth(0, days, 0) ==
        Znth(0, app(days, cons(0, nil)), 0) &&
      Znth(n - 1, days, 0) ==
        Znth(n - 1, app(days, cons(0, nil)), 0)
    */
    return (s[0] == 'S' && s[n - 1] == 'F');
}

// int main(void)
// {
//     int n;
//     char s[128];
//     if (scanf("%d %127s", &n, s) != 2)
//         return 0;

//     printf("%s\n", solver(s, n) ? "YES" : "NO");
//     return 0;
// }
