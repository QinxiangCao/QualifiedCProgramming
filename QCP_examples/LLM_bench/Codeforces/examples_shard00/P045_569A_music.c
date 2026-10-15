/* Codeforces 569/A - Music */
// #include <stdio.h>

/* QCP_INSERT_BEGIN:P045_569A_music.support */
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P045_569A_music_lib */
/* QCP_INSERT_END:P045_569A_music.support */
/*@ Extern Coq
      (MusicLoopInvariant : Z -> Z -> Z -> Z -> Z -> Prop)
*/
static int solver(long long t, long long s,
                  long long q) /* QCP_INSERT_BEGIN:P045_569A_music.contract */

/*@
    Require
      2 <= q && q <= 10000 &&
      1 <= s && s < t &&
      t <= 100000
    Ensure
      Spec(t, s, q, __return)
*/
/* QCP_INSERT_END:P045_569A_music.contract */

{
    int starts = 0;
    /*@ Inv Assert
          t == t@pre && q == q@pre &&
          2 <= q@pre && q@pre <= 10000 &&
          1 <= s@pre && s@pre < t@pre &&
          t@pre <= 100000 &&
          1 <= s && s <= (t@pre - 1) * q@pre &&
          0 <= starts && starts < s &&
          MusicLoopInvariant(t@pre, s@pre, q@pre, starts, s)
    */
    while (s < t)
    {
        s *= q;
        ++starts;
    }
    return starts;
}

// int main(void)
// {
//     long long t, s, q; if (scanf("%lld %lld %lld", &t, &s, &q) != 3) return 0;
//     printf("%d\n", solver(t, s, q));
//     return 0;
// }
