/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P035_807B_t_shirt_hunt_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P035_807B_t_shirt_hunt_lib
*/

/* Codeforces 807/B - T-Shirt Hunt */
// #include <stdio.h>

/*@ Extern Coq
      (ShirtSelection : Z -> Z -> Prop)
      (NoShirtSelection : Z -> Z -> Prop)
      (ShirtScanState : Z -> Z -> Z -> Z -> Prop)
      (AlignmentSearch : Z -> Z -> Z -> Prop)
      (CandidateSearch : Z -> Z -> Z -> Z -> Prop)
      (FirstWinningCandidate : Z -> Z -> Z -> Z -> Prop)
*/

static int wins(int place, int score)
/*@ Require
      26 <= place && place <= 500 &&
      0 <= score && score <= INT_MAX
    Ensure
      ((__return == 1 && ShirtSelection(score, place)) ||
       (__return == 0 && NoShirtSelection(score, place)))
*/
{
    int z = (score / 50) % 475;
    /*@ Inv Assert
          place == place@pre && score == score@pre &&
          26 <= place@pre && place@pre <= 500 &&
          0 <= score@pre && score@pre <= INT_MAX &&
          0 <= i && i <= 25 &&
          0 <= z && z < 475 &&
          ShirtScanState(score@pre, place@pre, i, z)
    */
    for (int i = 0; i < 25; ++i) {
        z = (z * 96 + 42) % 475;
        if (z + 26 == place) return 1;
    }
    return 0;
}

/* QCP_INSERT_BEGIN:P035_807B_t_shirt_hunt.support */
/*@ Extern Coq
      (Pre : Z -> Z -> Z -> Prop)
      (Spec : Z -> Z -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P035_807B_t_shirt_hunt_lib */
/* QCP_INSERT_END:P035_807B_t_shirt_hunt.support */
static int solver(int p, int x, int y)/* QCP_INSERT_BEGIN:P035_807B_t_shirt_hunt.contract */

/*@
    Require
      26 <= p && p <= 500 &&
      1 <= y && y <= x &&
      x <= 20000 &&
      Pre(p, x, y)
    Ensure
      Spec(p, x, y, __return)
*/
/* QCP_INSERT_END:P035_807B_t_shirt_hunt.contract */

{
    int score = y;
    /*@ Inv Assert
          p == p@pre && x == x@pre && y == y@pre &&
          26 <= p@pre && p@pre <= 500 &&
          1 <= y@pre && y@pre <= x@pre && x@pre <= 20000 &&
          Pre(p@pre, x@pre, y@pre) &&
          0 <= score - y@pre && score - y@pre <= 49 &&
          AlignmentSearch(x@pre, y@pre, score)
    */
    while ((score - x) % 50 != 0) ++score;
    /*@ Inv Assert
          p == p@pre && x == x@pre && y == y@pre &&
          26 <= p@pre && p@pre <= 500 &&
          1 <= y@pre && y@pre <= x@pre && x@pre <= 20000 &&
          Pre(p@pre, x@pre, y@pre) &&
          y@pre <= score && score <= x@pre + 50 * 475 &&
          CandidateSearch(p@pre, x@pre, y@pre, score)
    */
    while (!wins(p, score)) {
        /*@ Assert
              p == p@pre && x == x@pre && y == y@pre &&
              26 <= p@pre && p@pre <= 500 &&
              1 <= y@pre && y@pre <= x@pre && x@pre <= 20000 &&
              Pre(p@pre, x@pre, y@pre) &&
              y@pre <= score && score < x@pre + 50 * 475 &&
              score <= INT_MAX - 50 &&
              CandidateSearch(p@pre, x@pre, y@pre, score) &&
              NoShirtSelection(score, p@pre)
        */
        score += 50;
    }
    /*@ Assert
          p == p@pre && x == x@pre && y == y@pre &&
          26 <= p@pre && p@pre <= 500 &&
          1 <= y@pre && y@pre <= x@pre && x@pre <= 20000 &&
          y@pre <= score && score <= x@pre + 50 * 475 &&
          FirstWinningCandidate(p@pre, x@pre, y@pre, score)
    */
    return score <= x ? 0 : (score - x + 99) / 100;
}

// int main(void)
// {
//     int p, x, y; if (scanf("%d %d %d", &p, &x, &y) != 3) return 0;
//     printf("%d\n", solver(p, x, y));
//     return 0;
// }
