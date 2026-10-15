/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P013_1744C_traffic_light_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P013_1744C_traffic_light_lib
*/

/* Codeforces 1744/C - Traffic Light */
// #include <stdio.h>
#include "string.h"

/* QCP_INSERT_BEGIN:P013_1744C_traffic_light.support */
/*@ Extern Coq
      (Pre : Z -> list Z -> Prop)
      (Spec : Z -> list Z -> Z -> Prop)
      (CharArray::full : Z -> Z -> list Z -> Assertion)
      (CharArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P013_1744C_traffic_light_lib */
/*@ Extern Coq
      (TrafficScanState : Z -> list Z -> Z -> Z -> Z -> Prop)
*/
/* QCP_INSERT_END:P013_1744C_traffic_light.support */
static int solver(const char *s, int n, char c)/* QCP_INSERT_BEGIN:P013_1744C_traffic_light.contract */

/*@ With (lights : list Z)
    Require
      n == Zlength(lights) &&
      1 <= Zlength(lights) && Zlength(lights) <= 200000 &&
      (c == 114 || c == 121 || c == 103) &&
      (forall idx, (0 <= idx && idx < Zlength(lights)) =>
        (lights[idx] == 114 || lights[idx] == 121 || lights[idx] == 103)) &&
      Pre(c, lights) &&
      CharArray::full(s, n + 1, app(lights, cons(0, nil))) *
      CharArray::undef_seg(s, n + 1, 200005)
    Ensure
      Spec(c, lights, __return) &&
      CharArray::full(s, n + 1, app(lights, cons(0, nil))) *
      CharArray::undef_seg(s, n + 1, 200005)
*/
/* QCP_INSERT_END:P013_1744C_traffic_light.contract */

{
    /*@ Branch name
          red: c == 114;
          yellow: c == 121;
          green: c == 103
    */
    if (c == 'g') return 0;
    int ans = 0, next_green = -1;
    /*@ Inv
          red:
            n == Zlength(lights) &&
            1 <= n && n <= 200000 && c == 114 &&
            (forall idx, (0 <= idx && idx < n) =>
              (lights[idx] == 114 || lights[idx] == 121 || lights[idx] == 103)) &&
            Pre(c, lights) &&
            -1 <= i && i < 2 * n &&
            0 <= ans && ans <= n &&
            -1 <= next_green && next_green < 2 * n &&
            TrafficScanState(c, lights, i, ans, next_green);
          yellow:
            n == Zlength(lights) &&
            1 <= n && n <= 200000 && c == 121 &&
            (forall idx, (0 <= idx && idx < n) =>
              (lights[idx] == 114 || lights[idx] == 121 || lights[idx] == 103)) &&
            Pre(c, lights) &&
            -1 <= i && i < 2 * n &&
            0 <= ans && ans <= n &&
            -1 <= next_green && next_green < 2 * n &&
            TrafficScanState(c, lights, i, ans, next_green)
          with
          red ==> red
          yellow ==> yellow
    */
    for (int i = 2 * n - 1; i >= 0; --i) {
        /*@ 0 <= i % n && i % n < n by local */
        char ch = s[i % n];
        if (ch == 'g') next_green = i;
        if (i < n && ch == c && next_green - i > ans) ans = next_green - i;
    }
    return ans;
}

// int main(void)
// {
//     int t; scanf("%d", &t);
//     while (t--) {
//         int n; char c, s[200005];
//         scanf("%d %c %200004s", &n, &c, s);
//         printf("%d\n", solver(s, n, c));
//     }
//     return 0;
// }
