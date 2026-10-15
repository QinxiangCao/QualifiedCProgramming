/*
 * Codeforces 1313/A - Fast Food Restaurant  (rating 900, BRUTE FORCE)
 *
 * There are only 7 possible non-empty dish sets, so try every subfamily of
 * them (2^7 = 128) and keep the largest one whose total demand for each dish
 * fits the stock.
 */

// #include <stdio.h>
/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Z -> Prop)
      (BestBeforeMaskByBits : Z -> Z -> Z -> Z -> Z -> Prop)
      (FamilyPrefixByBits : Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (SelectedDishPrefixByBits :
        Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P007_1313A_fast_food_restaurant_lib */

/* solver: pure.  Maximum number of visitors servable from a, b, c portions. */
static int solver(int a, int b, int c)
/* QCP_INSERT_BEGIN:shard09-P007-solver-contract */
/*@
    Require
      0 <= a && a <= 10 && 0 <= b && b <= 10 && 0 <= c && c <= 10 &&
      emp
    Ensure
      Spec(a, b, c, __return) &&
      emp
*/
/* QCP_INSERT_END:shard09-P007-solver-contract */
{
    int best = 0;
    /*@ Inv Assert
          a == a@pre && b == b@pre && c == c@pre &&
          0 <= a && a <= 10 && 0 <= b && b <= 10 &&
          0 <= c && c <= 10 &&
          0 <= fam && fam <= 128 &&
          0 <= best && best <= 7 &&
          BestBeforeMaskByBits(a, b, c, fam, best) &&
          emp
     */
    for (int fam = 0; fam < 128; fam++) {
        int need[3] = {0, 0, 0}, cnt = 0;
        /*@ Inv Assert
              exists need_a need_b need_c,
                a == a@pre && b == b@pre && c == c@pre &&
                0 <= a && a <= 10 && 0 <= b && b <= 10 &&
                0 <= c && c <= 10 &&
                0 <= fam && fam < 128 &&
                0 <= best && best <= 7 &&
                BestBeforeMaskByBits(a, b, c, fam, best) &&
                1 <= s && s <= 8 &&
                0 <= cnt && cnt <= 7 &&
                0 <= need_a && need_a <= 4 &&
                0 <= need_b && need_b <= 4 &&
                0 <= need_c && need_c <= 4 &&
                FamilyPrefixByBits(fam, s, cnt,
                                   need_a, need_b, need_c) &&
                IntArray::full(need, 3,
                  cons(need_a, cons(need_b, cons(need_c, nil))))
         */
        for (int s = 1; s <= 7; s++)
            if (fam & (1 << (s - 1))) {
                cnt++;
                /*@ Inv Assert
                      exists need_a need_b need_c,
                        a == a@pre && b == b@pre && c == c@pre &&
                        0 <= a && a <= 10 && 0 <= b && b <= 10 &&
                        0 <= c && c <= 10 &&
                        0 <= fam && fam < 128 &&
                        0 <= best && best <= 7 &&
                        BestBeforeMaskByBits(a, b, c, fam, best) &&
                        1 <= s && s <= 7 &&
                        1 <= cnt && cnt <= 7 &&
                        0 <= d && d <= 3 &&
                        0 <= need_a && need_a <= 4 &&
                        0 <= need_b && need_b <= 4 &&
                        0 <= need_c && need_c <= 4 &&
                        SelectedDishPrefixByBits(
                          fam, s, d, cnt, need_a, need_b, need_c) &&
                        IntArray::full(need, 3,
                          cons(need_a, cons(need_b,
                            cons(need_c, nil))))
                 */
                for (int d = 0; d < 3; d++)
                    if (s & (1 << d))
                        need[d]++;
            }
        if (need[0] <= a && need[1] <= b && need[2] <= c && cnt > best)
            best = cnt;
    }
    return best;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         int a, b, c;
//         scanf("%d %d %d", &a, &b, &c);
//         printf("%d\n", solver(a, b, c));
//     }
//     return 0;
// }
