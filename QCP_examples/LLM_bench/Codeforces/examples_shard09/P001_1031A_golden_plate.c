/*
 * Codeforces 1031/A - Golden Plate  (rating 800, MATH)
 *
 * Ring i lies on the border of the (w-4(i-1)) x (h-4(i-1)) rectangle, and the
 * border of a W x H rectangle holds 2*(W+H) - 4 cells.  Sum that over the k
 * rings; the constraint on k guarantees every inner rectangle stays valid.
 */

// #include <stdio.h>

/*@ Extern Coq
      (Spec : Z -> Z -> Z -> Z -> Prop)
      (Z::min : Z -> Z -> Z)
      (Z::mul : Z -> Z -> Z)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P001_1031A_golden_plate_lib */


/* solver: pure.  Number of gilded cells for a w x h plate with k rings. */
static long long solver(int w, int h, int k)
/*@ Require
      3 <= w  && w <= 100 && 3 <= h && h <= 100 && 
      1 <= k && Z::mul(4, k) <= Z::min(w, h) + 1 
    Ensure
      Spec(w@pre, h@pre, k@pre, __return) 
*/
{
    long long total = 0;
    /*@ Inv Assert
          w == w@pre && h == h@pre && k == k@pre &&
          3 <= w@pre && w@pre <= 100 &&
          3 <= h@pre && h@pre <= 100 &&
          1 <= k@pre && k@pre <= 25 &&
          Z::mul(4, k@pre) <= Z::min(w@pre, h@pre) + 1 &&
          0 <= i && i <= k@pre &&
          total == 2 * i * (w@pre + h@pre - 2) -
                   8 * i * (i - 1) &&
          0 <= total && total <= 10000
     */
    for (int i = 0; i < k; i++) {
        long long W = w - 4LL * i, H = h - 4LL * i;
        total += 2 * (W + H) - 4;
    }
    return total;
}

// int main(void)
// {
//     int w, h, k;
//     if (scanf("%d %d %d", &w, &h, &k) != 3)
//         return 0;
//     printf("%lld\n", solver(w, h, k));
//     return 0;
// }
