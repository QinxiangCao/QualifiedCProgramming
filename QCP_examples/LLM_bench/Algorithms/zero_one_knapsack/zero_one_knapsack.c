



/*@ Extern Coq
      (KnapsackInputsBounded : list Z -> list Z -> Z -> Z -> Prop)
      (KnapsackRowsAnnotationState : list Z -> list Z -> Z -> Z -> Z -> list Z -> Z -> Prop)
      (KnapsackRowAnnotationState : list Z -> list Z -> Z -> Z -> Z -> list Z -> Z -> Z -> Prop)
      (KnapsackResultState : list Z -> list Z -> Z -> Z -> list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_lib */

int zeroOneKnapsack(int *weights, int *values, int n, int capacity, int *dp)
/*@ With (weights_l values_l : list Z)
    Require
      0 <= n && n <= 300 &&
      0 <= capacity && capacity <= 300 &&
      KnapsackInputsBounded(weights_l, values_l, n, capacity) &&
      IntArray::full(weights, n, weights_l) *
      IntArray::full(values, n, values_l) *
      IntArray::undef_full(dp, (n + 1) * (capacity + 1))
    Ensure
      exists dp_l,
      KnapsackResultState(weights_l, values_l, n, capacity, dp_l, __return) &&
      IntArray::full(weights, n, weights_l) *
      IntArray::full(values, n, values_l) *
      IntArray::full(dp, (n + 1) * (capacity + 1), dp_l)
 */
{
  int width = capacity + 1;

  /*@ Inv Assert
      exists dp_l,
      weights == weights@pre && values == values@pre && dp == dp@pre &&
      n == n@pre && capacity == capacity@pre &&
      width == capacity@pre + 1 &&
      0 <= n@pre && n@pre <= 300 &&
      0 <= capacity@pre && capacity@pre <= 300 &&
      0 <= i && i <= n@pre + 1 &&
      KnapsackRowsAnnotationState(
        weights_l, values_l, n@pre, capacity@pre, width, dp_l, i) &&
      IntArray::full(weights, n@pre, weights_l) *
      IntArray::full(values, n@pre, values_l) *
      IntArray::seg(dp, 0, i * width, dp_l) *
      IntArray::undef_seg(dp, i * width, (n@pre + 1) * (capacity@pre + 1))
   */
  for (int i = 0; i <= n; ++i) {
    /*@ Inv Assert
        exists dp_l,
        weights == weights@pre && values == values@pre && dp == dp@pre &&
        n == n@pre && capacity == capacity@pre &&
        width == capacity@pre + 1 &&
        0 <= n@pre && n@pre <= 300 &&
        0 <= capacity@pre && capacity@pre <= 300 &&
        0 <= i && i <= n@pre &&
        0 <= j && j <= capacity@pre + 1 &&
        KnapsackRowAnnotationState(
          weights_l, values_l, n@pre, capacity@pre, width, dp_l, i, j) &&
        IntArray::full(weights, n@pre, weights_l) *
        IntArray::full(values, n@pre, values_l) *
        IntArray::seg(dp, 0, i * width + j, dp_l) *
        IntArray::undef_seg(dp, i * width + j, (n@pre + 1) * (capacity@pre + 1))
     */
    for (int j = 0; j <= capacity; ++j) {
      int idx = i * width + j;
      /*@ 0 <= idx && idx < (n@pre + 1) * (capacity@pre + 1) by local */

      if (i == 0) {
        dp[idx] = 0;
      } else if (j == 0) {
        dp[idx] = 0;
      } else {
        int item = i - 1;
        /*@ 0 <= item && item < n@pre by local */
        int w = weights[item];
        int v = values[item];
        /*@ 0 <= (i - 1) * width + j &&
            (i - 1) * width + j < i * width + j by local */
        int without = dp[(i - 1) * width + j];

        if (w <= j) {
          /*@ 0 <= (i - 1) * width + (j - w) &&
              (i - 1) * width + (j - w) < i * width + j by local */
          int prev = dp[(i - 1) * width + (j - w)];
          int with_val = prev + v;
          if (with_val > without) {
            dp[idx] = with_val;
          } else {
            dp[idx] = without;
          }
        } else {
          dp[idx] = without;
        }
      }
    }
  }

  /*@ Assert
      exists dp_l,
      weights == weights@pre && values == values@pre && dp == dp@pre &&
      n == n@pre && capacity == capacity@pre && width == capacity@pre + 1 &&
      KnapsackResultState(
        weights_l, values_l, n@pre, capacity@pre, dp_l,
        dp_l[n@pre * width + capacity@pre]) &&
      IntArray::full(weights, n@pre, weights_l) *
      IntArray::full(values, n@pre, values_l) *
      IntArray::full(dp, (n@pre + 1) * (capacity@pre + 1), dp_l)
   */
  /*@ 0 <= n * width + capacity &&
      n * width + capacity < (n@pre + 1) * (capacity@pre + 1) by local */
  return dp[n * width + capacity];
}
