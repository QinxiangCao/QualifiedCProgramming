



/*@ Extern Coq
      (MultipleKnapsackAnswer : list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (MKDPValueBound : list Z -> Z -> Prop)
      (MKScratchArraysSafety : list Z -> list Z -> list Z -> Z -> Prop)
      (MKDPTableSafety : list Z -> Z -> Z -> list Z -> Prop)
      (MKDPTableSemantics : list Z -> list Z -> list Z -> Z -> Z -> list Z -> Prop)
      (MKZeroPrefixSafety : list Z -> Z -> Prop)
      (MKZeroPrefixSemantics : list Z -> Z -> Prop)
      (MKCopyPrefixSafety : list Z -> list Z -> Z -> Z -> Prop)
      (MKCopyPrefixSemantics : list Z -> list Z -> Z -> Prop)
      (MKTransitionSafety : list Z -> Z -> Z -> Z -> Z -> Prop)
      (MKTransitionSemantics : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MKTransitionValueBound : list Z -> Z -> Z -> Z -> Z -> Prop)
      (MKItemResidueProgressSafety : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (MKItemResidueProgressSemantics : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MKItemResiduePrefixSafety : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MKItemResiduePrefixSemantics : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MKResidueLoopSafety : list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MKResidueLoopSemantics : list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MKQueueDropSafety : list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MKQueueDropSemantics : list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MKQueueAfterDropSemantics : list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MKQueuePendingSemantics : list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MKQueueResultSafety : list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MKQueueResultSemantics : list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_lib */

int multipleKnapsack(int *weights, int *values, int *counts,
                     int n, int capacity,
                     int *dp, int *old, int *q_idx, int *q_val)
/*@ With (weights_l : list Z) (values_l : list Z) (counts_l : list Z)
          (old0 : list Z) (qidx0 : list Z) (qval0 : list Z)
    Require
      0 <= n && n <= 1000 &&
      0 <= capacity && capacity <= 1000 &&
      Zlength(weights_l) == n &&
      Zlength(values_l) == n &&
      Zlength(counts_l) == n &&
      MKScratchArraysSafety(old0, qidx0, qval0, capacity) &&
      IntArray::full(weights, n, weights_l) *
      IntArray::full(values, n, values_l) *
      IntArray::full(counts, n, counts_l) *
      IntArray::undef_full(dp, capacity + 1) *
      IntArray::full(old, capacity + 1, old0) *
      IntArray::full(q_idx, capacity + 1, qidx0) *
      IntArray::full(q_val, capacity + 1, qval0) &&
      (forall (idx : Z), (0 <= idx && idx < n) =>
        (1 <= weights_l[idx] && weights_l[idx] <= capacity + 1 &&
         0 <= values_l[idx] && values_l[idx] <= 1000 &&
         0 <= counts_l[idx] && counts_l[idx] <= capacity))
    Ensure
      exists dp_l old_l qidx_l qval_l,
      MultipleKnapsackAnswer(weights_l, values_l, counts_l, capacity, __return) &&
      MKDPTableSafety(weights_l, n, capacity, dp_l) &&
      MKDPTableSemantics(weights_l, values_l, counts_l, n, capacity, dp_l) &&
      IntArray::full(weights, n, weights_l) *
      IntArray::full(values, n, values_l) *
      IntArray::full(counts, n, counts_l) *
      IntArray::full(dp, capacity + 1, dp_l) *
      IntArray::full(old, capacity + 1, old_l) *
      IntArray::full(q_idx, capacity + 1, qidx_l) *
      IntArray::full(q_val, capacity + 1, qval_l)
 */
{
  /*@ Inv Assert
      exists dp_l,
      weights == weights@pre && values == values@pre && counts == counts@pre &&
      n == n@pre && capacity == capacity@pre &&
      dp == dp@pre && old == old@pre && q_idx == q_idx@pre && q_val == q_val@pre &&
      0 <= n@pre && n@pre <= 1000 &&
      0 <= capacity@pre && capacity@pre <= 1000 &&
      Zlength(weights_l) == n@pre &&
      Zlength(values_l) == n@pre &&
      Zlength(counts_l) == n@pre &&
      Zlength(dp_l) == j &&
      0 <= j && j <= capacity@pre + 1 &&
      MKScratchArraysSafety(old0, qidx0, qval0, capacity@pre) &&
      MKZeroPrefixSafety(dp_l, j) &&
      MKZeroPrefixSemantics(dp_l, j) &&
      IntArray::full(weights@pre, n@pre, weights_l) *
      IntArray::full(values@pre, n@pre, values_l) *
      IntArray::full(counts@pre, n@pre, counts_l) *
      IntArray::seg(dp@pre, 0, j, dp_l) *
      IntArray::undef_seg(dp@pre, j, capacity@pre + 1) *
      IntArray::full(old@pre, capacity@pre + 1, old0) *
      IntArray::full(q_idx@pre, capacity@pre + 1, qidx0) *
      IntArray::full(q_val@pre, capacity@pre + 1, qval0) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) =>
        (1 <= weights_l[idx] && weights_l[idx] <= capacity@pre + 1 &&
         0 <= values_l[idx] && values_l[idx] <= 1000 &&
         0 <= counts_l[idx] && counts_l[idx] <= capacity@pre))
   */
  for (int j = 0; j <= capacity; ++j) {
    dp[j] = 0;
  }

  /*@ Assert
      exists dp_l,
      weights == weights@pre && values == values@pre && counts == counts@pre &&
      n == n@pre && capacity == capacity@pre &&
      dp == dp@pre && old == old@pre && q_idx == q_idx@pre && q_val == q_val@pre &&
      0 <= n@pre && n@pre <= 1000 &&
      0 <= capacity@pre && capacity@pre <= 1000 &&
      Zlength(weights_l) == n@pre &&
      Zlength(values_l) == n@pre &&
      Zlength(counts_l) == n@pre &&
      Zlength(dp_l) == capacity@pre + 1 &&
      MKScratchArraysSafety(old0, qidx0, qval0, capacity@pre) &&
      MKZeroPrefixSafety(dp_l, capacity@pre + 1) &&
      MKZeroPrefixSemantics(dp_l, capacity@pre + 1) &&
      MKDPTableSafety(weights_l, 0, capacity@pre, dp_l) &&
      MKDPTableSemantics(weights_l, values_l, counts_l, 0, capacity@pre, dp_l) &&
      IntArray::full(weights@pre, n@pre, weights_l) *
      IntArray::full(values@pre, n@pre, values_l) *
      IntArray::full(counts@pre, n@pre, counts_l) *
      IntArray::full(dp@pre, capacity@pre + 1, dp_l) *
      IntArray::full(old@pre, capacity@pre + 1, old0) *
      IntArray::full(q_idx@pre, capacity@pre + 1, qidx0) *
      IntArray::full(q_val@pre, capacity@pre + 1, qval0) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) =>
        (1 <= weights_l[idx] && weights_l[idx] <= capacity@pre + 1 &&
         0 <= values_l[idx] && values_l[idx] <= 1000 &&
         0 <= counts_l[idx] && counts_l[idx] <= capacity@pre))
   */

  /*@ Inv Assert
      exists dp_l old_l qidx_l qval_l,
      weights == weights@pre && values == values@pre && counts == counts@pre &&
      n == n@pre && capacity == capacity@pre &&
      dp == dp@pre && old == old@pre && q_idx == q_idx@pre && q_val == q_val@pre &&
      0 <= n@pre && n@pre <= 1000 &&
      0 <= capacity@pre && capacity@pre <= 1000 &&
      Zlength(weights_l) == n@pre &&
      Zlength(values_l) == n@pre &&
      Zlength(counts_l) == n@pre &&
      Zlength(dp_l) == capacity@pre + 1 &&
      Zlength(old_l) == capacity@pre + 1 &&
      Zlength(qidx_l) == capacity@pre + 1 &&
      Zlength(qval_l) == capacity@pre + 1 &&
      0 <= i && i <= n@pre &&
      MKDPTableSafety(weights_l, i, capacity@pre, dp_l) &&
      MKDPTableSemantics(weights_l, values_l, counts_l, i, capacity@pre, dp_l) &&
      IntArray::full(weights@pre, n@pre, weights_l) *
      IntArray::full(values@pre, n@pre, values_l) *
      IntArray::full(counts@pre, n@pre, counts_l) *
      IntArray::full(dp@pre, capacity@pre + 1, dp_l) *
      IntArray::full(old@pre, capacity@pre + 1, old_l) *
      IntArray::full(q_idx@pre, capacity@pre + 1, qidx_l) *
      IntArray::full(q_val@pre, capacity@pre + 1, qval_l) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) =>
        (1 <= weights_l[idx] && weights_l[idx] <= capacity@pre + 1 &&
         0 <= values_l[idx] && values_l[idx] <= 1000 &&
         0 <= counts_l[idx] && counts_l[idx] <= capacity@pre))
   */
  for (int i = 0; i < n; ++i) {
    /*@ Inv Assert
        exists dp_l old_l qidx_l qval_l,
        weights == weights@pre && values == values@pre && counts == counts@pre &&
        n == n@pre && capacity == capacity@pre &&
        dp == dp@pre && old == old@pre && q_idx == q_idx@pre && q_val == q_val@pre &&
        0 <= n@pre && n@pre <= 1000 &&
        0 <= capacity@pre && capacity@pre <= 1000 &&
        Zlength(weights_l) == n@pre &&
        Zlength(values_l) == n@pre &&
        Zlength(counts_l) == n@pre &&
        Zlength(dp_l) == capacity@pre + 1 &&
        Zlength(old_l) == capacity@pre + 1 &&
        Zlength(qidx_l) == capacity@pre + 1 &&
        Zlength(qval_l) == capacity@pre + 1 &&
        0 <= i && i < n@pre &&
        0 <= j && j <= capacity@pre + 1 &&
      MKDPTableSafety(weights_l, i, capacity@pre, dp_l) &&
      MKDPTableSemantics(weights_l, values_l, counts_l, i, capacity@pre, dp_l) &&
        MKCopyPrefixSafety(dp_l, old_l, j, capacity@pre) &&
        MKCopyPrefixSemantics(dp_l, old_l, j) &&
        IntArray::full(weights@pre, n@pre, weights_l) *
        IntArray::full(values@pre, n@pre, values_l) *
        IntArray::full(counts@pre, n@pre, counts_l) *
        IntArray::full(dp@pre, capacity@pre + 1, dp_l) *
        IntArray::full(old@pre, capacity@pre + 1, old_l) *
        IntArray::full(q_idx@pre, capacity@pre + 1, qidx_l) *
        IntArray::full(q_val@pre, capacity@pre + 1, qval_l) &&
        (forall (idx : Z), (0 <= idx && idx < n@pre) =>
          (1 <= weights_l[idx] && weights_l[idx] <= capacity@pre + 1 &&
           0 <= values_l[idx] && values_l[idx] <= 1000 &&
           0 <= counts_l[idx] && counts_l[idx] <= capacity@pre))
     */
    for (int j = 0; j <= capacity; ++j) {
      old[j] = dp[j];
    }

    int w = weights[i];
    int v = values[i];
    int cnt = counts[i];

    /*@ Assert
      exists dp_l old_l qidx_l qval_l,
      weights == weights@pre && values == values@pre && counts == counts@pre &&
      n == n@pre && capacity == capacity@pre &&
      dp == dp@pre && old == old@pre && q_idx == q_idx@pre && q_val == q_val@pre &&
      0 <= n@pre && n@pre <= 1000 &&
      0 <= capacity@pre && capacity@pre <= 1000 &&
      Zlength(weights_l) == n@pre &&
      Zlength(values_l) == n@pre &&
      Zlength(counts_l) == n@pre &&
      Zlength(dp_l) == capacity@pre + 1 &&
      Zlength(old_l) == capacity@pre + 1 &&
      Zlength(qidx_l) == capacity@pre + 1 &&
      Zlength(qval_l) == capacity@pre + 1 &&
      0 <= i && i < n@pre &&
      w == weights_l[i] &&
      v == values_l[i] &&
      cnt == counts_l[i] &&
      1 <= w && w <= capacity@pre + 1 &&
      0 <= v && v <= 1000 &&
      0 <= cnt && cnt <= capacity@pre &&
      MKDPTableSafety(weights_l, i, capacity@pre, dp_l) &&
      MKDPTableSemantics(weights_l, values_l, counts_l, i, capacity@pre, dp_l) &&
      MKDPValueBound(old_l, capacity@pre) &&
      MKTransitionValueBound(old_l, w, v, cnt, capacity@pre) &&
      MKCopyPrefixSafety(dp_l, old_l, capacity@pre + 1, capacity@pre) &&
      MKCopyPrefixSemantics(dp_l, old_l, capacity@pre + 1) &&
      MKItemResidueProgressSafety(old_l, dp_l, 0, w, cnt, capacity@pre) &&
      MKItemResidueProgressSemantics(old_l, dp_l, 0, w, v, cnt, capacity@pre) &&
      IntArray::full(weights@pre, n@pre, weights_l) *
      IntArray::full(values@pre, n@pre, values_l) *
      IntArray::full(counts@pre, n@pre, counts_l) *
      IntArray::full(dp@pre, capacity@pre + 1, dp_l) *
      IntArray::full(old@pre, capacity@pre + 1, old_l) *
      IntArray::full(q_idx@pre, capacity@pre + 1, qidx_l) *
      IntArray::full(q_val@pre, capacity@pre + 1, qval_l) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) =>
        (1 <= weights_l[idx] && weights_l[idx] <= capacity@pre + 1 &&
         0 <= values_l[idx] && values_l[idx] <= 1000 &&
         0 <= counts_l[idx] && counts_l[idx] <= capacity@pre))
    */

    /*@ Inv Assert
      exists dp_l old_l qidx_l qval_l,
      weights == weights@pre && values == values@pre && counts == counts@pre &&
      n == n@pre && capacity == capacity@pre &&
      dp == dp@pre && old == old@pre && q_idx == q_idx@pre && q_val == q_val@pre &&
      0 <= n@pre && n@pre <= 1000 &&
      0 <= capacity@pre && capacity@pre <= 1000 &&
      Zlength(weights_l) == n@pre &&
      Zlength(values_l) == n@pre &&
      Zlength(counts_l) == n@pre &&
      Zlength(dp_l) == capacity@pre + 1 &&
      Zlength(old_l) == capacity@pre + 1 &&
      Zlength(qidx_l) == capacity@pre + 1 &&
      Zlength(qval_l) == capacity@pre + 1 &&
      0 <= i && i < n@pre &&
      w == weights_l[i] &&
      v == values_l[i] &&
      cnt == counts_l[i] &&
      1 <= w && w <= capacity@pre + 1 &&
      0 <= v && v <= 1000 &&
      0 <= cnt && cnt <= capacity@pre &&
      0 <= r && r <= w && r <= capacity@pre + 1 &&
      MKDPTableSafety(weights_l, i, capacity@pre, old_l) &&
      MKDPTableSemantics(weights_l, values_l, counts_l, i, capacity@pre, old_l) &&
      MKDPValueBound(old_l, capacity@pre) &&
      MKTransitionValueBound(old_l, w, v, cnt, capacity@pre) &&
      MKItemResidueProgressSafety(old_l, dp_l, r, w, cnt, capacity@pre) &&
      MKItemResidueProgressSemantics(old_l, dp_l, r, w, v, cnt, capacity@pre) &&
      IntArray::full(weights@pre, n@pre, weights_l) *
      IntArray::full(values@pre, n@pre, values_l) *
      IntArray::full(counts@pre, n@pre, counts_l) *
      IntArray::full(dp@pre, capacity@pre + 1, dp_l) *
      IntArray::full(old@pre, capacity@pre + 1, old_l) *
      IntArray::full(q_idx@pre, capacity@pre + 1, qidx_l) *
      IntArray::full(q_val@pre, capacity@pre + 1, qval_l) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) =>
        (1 <= weights_l[idx] && weights_l[idx] <= capacity@pre + 1 &&
         0 <= values_l[idx] && values_l[idx] <= 1000 &&
         0 <= counts_l[idx] && counts_l[idx] <= capacity@pre))
    */
    for (int r = 0; r < w && r <= capacity; ++r) {
      int head = 0;
      int tail = 0;
      int k = 0;

      /*@ Inv Assert
        exists dp_l old_l qidx_l qval_l,
        weights == weights@pre && values == values@pre && counts == counts@pre &&
        n == n@pre && capacity == capacity@pre &&
        dp == dp@pre && old == old@pre && q_idx == q_idx@pre && q_val == q_val@pre &&
        0 <= n@pre && n@pre <= 1000 &&
        0 <= capacity@pre && capacity@pre <= 1000 &&
        Zlength(weights_l) == n@pre &&
        Zlength(values_l) == n@pre &&
        Zlength(counts_l) == n@pre &&
        Zlength(dp_l) == capacity@pre + 1 &&
        Zlength(old_l) == capacity@pre + 1 &&
        Zlength(qidx_l) == capacity@pre + 1 &&
        Zlength(qval_l) == capacity@pre + 1 &&
        0 <= i && i < n@pre &&
        0 <= r && r < w && r <= capacity@pre &&
        w == weights_l[i] &&
        v == values_l[i] &&
        cnt == counts_l[i] &&
        1 <= w && w <= capacity@pre + 1 &&
        0 <= v && v <= 1000 &&
        0 <= cnt && cnt <= capacity@pre &&
        pos == r + k * w &&
        0 <= k && k <= capacity@pre + 1 && 0 <= pos && pos <= capacity@pre + w &&
        0 <= head && head <= tail && tail <= k && tail <= capacity@pre + 1 &&
        MKDPTableSafety(weights_l, i, capacity@pre, old_l) &&
        MKDPTableSemantics(weights_l, values_l, counts_l, i, capacity@pre, old_l) &&
        MKDPValueBound(old_l, capacity@pre) &&
        MKTransitionValueBound(old_l, w, v, cnt, capacity@pre) &&
        MKItemResiduePrefixSafety(old_l, dp_l, r, w, cnt, k, capacity@pre) &&
        MKItemResiduePrefixSemantics(old_l, dp_l, r, w, v, cnt, k, capacity@pre) &&
        MKResidueLoopSafety(old_l, dp_l, qidx_l, qval_l, r, w, k, head, tail, capacity@pre) &&
        MKResidueLoopSemantics(old_l, dp_l, qidx_l, qval_l, r, w, v, cnt, k, head, tail, capacity@pre) &&
        IntArray::full(weights@pre, n@pre, weights_l) *
        IntArray::full(values@pre, n@pre, values_l) *
        IntArray::full(counts@pre, n@pre, counts_l) *
        IntArray::full(dp@pre, capacity@pre + 1, dp_l) *
        IntArray::full(old@pre, capacity@pre + 1, old_l) *
        IntArray::full(q_idx@pre, capacity@pre + 1, qidx_l) *
        IntArray::full(q_val@pre, capacity@pre + 1, qval_l) &&
        (forall (idx : Z), (0 <= idx && idx < n@pre) =>
          (1 <= weights_l[idx] && weights_l[idx] <= capacity@pre + 1 &&
           0 <= values_l[idx] && values_l[idx] <= 1000 &&
           0 <= counts_l[idx] && counts_l[idx] <= capacity@pre))
      */
      for (int pos = r; pos <= capacity; pos += w) {
        int current = old[pos] - k * v;

        /*@ Inv Assert
          exists dp_l old_l qidx_l qval_l,
          weights == weights@pre && values == values@pre && counts == counts@pre &&
          n == n@pre && capacity == capacity@pre &&
          dp == dp@pre && old == old@pre && q_idx == q_idx@pre && q_val == q_val@pre &&
          0 <= n@pre && n@pre <= 1000 &&
          0 <= capacity@pre && capacity@pre <= 1000 &&
          Zlength(weights_l) == n@pre &&
          Zlength(values_l) == n@pre &&
          Zlength(counts_l) == n@pre &&
          Zlength(dp_l) == capacity@pre + 1 &&
          Zlength(old_l) == capacity@pre + 1 &&
          Zlength(qidx_l) == capacity@pre + 1 &&
          Zlength(qval_l) == capacity@pre + 1 &&
          0 <= i && i < n@pre &&
          0 <= r && r < w && r <= capacity@pre &&
          w == weights_l[i] &&
          v == values_l[i] &&
          cnt == counts_l[i] &&
          1 <= w && w <= capacity@pre + 1 &&
          0 <= v && v <= 1000 &&
          0 <= cnt && cnt <= capacity@pre &&
          pos == r + k * w &&
          0 <= k && k <= capacity@pre && 0 <= pos && pos <= capacity@pre &&
          current == old_l[pos] - k * v &&
          -1000000 <= current && current <= 1000000 &&
          0 <= current + k * v && current + k * v <= 1000000 &&
          0 <= head && head <= tail && tail <= k && tail <= capacity@pre + 1 &&
          MKDPTableSafety(weights_l, i, capacity@pre, old_l) &&
          MKDPTableSemantics(weights_l, values_l, counts_l, i, capacity@pre, old_l) &&
          MKDPValueBound(old_l, capacity@pre) &&
          MKTransitionValueBound(old_l, w, v, cnt, capacity@pre) &&
          MKItemResiduePrefixSafety(old_l, dp_l, r, w, cnt, k, capacity@pre) &&
          MKItemResiduePrefixSemantics(old_l, dp_l, r, w, v, cnt, k, capacity@pre) &&
          MKQueueDropSafety(old_l, qidx_l, qval_l, head, tail, r, w, k, capacity@pre) &&
          MKQueueDropSemantics(old_l, qidx_l, qval_l, head, tail, r, w, v, cnt, k) &&
          IntArray::full(weights@pre, n@pre, weights_l) *
          IntArray::full(values@pre, n@pre, values_l) *
          IntArray::full(counts@pre, n@pre, counts_l) *
          IntArray::full(dp@pre, capacity@pre + 1, dp_l) *
          IntArray::full(old@pre, capacity@pre + 1, old_l) *
          IntArray::full(q_idx@pre, capacity@pre + 1, qidx_l) *
          IntArray::full(q_val@pre, capacity@pre + 1, qval_l) &&
          (forall (idx : Z), (0 <= idx && idx < n@pre) =>
            (1 <= weights_l[idx] && weights_l[idx] <= capacity@pre + 1 &&
             0 <= values_l[idx] && values_l[idx] <= 1000 &&
             0 <= counts_l[idx] && counts_l[idx] <= capacity@pre))
        */
        while (head < tail && q_idx[head] < k - cnt) {
          head++;
        }

        /*@ Assert
          exists dp_l old_l qidx_l qval_l,
          weights == weights@pre && values == values@pre && counts == counts@pre &&
          n == n@pre && capacity == capacity@pre &&
          dp == dp@pre && old == old@pre && q_idx == q_idx@pre && q_val == q_val@pre &&
          0 <= n@pre && n@pre <= 1000 &&
          0 <= capacity@pre && capacity@pre <= 1000 &&
          Zlength(weights_l) == n@pre &&
          Zlength(values_l) == n@pre &&
          Zlength(counts_l) == n@pre &&
          Zlength(dp_l) == capacity@pre + 1 &&
          Zlength(old_l) == capacity@pre + 1 &&
          Zlength(qidx_l) == capacity@pre + 1 &&
          Zlength(qval_l) == capacity@pre + 1 &&
          0 <= i && i < n@pre &&
          0 <= r && r < w && r <= capacity@pre &&
          w == weights_l[i] &&
          v == values_l[i] &&
          cnt == counts_l[i] &&
          1 <= w && w <= capacity@pre + 1 &&
          0 <= v && v <= 1000 &&
          0 <= cnt && cnt <= capacity@pre &&
          pos == r + k * w &&
          0 <= k && k <= capacity@pre && 0 <= pos && pos <= capacity@pre &&
          current == old_l[pos] - k * v &&
          -1000000 <= current && current <= 1000000 &&
          0 <= current + k * v && current + k * v <= 1000000 &&
          0 <= head && head <= tail && tail <= k && tail <= capacity@pre + 1 &&
          (head < tail => 0 <= tail - 1 && tail - 1 < capacity@pre + 1) &&
          MKDPTableSafety(weights_l, i, capacity@pre, old_l) &&
          MKDPTableSemantics(weights_l, values_l, counts_l, i, capacity@pre, old_l) &&
          MKDPValueBound(old_l, capacity@pre) &&
          MKTransitionValueBound(old_l, w, v, cnt, capacity@pre) &&
          MKItemResiduePrefixSafety(old_l, dp_l, r, w, cnt, k, capacity@pre) &&
          MKItemResiduePrefixSemantics(old_l, dp_l, r, w, v, cnt, k, capacity@pre) &&
          MKQueueDropSafety(old_l, qidx_l, qval_l, head, tail, r, w, k, capacity@pre) &&
          MKQueueAfterDropSemantics(old_l, qidx_l, qval_l, head, tail, r, w, v, cnt, k) &&
          IntArray::full(weights@pre, n@pre, weights_l) *
          IntArray::full(values@pre, n@pre, values_l) *
          IntArray::full(counts@pre, n@pre, counts_l) *
          IntArray::full(dp@pre, capacity@pre + 1, dp_l) *
          IntArray::full(old@pre, capacity@pre + 1, old_l) *
          IntArray::full(q_idx@pre, capacity@pre + 1, qidx_l) *
          IntArray::full(q_val@pre, capacity@pre + 1, qval_l) &&
          (forall (idx : Z), (0 <= idx && idx < n@pre) =>
            (1 <= weights_l[idx] && weights_l[idx] <= capacity@pre + 1 &&
             0 <= values_l[idx] && values_l[idx] <= 1000 &&
             0 <= counts_l[idx] && counts_l[idx] <= capacity@pre))
        */

        /*@ Inv Assert
          exists dp_l old_l qidx_l qval_l,
          weights == weights@pre && values == values@pre && counts == counts@pre &&
          n == n@pre && capacity == capacity@pre &&
          dp == dp@pre && old == old@pre && q_idx == q_idx@pre && q_val == q_val@pre &&
          0 <= n@pre && n@pre <= 1000 &&
          0 <= capacity@pre && capacity@pre <= 1000 &&
          Zlength(weights_l) == n@pre &&
          Zlength(values_l) == n@pre &&
          Zlength(counts_l) == n@pre &&
          Zlength(dp_l) == capacity@pre + 1 &&
          Zlength(old_l) == capacity@pre + 1 &&
          Zlength(qidx_l) == capacity@pre + 1 &&
          Zlength(qval_l) == capacity@pre + 1 &&
          0 <= i && i < n@pre &&
          0 <= r && r < w && r <= capacity@pre &&
          w == weights_l[i] &&
          v == values_l[i] &&
          cnt == counts_l[i] &&
          1 <= w && w <= capacity@pre + 1 &&
          0 <= v && v <= 1000 &&
          0 <= cnt && cnt <= capacity@pre &&
          pos == r + k * w &&
          0 <= k && k <= capacity@pre && 0 <= pos && pos <= capacity@pre &&
          current == old_l[pos] - k * v &&
          -1000000 <= current && current <= 1000000 &&
          0 <= current + k * v && current + k * v <= 1000000 &&
          0 <= head && head <= tail && tail <= k && tail <= capacity@pre + 1 &&
          (head < tail => 0 <= tail - 1 && tail - 1 < capacity@pre + 1) &&
          MKDPTableSafety(weights_l, i, capacity@pre, old_l) &&
          MKDPTableSemantics(weights_l, values_l, counts_l, i, capacity@pre, old_l) &&
          MKDPValueBound(old_l, capacity@pre) &&
          MKTransitionValueBound(old_l, w, v, cnt, capacity@pre) &&
          MKItemResiduePrefixSafety(old_l, dp_l, r, w, cnt, k, capacity@pre) &&
          MKItemResiduePrefixSemantics(old_l, dp_l, r, w, v, cnt, k, capacity@pre) &&
          MKQueueDropSafety(old_l, qidx_l, qval_l, head, tail, r, w, k, capacity@pre) &&
          MKQueuePendingSemantics(old_l, qidx_l, qval_l, head, tail, r, w, v, cnt, k, current) &&
          IntArray::full(weights@pre, n@pre, weights_l) *
          IntArray::full(values@pre, n@pre, values_l) *
          IntArray::full(counts@pre, n@pre, counts_l) *
          IntArray::full(dp@pre, capacity@pre + 1, dp_l) *
          IntArray::full(old@pre, capacity@pre + 1, old_l) *
          IntArray::full(q_idx@pre, capacity@pre + 1, qidx_l) *
          IntArray::full(q_val@pre, capacity@pre + 1, qval_l) &&
          (forall (idx : Z), (0 <= idx && idx < n@pre) =>
            (1 <= weights_l[idx] && weights_l[idx] <= capacity@pre + 1 &&
             0 <= values_l[idx] && values_l[idx] <= 1000 &&
             0 <= counts_l[idx] && counts_l[idx] <= capacity@pre))
        */
        while (head < tail && q_val[tail - 1] <= current) {
          tail--;
        }

        q_idx[tail] = k;
        q_val[tail] = current;
        tail++;

        /*@ Assert
          exists dp_l old_l qidx_l qval_l,
          weights == weights@pre && values == values@pre && counts == counts@pre &&
          n == n@pre && capacity == capacity@pre &&
          dp == dp@pre && old == old@pre && q_idx == q_idx@pre && q_val == q_val@pre &&
          0 <= n@pre && n@pre <= 1000 &&
          0 <= capacity@pre && capacity@pre <= 1000 &&
          Zlength(weights_l) == n@pre &&
          Zlength(values_l) == n@pre &&
          Zlength(counts_l) == n@pre &&
          Zlength(dp_l) == capacity@pre + 1 &&
          Zlength(old_l) == capacity@pre + 1 &&
          Zlength(qidx_l) == capacity@pre + 1 &&
          Zlength(qval_l) == capacity@pre + 1 &&
          0 <= i && i < n@pre &&
          0 <= r && r < w && r <= capacity@pre &&
          w == weights_l[i] &&
          v == values_l[i] &&
          cnt == counts_l[i] &&
          1 <= w && w <= capacity@pre + 1 &&
          0 <= v && v <= 1000 &&
          0 <= cnt && cnt <= capacity@pre &&
          pos == r + k * w &&
          0 <= k && k <= capacity@pre && 0 <= pos && pos <= capacity@pre &&
          current == old_l[pos] - k * v &&
          -1000000 <= current && current <= 1000000 &&
          0 <= current + k * v && current + k * v <= 1000000 &&
          0 <= head && head < tail && tail <= k + 1 && tail <= capacity@pre + 1 &&
          MKDPTableSafety(weights_l, i, capacity@pre, old_l) &&
          MKDPTableSemantics(weights_l, values_l, counts_l, i, capacity@pre, old_l) &&
          MKDPValueBound(old_l, capacity@pre) &&
          MKTransitionValueBound(old_l, w, v, cnt, capacity@pre) &&
          MKItemResiduePrefixSafety(old_l, dp_l, r, w, cnt, k, capacity@pre) &&
          MKItemResiduePrefixSemantics(old_l, dp_l, r, w, v, cnt, k, capacity@pre) &&
          MKQueueResultSafety(old_l, qidx_l, qval_l, head, tail, r, w, k + 1, capacity@pre) &&
          MKQueueResultSemantics(old_l, qidx_l, qval_l, head, tail, r, w, v, cnt, k + 1, capacity@pre) &&
          MKTransitionSafety(old_l, w, cnt, capacity@pre, pos) &&
          MKTransitionSemantics(old_l, w, v, cnt, capacity@pre, pos, qval_l[head] + k * v) &&
          0 <= qval_l[head] + k * v && qval_l[head] + k * v <= 1000000 &&
          IntArray::full(weights@pre, n@pre, weights_l) *
          IntArray::full(values@pre, n@pre, values_l) *
          IntArray::full(counts@pre, n@pre, counts_l) *
          IntArray::full(dp@pre, capacity@pre + 1, dp_l) *
          IntArray::full(old@pre, capacity@pre + 1, old_l) *
          IntArray::full(q_idx@pre, capacity@pre + 1, qidx_l) *
          IntArray::full(q_val@pre, capacity@pre + 1, qval_l) &&
          (forall (idx : Z), (0 <= idx && idx < n@pre) =>
            (1 <= weights_l[idx] && weights_l[idx] <= capacity@pre + 1 &&
             0 <= values_l[idx] && values_l[idx] <= 1000 &&
             0 <= counts_l[idx] && counts_l[idx] <= capacity@pre))
        */

        dp[pos] = q_val[head] + k * v;
        k++;
      }

      /*@ Assert
        exists dp_l old_l qidx_l qval_l,
        weights == weights@pre && values == values@pre && counts == counts@pre &&
        n == n@pre && capacity == capacity@pre &&
        dp == dp@pre && old == old@pre && q_idx == q_idx@pre && q_val == q_val@pre &&
        0 <= n@pre && n@pre <= 1000 &&
        0 <= capacity@pre && capacity@pre <= 1000 &&
        Zlength(weights_l) == n@pre &&
        Zlength(values_l) == n@pre &&
        Zlength(counts_l) == n@pre &&
        Zlength(dp_l) == capacity@pre + 1 &&
        Zlength(old_l) == capacity@pre + 1 &&
        Zlength(qidx_l) == capacity@pre + 1 &&
        Zlength(qval_l) == capacity@pre + 1 &&
        0 <= i && i < n@pre &&
        0 <= r && r < w && r <= capacity@pre &&
        w == weights_l[i] &&
        v == values_l[i] &&
        cnt == counts_l[i] &&
        1 <= w && w <= capacity@pre + 1 &&
        0 <= v && v <= 1000 &&
        0 <= cnt && cnt <= capacity@pre &&
        0 <= k && k <= capacity@pre + 1 &&
        0 <= head && head <= tail && tail <= k && tail <= capacity@pre + 1 &&
        MKDPTableSafety(weights_l, i, capacity@pre, old_l) &&
        MKDPTableSemantics(weights_l, values_l, counts_l, i, capacity@pre, old_l) &&
        MKDPValueBound(old_l, capacity@pre) &&
        MKTransitionValueBound(old_l, w, v, cnt, capacity@pre) &&
        MKItemResidueProgressSafety(old_l, dp_l, r + 1, w, cnt, capacity@pre) &&
        MKItemResidueProgressSemantics(old_l, dp_l, r + 1, w, v, cnt, capacity@pre) &&
        IntArray::full(weights@pre, n@pre, weights_l) *
        IntArray::full(values@pre, n@pre, values_l) *
        IntArray::full(counts@pre, n@pre, counts_l) *
        IntArray::full(dp@pre, capacity@pre + 1, dp_l) *
        IntArray::full(old@pre, capacity@pre + 1, old_l) *
        IntArray::full(q_idx@pre, capacity@pre + 1, qidx_l) *
        IntArray::full(q_val@pre, capacity@pre + 1, qval_l) &&
        (forall (idx : Z), (0 <= idx && idx < n@pre) =>
          (1 <= weights_l[idx] && weights_l[idx] <= capacity@pre + 1 &&
           0 <= values_l[idx] && values_l[idx] <= 1000 &&
           0 <= counts_l[idx] && counts_l[idx] <= capacity@pre))
      */
    }
    /*@ Assert
      exists dp_l old_l qidx_l qval_l,
      weights == weights@pre && values == values@pre && counts == counts@pre &&
      n == n@pre && capacity == capacity@pre &&
      dp == dp@pre && old == old@pre && q_idx == q_idx@pre && q_val == q_val@pre &&
      0 <= n@pre && n@pre <= 1000 &&
      0 <= capacity@pre && capacity@pre <= 1000 &&
      Zlength(weights_l) == n@pre &&
      Zlength(values_l) == n@pre &&
      Zlength(counts_l) == n@pre &&
      Zlength(dp_l) == capacity@pre + 1 &&
      Zlength(old_l) == capacity@pre + 1 &&
      Zlength(qidx_l) == capacity@pre + 1 &&
      Zlength(qval_l) == capacity@pre + 1 &&
      0 <= i && i < n@pre &&
      w == weights_l[i] &&
      v == values_l[i] &&
      cnt == counts_l[i] &&
      1 <= w && w <= capacity@pre + 1 &&
      0 <= v && v <= 1000 &&
      0 <= cnt && cnt <= capacity@pre &&
      MKDPTableSafety(weights_l, i + 1, capacity@pre, dp_l) &&
      MKDPTableSemantics(weights_l, values_l, counts_l, i + 1, capacity@pre, dp_l) &&
      IntArray::full(weights@pre, n@pre, weights_l) *
      IntArray::full(values@pre, n@pre, values_l) *
      IntArray::full(counts@pre, n@pre, counts_l) *
      IntArray::full(dp@pre, capacity@pre + 1, dp_l) *
      IntArray::full(old@pre, capacity@pre + 1, old_l) *
      IntArray::full(q_idx@pre, capacity@pre + 1, qidx_l) *
      IntArray::full(q_val@pre, capacity@pre + 1, qval_l) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) =>
        (1 <= weights_l[idx] && weights_l[idx] <= capacity@pre + 1 &&
         0 <= values_l[idx] && values_l[idx] <= 1000 &&
         0 <= counts_l[idx] && counts_l[idx] <= capacity@pre))
    */
  }

  /*@ Assert
      exists dp_l old_l qidx_l qval_l,
      weights == weights@pre && values == values@pre && counts == counts@pre &&
      n == n@pre && capacity == capacity@pre &&
      dp == dp@pre && old == old@pre && q_idx == q_idx@pre && q_val == q_val@pre &&
      0 <= n@pre && n@pre <= 1000 &&
      0 <= capacity@pre && capacity@pre <= 1000 &&
      Zlength(weights_l) == n@pre &&
      Zlength(values_l) == n@pre &&
      Zlength(counts_l) == n@pre &&
      Zlength(dp_l) == capacity@pre + 1 &&
      Zlength(old_l) == capacity@pre + 1 &&
      Zlength(qidx_l) == capacity@pre + 1 &&
      Zlength(qval_l) == capacity@pre + 1 &&
      MKDPTableSafety(weights_l, n@pre, capacity@pre, dp_l) &&
      MKDPTableSemantics(weights_l, values_l, counts_l, n@pre, capacity@pre, dp_l) &&
      MultipleKnapsackAnswer(weights_l, values_l, counts_l, capacity@pre, dp_l[capacity@pre]) &&
      IntArray::full(weights@pre, n@pre, weights_l) *
      IntArray::full(values@pre, n@pre, values_l) *
      IntArray::full(counts@pre, n@pre, counts_l) *
      IntArray::full(dp@pre, capacity@pre + 1, dp_l) *
      IntArray::full(old@pre, capacity@pre + 1, old_l) *
      IntArray::full(q_idx@pre, capacity@pre + 1, qidx_l) *
      IntArray::full(q_val@pre, capacity@pre + 1, qval_l)
   */
  return dp[capacity];
}
