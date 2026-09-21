/* Bounded knapsack: choose one integer quantity per item type, within counts,
   with total weight at most capacity, and return the maximum total value.
   All dynamic programming and queue workspaces are local to the function. */
/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (eq : {A} -> A -> A -> Prop)
      (MultipleKnapsackAnswer : list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (MKDPTableSemantics : list Z -> list Z -> list Z -> Z -> Z -> list Z -> Prop)
      (MKCopyPrefixSemantics : list Z -> list Z -> Z -> Prop)
      (MKTransitionSemantics : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MKItemResidueProgressSemantics : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MKItemResiduePrefixSemantics : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MKQueueDropSemantics : list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MKQueuePendingSemantics : list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (MKQueueResultSemantics : list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_lib */

int multipleKnapsack(int *weights, int *values, int *counts,
                     int n, int capacity)
/*@ With (weights_l : list Z) (values_l : list Z) (counts_l : list Z)
    Require
      0 <= n && n <= 1000 &&
      0 <= capacity && capacity <= 1000 &&
      Zlength(weights_l) == n &&
      Zlength(values_l) == n &&
      Zlength(counts_l) == n &&
      IntArray::full(weights, n, weights_l) *
      IntArray::full(values, n, values_l) *
      IntArray::full(counts, n, counts_l) &&
      Forall(Z::le(1), weights_l) && Forall(Z::ge(capacity + 1), weights_l) &&
      Forall(Z::le(0), values_l) && Forall(Z::ge(1000), values_l) &&
      Forall(Z::le(0), counts_l) && Forall(Z::ge(capacity), counts_l)
    Ensure
      MultipleKnapsackAnswer(weights_l, values_l, counts_l, capacity, __return) &&
      IntArray::full(weights, n, weights_l) *
      IntArray::full(values, n, values_l) *
      IntArray::full(counts, n, counts_l)
 */
{
  int dp[1001];
  int old[1001];
  int q_idx[1001];
  int q_val[1001];

  /*@ Inv Assert
      exists dp_l old0 qidx0 qval0,
      weights == weights@pre && values == values@pre && counts == counts@pre &&
      n == n@pre && capacity == capacity@pre &&
      0 <= n@pre && n@pre <= 1000 &&
      0 <= capacity@pre && capacity@pre <= 1000 &&
      Zlength(weights_l) == n@pre &&
      Zlength(values_l) == n@pre &&
      Zlength(counts_l) == n@pre &&
      Zlength(dp_l) == j &&
      Zlength(old0) == j &&
      Zlength(qidx0) == j &&
      Zlength(qval0) == j &&
      0 <= j && j <= capacity@pre + 1 &&
      Forall(eq(0), dp_l) &&
      IntArray::full(weights@pre, n@pre, weights_l) *
      IntArray::full(values@pre, n@pre, values_l) *
      IntArray::full(counts@pre, n@pre, counts_l) *
      IntArray::seg(dp, 0, j, dp_l) *
      IntArray::undef_seg(dp, j, 1001) *
      IntArray::seg(old, 0, j, old0) *
      IntArray::undef_seg(old, j, 1001) *
      IntArray::seg(q_idx, 0, j, qidx0) *
      IntArray::undef_seg(q_idx, j, 1001) *
      IntArray::seg(q_val, 0, j, qval0) *
      IntArray::undef_seg(q_val, j, 1001) &&
      Forall(Z::le(1), weights_l) && Forall(Z::ge(capacity@pre + 1), weights_l) &&
      Forall(Z::le(0), values_l) && Forall(Z::ge(1000), values_l) &&
      Forall(Z::le(0), counts_l) && Forall(Z::ge(capacity@pre), counts_l)
   */
  for (int j = 0; j <= capacity; ++j) {
    dp[j] = 0;
    old[j] = 0;
    q_idx[j] = 0;
    q_val[j] = 0;
  }

  /*@ Inv Assert
      exists dp_l old_l qidx_l qval_l,
      weights == weights@pre && values == values@pre && counts == counts@pre &&
      n == n@pre && capacity == capacity@pre &&
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
      MKDPTableSemantics(weights_l, values_l, counts_l, i, capacity@pre, dp_l) &&
      IntArray::full(weights@pre, n@pre, weights_l) *
      IntArray::full(values@pre, n@pre, values_l) *
      IntArray::full(counts@pre, n@pre, counts_l) *
      IntArray::full(dp, capacity@pre + 1, dp_l) *
      IntArray::undef_seg(dp, capacity@pre + 1, 1001) *
      IntArray::full(old, capacity@pre + 1, old_l) *
      IntArray::undef_seg(old, capacity@pre + 1, 1001) *
      IntArray::full(q_idx, capacity@pre + 1, qidx_l) *
      IntArray::undef_seg(q_idx, capacity@pre + 1, 1001) *
      IntArray::full(q_val, capacity@pre + 1, qval_l) *
      IntArray::undef_seg(q_val, capacity@pre + 1, 1001) &&
      Forall(Z::le(1), weights_l) && Forall(Z::ge(capacity@pre + 1), weights_l) &&
      Forall(Z::le(0), values_l) && Forall(Z::ge(1000), values_l) &&
      Forall(Z::le(0), counts_l) && Forall(Z::ge(capacity@pre), counts_l)
   */
  for (int i = 0; i < n; ++i) {
    /*@ Inv Assert
        exists dp_l old_l qidx_l qval_l,
        weights == weights@pre && values == values@pre && counts == counts@pre &&
        n == n@pre && capacity == capacity@pre &&
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
        MKDPTableSemantics(weights_l, values_l, counts_l, i, capacity@pre, dp_l) &&
        MKCopyPrefixSemantics(dp_l, old_l, j) &&
        IntArray::full(weights@pre, n@pre, weights_l) *
        IntArray::full(values@pre, n@pre, values_l) *
        IntArray::full(counts@pre, n@pre, counts_l) *
        IntArray::full(dp, capacity@pre + 1, dp_l) *
      IntArray::undef_seg(dp, capacity@pre + 1, 1001) *
        IntArray::full(old, capacity@pre + 1, old_l) *
      IntArray::undef_seg(old, capacity@pre + 1, 1001) *
        IntArray::full(q_idx, capacity@pre + 1, qidx_l) *
      IntArray::undef_seg(q_idx, capacity@pre + 1, 1001) *
        IntArray::full(q_val, capacity@pre + 1, qval_l) *
      IntArray::undef_seg(q_val, capacity@pre + 1, 1001) &&
        Forall(Z::le(1), weights_l) && Forall(Z::ge(capacity@pre + 1), weights_l) &&
        Forall(Z::le(0), values_l) && Forall(Z::ge(1000), values_l) &&
        Forall(Z::le(0), counts_l) && Forall(Z::ge(capacity@pre), counts_l)
     */
    for (int j = 0; j <= capacity; ++j) {
      old[j] = dp[j];
    }

    int w = weights[i];
    int v = values[i];
    int cnt = counts[i];

    /*@ Inv Assert
        exists dp_l old_l qidx_l qval_l,
        weights == weights@pre && values == values@pre && counts == counts@pre &&
        n == n@pre && capacity == capacity@pre &&
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
        MKDPTableSemantics(weights_l, values_l, counts_l, i, capacity@pre, old_l) &&
        Forall(Z::le(0), old_l) && Forall(Z::ge(1000000), old_l) &&
        (forall (p a : Z), (0 <= p && p <= capacity@pre &&
        MKTransitionSemantics(old_l, w, v, cnt, capacity@pre, p, a)) =>
        (0 <= a && a <= 1000000)) &&
        MKItemResidueProgressSemantics(old_l, dp_l, r, w, v, cnt, capacity@pre) &&
        IntArray::full(weights@pre, n@pre, weights_l) *
        IntArray::full(values@pre, n@pre, values_l) *
        IntArray::full(counts@pre, n@pre, counts_l) *
        IntArray::full(dp, capacity@pre + 1, dp_l) *
      IntArray::undef_seg(dp, capacity@pre + 1, 1001) *
        IntArray::full(old, capacity@pre + 1, old_l) *
      IntArray::undef_seg(old, capacity@pre + 1, 1001) *
        IntArray::full(q_idx, capacity@pre + 1, qidx_l) *
      IntArray::undef_seg(q_idx, capacity@pre + 1, 1001) *
        IntArray::full(q_val, capacity@pre + 1, qval_l) *
      IntArray::undef_seg(q_val, capacity@pre + 1, 1001) &&
        Forall(Z::le(1), weights_l) && Forall(Z::ge(capacity@pre + 1), weights_l) &&
        Forall(Z::le(0), values_l) && Forall(Z::ge(1000), values_l) &&
        Forall(Z::le(0), counts_l) && Forall(Z::ge(capacity@pre), counts_l)
     */
    for (int r = 0; r < w && r <= capacity; ++r) {
      int head = 0;
      int tail = 0;
      int k = 0;

      /*@ Inv Assert
          exists dp_l old_l qidx_l qval_l,
          weights == weights@pre && values == values@pre && counts == counts@pre &&
          n == n@pre && capacity == capacity@pre &&
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
          MKDPTableSemantics(weights_l, values_l, counts_l, i, capacity@pre, old_l) &&
          Forall(Z::le(0), old_l) && Forall(Z::ge(1000000), old_l) &&
          (forall (p a : Z), (0 <= p && p <= capacity@pre &&
          MKTransitionSemantics(old_l, w, v, cnt, capacity@pre, p, a)) =>
          (0 <= a && a <= 1000000)) &&
          MKItemResiduePrefixSemantics(old_l, dp_l, r, w, v, cnt, k, capacity@pre) &&
          MKQueueResultSemantics(old_l, qidx_l, qval_l, head, tail, r, w, v, cnt, k, capacity@pre) &&
          Forall(Z::le(-((k - 1) * v)), sublist(head, tail, qval_l)) &&
          Forall(Z::ge(1000000 - ((k - 1) * v)), sublist(head, tail, qval_l)) &&
          IntArray::full(weights@pre, n@pre, weights_l) *
          IntArray::full(values@pre, n@pre, values_l) *
          IntArray::full(counts@pre, n@pre, counts_l) *
          IntArray::full(dp, capacity@pre + 1, dp_l) *
      IntArray::undef_seg(dp, capacity@pre + 1, 1001) *
          IntArray::full(old, capacity@pre + 1, old_l) *
      IntArray::undef_seg(old, capacity@pre + 1, 1001) *
          IntArray::full(q_idx, capacity@pre + 1, qidx_l) *
      IntArray::undef_seg(q_idx, capacity@pre + 1, 1001) *
          IntArray::full(q_val, capacity@pre + 1, qval_l) *
      IntArray::undef_seg(q_val, capacity@pre + 1, 1001) &&
          Forall(Z::le(1), weights_l) && Forall(Z::ge(capacity@pre + 1), weights_l) &&
          Forall(Z::le(0), values_l) && Forall(Z::ge(1000), values_l) &&
          Forall(Z::le(0), counts_l) && Forall(Z::ge(capacity@pre), counts_l)
       */
      for (int pos = r; pos <= capacity; pos += w) {
        int current = old[pos] - k * v;

        /*@ Inv Assert
            exists dp_l old_l qidx_l qval_l,
            weights == weights@pre && values == values@pre && counts == counts@pre &&
            n == n@pre && capacity == capacity@pre &&
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
            MKDPTableSemantics(weights_l, values_l, counts_l, i, capacity@pre, old_l) &&
            Forall(Z::le(0), old_l) && Forall(Z::ge(1000000), old_l) &&
            (forall (p a : Z), (0 <= p && p <= capacity@pre &&
            MKTransitionSemantics(old_l, w, v, cnt, capacity@pre, p, a)) =>
            (0 <= a && a <= 1000000)) &&
            MKItemResiduePrefixSemantics(old_l, dp_l, r, w, v, cnt, k, capacity@pre) &&
            MKQueueDropSemantics(old_l, qidx_l, qval_l, head, tail, r, w, v, cnt, k) &&
            Forall(Z::le(-((k - 1) * v)), sublist(head, tail, qval_l)) &&
            Forall(Z::ge(1000000 - ((k - 1) * v)), sublist(head, tail, qval_l)) &&
            IntArray::full(weights@pre, n@pre, weights_l) *
            IntArray::full(values@pre, n@pre, values_l) *
            IntArray::full(counts@pre, n@pre, counts_l) *
            IntArray::full(dp, capacity@pre + 1, dp_l) *
      IntArray::undef_seg(dp, capacity@pre + 1, 1001) *
            IntArray::full(old, capacity@pre + 1, old_l) *
      IntArray::undef_seg(old, capacity@pre + 1, 1001) *
            IntArray::full(q_idx, capacity@pre + 1, qidx_l) *
      IntArray::undef_seg(q_idx, capacity@pre + 1, 1001) *
            IntArray::full(q_val, capacity@pre + 1, qval_l) *
      IntArray::undef_seg(q_val, capacity@pre + 1, 1001) &&
            Forall(Z::le(1), weights_l) && Forall(Z::ge(capacity@pre + 1), weights_l) &&
            Forall(Z::le(0), values_l) && Forall(Z::ge(1000), values_l) &&
            Forall(Z::le(0), counts_l) && Forall(Z::ge(capacity@pre), counts_l)
         */
        while (head < tail && q_idx[head] < k - cnt) {
          head++;
        }

        /*@ Inv Assert
            exists dp_l old_l qidx_l qval_l,
            weights == weights@pre && values == values@pre && counts == counts@pre &&
            n == n@pre && capacity == capacity@pre &&
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
            MKDPTableSemantics(weights_l, values_l, counts_l, i, capacity@pre, old_l) &&
            Forall(Z::le(0), old_l) && Forall(Z::ge(1000000), old_l) &&
            (forall (p a : Z), (0 <= p && p <= capacity@pre &&
            MKTransitionSemantics(old_l, w, v, cnt, capacity@pre, p, a)) =>
            (0 <= a && a <= 1000000)) &&
            MKItemResiduePrefixSemantics(old_l, dp_l, r, w, v, cnt, k, capacity@pre) &&
            MKQueuePendingSemantics(old_l, qidx_l, qval_l, head, tail, r, w, v, cnt, k, current) &&
            Forall(Z::le(-(k * v)), sublist(head, tail, qval_l)) &&
            Forall(Z::ge(1000000 - (k * v)), sublist(head, tail, qval_l)) &&
            IntArray::full(weights@pre, n@pre, weights_l) *
            IntArray::full(values@pre, n@pre, values_l) *
            IntArray::full(counts@pre, n@pre, counts_l) *
            IntArray::full(dp, capacity@pre + 1, dp_l) *
      IntArray::undef_seg(dp, capacity@pre + 1, 1001) *
            IntArray::full(old, capacity@pre + 1, old_l) *
      IntArray::undef_seg(old, capacity@pre + 1, 1001) *
            IntArray::full(q_idx, capacity@pre + 1, qidx_l) *
      IntArray::undef_seg(q_idx, capacity@pre + 1, 1001) *
            IntArray::full(q_val, capacity@pre + 1, qval_l) *
      IntArray::undef_seg(q_val, capacity@pre + 1, 1001) &&
            Forall(Z::le(1), weights_l) && Forall(Z::ge(capacity@pre + 1), weights_l) &&
            Forall(Z::le(0), values_l) && Forall(Z::ge(1000), values_l) &&
            Forall(Z::le(0), counts_l) && Forall(Z::ge(capacity@pre), counts_l)
         */
        while (head < tail && q_val[tail - 1] <= current) {
          tail--;
        }

        q_idx[tail] = k;
        q_val[tail] = current;
        tail++;



        dp[pos] = q_val[head] + k * v;
        k++;
      }

    }

  }

  int answer = dp[capacity];
  /*@ Assert
      weights == weights@pre && values == values@pre && counts == counts@pre &&
      n == n@pre && capacity == capacity@pre &&
      MultipleKnapsackAnswer(weights_l, values_l, counts_l, capacity, answer) &&
      IntArray::full(weights, n, weights_l) *
      IntArray::full(values, n, values_l) *
      IntArray::full(counts, n, counts_l) *
      IntArray::undef_full(dp, 1001) *
      IntArray::undef_full(old, 1001) *
      IntArray::undef_full(q_idx, 1001) *
      IntArray::undef_full(q_val, 1001)
   */
  return answer;
}
