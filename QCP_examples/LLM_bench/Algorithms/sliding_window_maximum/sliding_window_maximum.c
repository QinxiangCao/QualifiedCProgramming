



/*@ Extern Coq
      (SWMInputSafe : list Z -> Z -> Z -> Prop)
	      (WindowMaxValue : list Z -> Z -> Z -> Z -> Prop)
	      (SlidingWindowMaximum : list Z -> Z -> list Z -> Prop)
	      (SWMOutputPrefixShape : list Z -> Z -> Z -> list Z -> Prop)
	      (SWMOutputPrefix : list Z -> Z -> Z -> list Z -> Prop)
	      (SWMQueueStorageSafe : list Z -> list Z -> Z -> Z -> Z -> Prop)
	      (SWMQueueState : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
	      (SWMQueueDropLoopState : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
	      (SWMQueueAfterDrop : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
	      (SWMQueuePendingState : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
	 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_lib */

void maxSlidingWindow(int *nums, int n, int k, int *out, int *q)
/*@ With (l : list Z) (q0 : list Z)
    Require
      1 <= k && k <= n && n <= 100000 &&
      Zlength(l) == n &&
      Zlength(q0) == n &&
      SWMInputSafe(l, n, k) &&
      IntArray::full(nums, n, l) *
      IntArray::undef_full(out, n - k + 1) *
      IntArray::full(q, n, q0)
    Ensure
      exists out_l q_l,
      SlidingWindowMaximum(l, k, out_l) &&
      IntArray::full(nums, n, l) *
      IntArray::full(out, n - k + 1, out_l) *
      IntArray::full(q, n, q_l)
 */
{
  int head = 0;
  int tail = 0;
  int out_idx = 0;

  /*@ Inv Assert
      exists out_l q_l,
      nums == nums@pre && n == n@pre && k == k@pre &&
      out == out@pre && q == q@pre &&
      1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      Zlength(q_l) == n@pre &&
      0 <= i && i <= n@pre &&
      0 <= head && head <= tail && tail <= i &&
      0 <= out_idx && out_idx <= n@pre - k@pre + 1 &&
      (i < k@pre => out_idx == 0) &&
      (k@pre <= i => out_idx == i - k@pre + 1) &&
	      (k@pre <= i => head < tail) &&
	      SWMInputSafe(l, n@pre, k@pre) &&
	      SWMOutputPrefixShape(l, k@pre, out_idx, out_l) &&
	      SWMOutputPrefix(l, k@pre, out_idx, out_l) &&
	      SWMQueueStorageSafe(l, q_l, head, tail, i) &&
	      SWMQueueState(l, q_l, head, tail, i, k@pre) &&
	      (forall (pos : Z), (head <= pos && pos < tail) => (0 <= q_l[pos] && q_l[pos] < n@pre)) &&
	      IntArray::full(nums@pre, n@pre, l) *
      IntArray::seg(out@pre, 0, out_idx, out_l) *
      IntArray::undef_seg(out@pre, out_idx, n@pre - k@pre + 1) *
      IntArray::full(q@pre, n@pre, q_l)
   */
  for (int i = 0; i < n; ++i) {
    /*@ Inv Assert
      exists out_l q_l,
      nums == nums@pre && n == n@pre && k == k@pre &&
      out == out@pre && q == q@pre &&
      1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      Zlength(q_l) == n@pre &&
      0 <= i && i < n@pre &&
      0 <= head && head <= tail && tail <= i &&
      0 <= out_idx && out_idx <= n@pre - k@pre + 1 &&
	      (i < k@pre => out_idx == 0) &&
	      (k@pre <= i => out_idx == i - k@pre + 1) &&
	      SWMInputSafe(l, n@pre, k@pre) &&
	      SWMOutputPrefixShape(l, k@pre, out_idx, out_l) &&
	      SWMOutputPrefix(l, k@pre, out_idx, out_l) &&
	      SWMQueueStorageSafe(l, q_l, head, tail, i) &&
	      SWMQueueDropLoopState(l, q_l, head, tail, i, k@pre) &&
	      (forall (pos : Z), (head <= pos && pos < tail) => (0 <= q_l[pos] && q_l[pos] < n@pre)) &&
      IntArray::full(nums@pre, n@pre, l) *
      IntArray::seg(out@pre, 0, out_idx, out_l) *
      IntArray::undef_seg(out@pre, out_idx, n@pre - k@pre + 1) *
      IntArray::full(q@pre, n@pre, q_l)
    */
    while (head < tail && q[head] <= i - k) {
      head++;
    }

    /*@ Assert
      exists out_l q_l,
      nums == nums@pre && n == n@pre && k == k@pre &&
      out == out@pre && q == q@pre &&
      1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      Zlength(q_l) == n@pre &&
      0 <= i && i < n@pre &&
      0 <= head && head <= tail && tail <= i &&
      0 <= out_idx && out_idx <= n@pre - k@pre + 1 &&
	      (i < k@pre => out_idx == 0) &&
	      (k@pre <= i => out_idx == i - k@pre + 1) &&
	      SWMInputSafe(l, n@pre, k@pre) &&
	      SWMOutputPrefixShape(l, k@pre, out_idx, out_l) &&
	      SWMOutputPrefix(l, k@pre, out_idx, out_l) &&
	      SWMQueueStorageSafe(l, q_l, head, tail, i) &&
	      SWMQueueAfterDrop(l, q_l, head, tail, i, k@pre) &&
	      (forall (pos : Z), (head <= pos && pos < tail) => (0 <= q_l[pos] && q_l[pos] < n@pre)) &&
	      (head < tail => (0 <= tail - 1 && tail - 1 < n@pre && 0 <= q_l[tail - 1] && q_l[tail - 1] < n@pre)) &&
      IntArray::full(nums@pre, n@pre, l) *
      IntArray::seg(out@pre, 0, out_idx, out_l) *
      IntArray::undef_seg(out@pre, out_idx, n@pre - k@pre + 1) *
      IntArray::full(q@pre, n@pre, q_l)
    */
    /*@ Inv Assert
      exists out_l q_l,
      nums == nums@pre && n == n@pre && k == k@pre &&
      out == out@pre && q == q@pre &&
      1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      Zlength(q_l) == n@pre &&
      0 <= i && i < n@pre &&
      0 <= head && head <= tail && tail <= i &&
      0 <= out_idx && out_idx <= n@pre - k@pre + 1 &&
	      (i < k@pre => out_idx == 0) &&
	      (k@pre <= i => out_idx == i - k@pre + 1) &&
	      SWMInputSafe(l, n@pre, k@pre) &&
	      SWMOutputPrefixShape(l, k@pre, out_idx, out_l) &&
	      SWMOutputPrefix(l, k@pre, out_idx, out_l) &&
	      SWMQueueStorageSafe(l, q_l, head, tail, i) &&
	      SWMQueuePendingState(l, q_l, head, tail, i, k@pre) &&
	      (forall (pos : Z), (head <= pos && pos < tail) => (0 <= q_l[pos] && q_l[pos] < n@pre)) &&
	      (head < tail => (0 <= tail - 1 && tail - 1 < n@pre && 0 <= q_l[tail - 1] && q_l[tail - 1] < n@pre)) &&
      IntArray::full(nums@pre, n@pre, l) *
      IntArray::seg(out@pre, 0, out_idx, out_l) *
      IntArray::undef_seg(out@pre, out_idx, n@pre - k@pre + 1) *
      IntArray::full(q@pre, n@pre, q_l)
    */
    while (head < tail && nums[q[tail - 1]] <= nums[i]) {
      tail--;
    }

    /*@ Assert
      exists out_l q_l,
      nums == nums@pre && n == n@pre && k == k@pre &&
      out == out@pre && q == q@pre &&
      1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      Zlength(q_l) == n@pre &&
      0 <= i && i < n@pre &&
      0 <= head && head <= tail && tail <= i &&
      0 <= out_idx && out_idx <= n@pre - k@pre + 1 &&
	      (i < k@pre => out_idx == 0) &&
	      (k@pre <= i => out_idx == i - k@pre + 1) &&
	      SWMInputSafe(l, n@pre, k@pre) &&
	      SWMOutputPrefixShape(l, k@pre, out_idx, out_l) &&
	      SWMOutputPrefix(l, k@pre, out_idx, out_l) &&
	      SWMQueueStorageSafe(l, q_l, head, tail, i) &&
	      SWMQueuePendingState(l, q_l, head, tail, i, k@pre) &&
	      (forall (pos : Z), (head <= pos && pos < tail) => (0 <= q_l[pos] && q_l[pos] < n@pre)) &&
	      (head < tail => (0 <= tail - 1 && tail - 1 < n@pre && 0 <= q_l[tail - 1] && q_l[tail - 1] < n@pre)) &&
      (head < tail => l[q_l[tail - 1]] > l[i]) &&
      IntArray::full(nums@pre, n@pre, l) *
      IntArray::seg(out@pre, 0, out_idx, out_l) *
      IntArray::undef_seg(out@pre, out_idx, n@pre - k@pre + 1) *
      IntArray::full(q@pre, n@pre, q_l)
    */
    q[tail] = i;
    tail++;

    /*@ Assert
      exists out_l q_l,
      nums == nums@pre && n == n@pre && k == k@pre &&
      out == out@pre && q == q@pre &&
      1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      Zlength(q_l) == n@pre &&
      0 <= i && i < n@pre &&
      0 <= head && head < tail && tail <= i + 1 &&
      0 <= out_idx && out_idx <= n@pre - k@pre + 1 &&
	      (i < k@pre => out_idx == 0) &&
	      (k@pre <= i => out_idx == i - k@pre + 1) &&
	      SWMInputSafe(l, n@pre, k@pre) &&
	      SWMOutputPrefixShape(l, k@pre, out_idx, out_l) &&
	      SWMOutputPrefix(l, k@pre, out_idx, out_l) &&
	      SWMQueueStorageSafe(l, q_l, head, tail, i + 1) &&
	      SWMQueueState(l, q_l, head, tail, i + 1, k@pre) &&
	      (forall (pos : Z), (head <= pos && pos < tail) => (0 <= q_l[pos] && q_l[pos] < n@pre)) &&
	      IntArray::full(nums@pre, n@pre, l) *
      IntArray::seg(out@pre, 0, out_idx, out_l) *
      IntArray::undef_seg(out@pre, out_idx, n@pre - k@pre + 1) *
      IntArray::full(q@pre, n@pre, q_l)
    */
    if (i >= k - 1) {
      /*@ Assert
        exists out_l q_l,
        nums == nums@pre && n == n@pre && k == k@pre &&
        out == out@pre && q == q@pre &&
        1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
        Zlength(l) == n@pre &&
        Zlength(q_l) == n@pre &&
        0 <= i && i < n@pre &&
        0 <= head && head < tail && tail <= i + 1 &&
        head < n@pre &&
        0 <= q_l[head] && q_l[head] < n@pre &&
	        out_idx == i - k@pre + 1 &&
	        0 <= out_idx && out_idx < n@pre - k@pre + 1 &&
	        SWMInputSafe(l, n@pre, k@pre) &&
	        SWMOutputPrefixShape(l, k@pre, out_idx, out_l) &&
	        SWMOutputPrefix(l, k@pre, out_idx, out_l) &&
	        SWMQueueStorageSafe(l, q_l, head, tail, i + 1) &&
	        SWMQueueState(l, q_l, head, tail, i + 1, k@pre) &&
	        (forall (pos : Z), (head <= pos && pos < tail) => (0 <= q_l[pos] && q_l[pos] < n@pre)) &&
	        WindowMaxValue(l, i - k@pre + 1, i + 1, l[q_l[head]]) &&
        IntArray::full(nums@pre, n@pre, l) *
        IntArray::seg(out@pre, 0, out_idx, out_l) *
        IntArray::undef_seg(out@pre, out_idx, n@pre - k@pre + 1) *
        IntArray::full(q@pre, n@pre, q_l)
      */
      out[out_idx] = nums[q[head]];
      /*@ Assert
        exists out_l q_l,
        nums == nums@pre && n == n@pre && k == k@pre &&
        out == out@pre && q == q@pre &&
        1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
        Zlength(l) == n@pre &&
        Zlength(q_l) == n@pre &&
        0 <= i && i < n@pre &&
        0 <= head && head < tail && tail <= i + 1 &&
        out_idx == i - k@pre + 1 &&
	        0 <= out_idx && out_idx < n@pre - k@pre + 1 &&
	        SWMInputSafe(l, n@pre, k@pre) &&
	        SWMOutputPrefixShape(l, k@pre, out_idx + 1, out_l) &&
	        SWMOutputPrefix(l, k@pre, out_idx + 1, out_l) &&
	        SWMQueueStorageSafe(l, q_l, head, tail, i + 1) &&
	        SWMQueueState(l, q_l, head, tail, i + 1, k@pre) &&
	        (forall (pos : Z), (head <= pos && pos < tail) => (0 <= q_l[pos] && q_l[pos] < n@pre)) &&
	        IntArray::full(nums@pre, n@pre, l) *
        IntArray::seg(out@pre, 0, out_idx + 1, out_l) *
        IntArray::undef_seg(out@pre, out_idx + 1, n@pre - k@pre + 1) *
        IntArray::full(q@pre, n@pre, q_l)
      */
      out_idx++;
    }
    /*@ Assert
      exists out_l q_l,
      nums == nums@pre && n == n@pre && k == k@pre &&
      out == out@pre && q == q@pre &&
      1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      Zlength(q_l) == n@pre &&
      0 <= i && i < n@pre &&
      0 <= head && head <= tail && tail <= i + 1 &&
      0 <= out_idx && out_idx <= n@pre - k@pre + 1 &&
      (i + 1 < k@pre => out_idx == 0) &&
      (k@pre <= i + 1 => out_idx == i + 1 - k@pre + 1) &&
	      (k@pre <= i + 1 => head < tail) &&
	      SWMInputSafe(l, n@pre, k@pre) &&
	      SWMOutputPrefixShape(l, k@pre, out_idx, out_l) &&
	      SWMOutputPrefix(l, k@pre, out_idx, out_l) &&
	      SWMQueueStorageSafe(l, q_l, head, tail, i + 1) &&
	      SWMQueueState(l, q_l, head, tail, i + 1, k@pre) &&
	      (forall (pos : Z), (head <= pos && pos < tail) => (0 <= q_l[pos] && q_l[pos] < n@pre)) &&
	      IntArray::full(nums@pre, n@pre, l) *
      IntArray::seg(out@pre, 0, out_idx, out_l) *
      IntArray::undef_seg(out@pre, out_idx, n@pre - k@pre + 1) *
      IntArray::full(q@pre, n@pre, q_l)
    */
  }
  /*@ Assert
      exists out_l q_l,
      nums == nums@pre && n == n@pre && k == k@pre &&
      out == out@pre && q == q@pre &&
      1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      Zlength(q_l) == n@pre &&
      0 <= head && head <= tail && tail <= n@pre &&
      out_idx == n@pre - k@pre + 1 &&
      SWMInputSafe(l, n@pre, k@pre) &&
      SlidingWindowMaximum(l, k@pre, out_l) &&
      IntArray::full(nums@pre, n@pre, l) *
      IntArray::full(out@pre, n@pre - k@pre + 1, out_l) *
      IntArray::full(q@pre, n@pre, q_l)
   */
}
