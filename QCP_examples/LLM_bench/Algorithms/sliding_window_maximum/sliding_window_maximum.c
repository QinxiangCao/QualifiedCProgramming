



/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (Z::gt : Z -> Z -> Prop)
      (sublist : {A} -> Z -> Z -> list A -> list A)
	      (WindowMaxValue : list Z -> Z -> Z -> Z -> Prop)
	      (SlidingWindowMaximum : list Z -> Z -> list Z -> Prop)
	      (SWMOutputPrefix : list Z -> Z -> Z -> list Z -> Prop)
	      (SWMQueueState : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
	      (SWMQueueDropLoopState : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
	      (SWMQueueAfterDrop : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
	      (SWMQueuePendingState : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
	 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_lib */

void maxSlidingWindow(int *nums, int n, int k, int *out)
/*@ With (l : list Z)
    Require
      1 <= k && k <= n && n <= 100000 &&
      Zlength(l) == n &&
      Forall(Z::le(-10000), l) && Forall(Z::ge(10000), l) &&
      IntArray::full(nums, n, l) *
      IntArray::undef_full(out, n - k + 1)
    Ensure
      exists out_l,
      SlidingWindowMaximum(l, k, out_l) &&
      IntArray::full(nums, n, l) *
      IntArray::full(out, n - k + 1, out_l)
 */
{
  int q[100000];
  /*@ Inv Assert
      exists q_init,
      nums == nums@pre && n == n@pre && k == k@pre && out == out@pre &&
      1 <= k && k <= n && n <= 100000 && Zlength(l) == n &&
      Forall(Z::le(-10000), l) && Forall(Z::ge(10000), l) &&
      0 <= z && z <= n && Zlength(q_init) == z &&
      IntArray::full(nums, n, l) * IntArray::undef_full(out, n - k + 1) *
      IntArray::seg(q, 0, z, q_init) * IntArray::undef_seg(q, z, n) *
      IntArray::undef_seg(q, n, 100000)
   */
  for (int z = 0; z < n; ++z) {
    q[z] = 0;
  }

  int head = 0;
  int tail = 0;
  int out_idx = 0;

  /*@ Inv Assert
      exists out_l q_l,
      nums == nums@pre && n == n@pre && k == k@pre &&
      out == out@pre &&
      1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      Zlength(q_l) == n@pre &&
      0 <= i && i <= n@pre &&
      0 <= head && head <= tail && tail <= i &&
      0 <= out_idx && out_idx <= n@pre - k@pre + 1 &&
      (i < k@pre => out_idx == 0) &&
      (k@pre <= i => out_idx == i - k@pre + 1) &&
	      (k@pre <= i => head < tail) &&
	      Forall(Z::le(-10000), l) && Forall(Z::ge(10000), l) &&
	      Zlength(out_l) == out_idx &&
	      SWMOutputPrefix(l, k@pre, out_idx, out_l) &&
	      SWMQueueState(l, q_l, head, tail, i, k@pre) &&
	      Forall(Z::le(0), sublist(head, tail, q_l)) && Forall(Z::gt(n@pre), sublist(head, tail, q_l)) &&
	      IntArray::full(nums@pre, n@pre, l) *
      IntArray::seg(out@pre, 0, out_idx, out_l) *
      IntArray::undef_seg(out@pre, out_idx, n@pre - k@pre + 1) *
      IntArray::full(q, n@pre, q_l) *
      IntArray::undef_seg(q, n@pre, 100000)
   */
  for (int i = 0; i < n; ++i) {
    /*@ Inv Assert
      exists out_l q_l,
      nums == nums@pre && n == n@pre && k == k@pre &&
      out == out@pre &&
      1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      Zlength(q_l) == n@pre &&
      0 <= i && i < n@pre &&
      0 <= head && head <= tail && tail <= i &&
      0 <= out_idx && out_idx <= n@pre - k@pre + 1 &&
	      (i < k@pre => out_idx == 0) &&
	      (k@pre <= i => out_idx == i - k@pre + 1) &&
	      Forall(Z::le(-10000), l) && Forall(Z::ge(10000), l) &&
	      Zlength(out_l) == out_idx &&
	      SWMOutputPrefix(l, k@pre, out_idx, out_l) &&
	      SWMQueueDropLoopState(l, q_l, head, tail, i, k@pre) &&
	      Forall(Z::le(0), sublist(head, tail, q_l)) && Forall(Z::gt(n@pre), sublist(head, tail, q_l)) &&
      IntArray::full(nums@pre, n@pre, l) *
      IntArray::seg(out@pre, 0, out_idx, out_l) *
      IntArray::undef_seg(out@pre, out_idx, n@pre - k@pre + 1) *
      IntArray::full(q, n@pre, q_l) *
      IntArray::undef_seg(q, n@pre, 100000)
    */
    while (head < tail && q[head] <= i - k) {
      head++;
    }

    
    /*@ Inv Assert
      exists out_l q_l,
      nums == nums@pre && n == n@pre && k == k@pre &&
      out == out@pre &&
      1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      Zlength(q_l) == n@pre &&
      0 <= i && i < n@pre &&
      0 <= head && head <= tail && tail <= i &&
      0 <= out_idx && out_idx <= n@pre - k@pre + 1 &&
	      (i < k@pre => out_idx == 0) &&
	      (k@pre <= i => out_idx == i - k@pre + 1) &&
	      Forall(Z::le(-10000), l) && Forall(Z::ge(10000), l) &&
	      Zlength(out_l) == out_idx &&
	      SWMOutputPrefix(l, k@pre, out_idx, out_l) &&
	      SWMQueuePendingState(l, q_l, head, tail, i, k@pre) &&
	      Forall(Z::le(0), sublist(head, tail, q_l)) && Forall(Z::gt(n@pre), sublist(head, tail, q_l)) &&
	      (head < tail => (0 <= tail - 1 && tail - 1 < n@pre && 0 <= q_l[tail - 1] && q_l[tail - 1] < n@pre)) &&
      IntArray::full(nums@pre, n@pre, l) *
      IntArray::seg(out@pre, 0, out_idx, out_l) *
      IntArray::undef_seg(out@pre, out_idx, n@pre - k@pre + 1) *
      IntArray::full(q, n@pre, q_l) *
      IntArray::undef_seg(q, n@pre, 100000)
    */
    while (head < tail && nums[q[tail - 1]] <= nums[i]) {
      tail--;
    }


    q[tail] = i;
    tail++;

    /*@ Assert
      exists out_l q_l,
      nums == nums@pre && n == n@pre && k == k@pre &&
      out == out@pre &&
      1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      Zlength(q_l) == n@pre &&
      0 <= i && i < n@pre &&
      0 <= head && head < tail && tail <= i + 1 &&
      0 <= out_idx && out_idx <= n@pre - k@pre + 1 &&
	      (i < k@pre => out_idx == 0) &&
	      (k@pre <= i => out_idx == i - k@pre + 1) &&
	      Forall(Z::le(-10000), l) && Forall(Z::ge(10000), l) &&
	      Zlength(out_l) == out_idx &&
	      SWMOutputPrefix(l, k@pre, out_idx, out_l) &&
	      SWMQueueState(l, q_l, head, tail, i + 1, k@pre) &&
	      Forall(Z::le(0), sublist(head, tail, q_l)) && Forall(Z::gt(n@pre), sublist(head, tail, q_l)) &&
	      IntArray::full(nums@pre, n@pre, l) *
      IntArray::seg(out@pre, 0, out_idx, out_l) *
      IntArray::undef_seg(out@pre, out_idx, n@pre - k@pre + 1) *
      IntArray::full(q, n@pre, q_l) *
      IntArray::undef_seg(q, n@pre, 100000)
    */
    if (i >= k - 1) {
      /*@ Assert
        exists out_l q_l,
        nums == nums@pre && n == n@pre && k == k@pre &&
        out == out@pre &&
        1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
        Zlength(l) == n@pre &&
        Zlength(q_l) == n@pre &&
        0 <= i && i < n@pre &&
        0 <= head && head < tail && tail <= i + 1 &&
        head < n@pre &&
        0 <= q_l[head] && q_l[head] < n@pre &&
	        out_idx == i - k@pre + 1 &&
	        0 <= out_idx && out_idx < n@pre - k@pre + 1 &&
	        Forall(Z::le(-10000), l) && Forall(Z::ge(10000), l) &&
	        Zlength(out_l) == out_idx &&
	        SWMOutputPrefix(l, k@pre, out_idx, out_l) &&
	        SWMQueueState(l, q_l, head, tail, i + 1, k@pre) &&
	        Forall(Z::le(0), sublist(head, tail, q_l)) && Forall(Z::gt(n@pre), sublist(head, tail, q_l)) &&
	        WindowMaxValue(l, i - k@pre + 1, i + 1, l[q_l[head]]) &&
        IntArray::full(nums@pre, n@pre, l) *
        IntArray::seg(out@pre, 0, out_idx, out_l) *
        IntArray::undef_seg(out@pre, out_idx, n@pre - k@pre + 1) *
        IntArray::full(q, n@pre, q_l) *
      IntArray::undef_seg(q, n@pre, 100000)
      */
      out[out_idx] = nums[q[head]];

      out_idx++;
    }
    /*@ Assert
      exists out_l q_l,
      nums == nums@pre && n == n@pre && k == k@pre &&
      out == out@pre &&
      1 <= k@pre && k@pre <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      Zlength(q_l) == n@pre &&
      0 <= i && i < n@pre &&
      0 <= head && head <= tail && tail <= i + 1 &&
      0 <= out_idx && out_idx <= n@pre - k@pre + 1 &&
      (i + 1 < k@pre => out_idx == 0) &&
      (k@pre <= i + 1 => out_idx == i + 1 - k@pre + 1) &&
	      (k@pre <= i + 1 => head < tail) &&
	      Forall(Z::le(-10000), l) && Forall(Z::ge(10000), l) &&
	      Zlength(out_l) == out_idx &&
	      SWMOutputPrefix(l, k@pre, out_idx, out_l) &&
	      SWMQueueState(l, q_l, head, tail, i + 1, k@pre) &&
	      Forall(Z::le(0), sublist(head, tail, q_l)) && Forall(Z::gt(n@pre), sublist(head, tail, q_l)) &&
	      IntArray::full(nums@pre, n@pre, l) *
      IntArray::seg(out@pre, 0, out_idx, out_l) *
      IntArray::undef_seg(out@pre, out_idx, n@pre - k@pre + 1) *
      IntArray::full(q, n@pre, q_l) *
      IntArray::undef_seg(q, n@pre, 100000)
    */
  }
  
  /*@ Assert
      exists out_l,
      nums == nums@pre && n == n@pre && k == k@pre && out == out@pre &&
      0 <= head && 0 <= tail && 0 <= out_idx &&
      SlidingWindowMaximum(l, k, out_l) &&
      IntArray::full(nums, n, l) * IntArray::full(out, n - k + 1, out_l) *
      IntArray::undef_full(q, 100000)
   */
}
