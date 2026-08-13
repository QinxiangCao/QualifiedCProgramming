



/*@ Extern Coq (multiset :: * => *) */
/*@ Extern Coq
      (heap_capacity : Z)
      (mlist : {A} -> multiset A -> list A)
      (list_to_multiset : {A} -> list A -> multiset A)
      (multiset_size : {A} -> multiset A -> Z)
      (multiset_equiv : {A} -> multiset A -> multiset A -> Prop)
      (multiset_insert : {A} -> multiset A -> A -> multiset A)
      (multiset_remove :
        {A} -> multiset A -> A -> multiset A)
      (multiset_max : multiset Z -> Z)
      (multiset_maximum : multiset Z -> Z -> Prop)
      (store_heap : Z -> multiset Z -> Z -> Assertion)
      (heap_retired_cell : Z -> Z -> Z -> Assertion)
      (heap_representation :
        multiset Z -> list Z -> Z -> Prop)
      (PrefixMaximum : list Z -> Z -> Z -> Prop)
      (PushSource : list Z -> multiset Z -> Z -> Z -> Prop)
      (PushLoopState : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (PushResult : multiset Z -> list Z -> Z -> Z -> Prop)
      (BuildPrefixState : multiset Z -> list Z -> Z -> Prop)
      (heap_parent : Z -> Z)
      (PopLoopState : list Z -> list Z -> Z -> Z -> Prop)
      (PopSelectedChild : list Z -> Z -> Z -> Z -> Prop)
      (PopReadyState : list Z -> list Z -> Z -> Z -> Prop)
      (PopResult :
        multiset Z -> list Z -> list Z -> Z -> Z -> Prop)
      (HeapSortState :
        list Z -> multiset Z -> list Z -> Prop)
      (Permutation : list Z -> list Z -> Prop)
      (increasing : list Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib */

void push(int *heap, int n, int x)
/*@ With (S_before : multiset Z)
    Require
      n < heap_capacity &&
      store_heap(heap, S_before, n) *
      IntArray::undef_seg(heap, n, n + 1)
    Ensure
      store_heap(
        heap, multiset_insert(S_before, x), n + 1
      )
 */
{
  /*@ Assert
      exists base,
        heap == heap@pre && n == n@pre && x == x@pre &&
        0 <= n@pre && n@pre < heap_capacity &&
        heap_representation(S_before, base, n@pre) &&
        IntArray::full(heap, n@pre, base) *
        IntArray::undef_seg(heap, n@pre, n@pre + 1)
   */
  heap[n] = x;
  /*@ Assert
      exists written,
        heap == heap@pre && n == n@pre && x == x@pre &&
        0 <= n@pre && n@pre < heap_capacity &&
        PushSource(written, S_before, n@pre, x@pre) &&
        PushLoopState(written, written, n@pre, n@pre, x@pre) &&
        IntArray::full(heap, n@pre + 1, written)
   */
  int child = n;
  /*@ Inv Assert
      exists written current,
        heap == heap@pre && n == n@pre && x == x@pre &&
        0 <= n@pre && n@pre < heap_capacity &&
        0 <= child && child <= n@pre &&
        PushSource(written, S_before, n@pre, x@pre) &&
        PushLoopState(written, current, n@pre, child, x@pre) &&
        IntArray::full(heap, n@pre + 1, current)
   */
  while (child > 0) {
    int parent = (child - 1) / 2;
    /*@ Assert
        exists written current,
          heap == heap@pre && n == n@pre && x == x@pre &&
          0 <= n@pre && n@pre < heap_capacity &&
          0 < child && child <= n@pre &&
          0 <= parent && parent < child && parent <= n@pre &&
          parent == heap_parent(child) &&
          PushSource(written, S_before, n@pre, x@pre) &&
          PushLoopState(written, current, n@pre, child, x@pre) &&
          IntArray::full(heap, n@pre + 1, current)
     */
    if (heap[parent] >= heap[child]) {
      /*@ Assert
          exists written current,
            heap == heap@pre && n == n@pre && x == x@pre &&
            0 <= n@pre && n@pre < heap_capacity &&
            0 < child && child <= n@pre &&
            0 <= parent && parent < child && parent <= n@pre &&
            parent == heap_parent(child) &&
            current[parent] >= current[child] &&
            PushSource(written, S_before, n@pre, x@pre) &&
            PushResult(S_before, current, n@pre, x@pre) &&
            IntArray::full(heap, n@pre + 1, current)
       */
      break;
    }
    int tmp = heap[parent];
    heap[parent] = heap[child];
    heap[child] = tmp;
    /*@ Assert
        exists written current,
          heap == heap@pre && n == n@pre && x == x@pre &&
          0 <= n@pre && n@pre < heap_capacity &&
          0 < child && child <= n@pre &&
          0 <= parent && parent < child && parent <= n@pre &&
          parent == heap_parent(child) &&
          tmp == current[child] &&
          PushSource(written, S_before, n@pre, x@pre) &&
          PushLoopState(written, current, n@pre, parent, x@pre) &&
          IntArray::full(heap, n@pre + 1, current)
     */
    child = parent;
  }
  /*@ Assert
      exists written result,
        heap == heap@pre && n == n@pre && x == x@pre &&
        0 <= n@pre && n@pre < heap_capacity &&
        0 <= child && child <= n@pre &&
        PushSource(written, S_before, n@pre, x@pre) &&
        PushResult(S_before, result, n@pre, x@pre) &&
        IntArray::full(heap, n@pre + 1, result)
   */
  /*@ Assert
      heap == heap@pre && n == n@pre && x == x@pre &&
      0 <= child && child <= n@pre &&
      store_heap(
        heap, multiset_insert(S_before, x@pre), n@pre + 1
      )
   */
}

void build(int *heap, int n)
/*@ With (input : list Z)
    Require
      0 <= n &&
      n <= heap_capacity &&
      Zlength(input) == n &&
      IntArray::full(heap, n, input)
    Ensure
      store_heap(heap, list_to_multiset(input), n)
 */
{
  /*@ Inv Assert
      (heap == heap@pre && n == n@pre &&
       n@pre == 0 && i == 1 &&
       Zlength(input) == n@pre &&
       IntArray::full(heap, n@pre, input))
      ||
      (exists S_prefix,
        heap == heap@pre && n == n@pre &&
        1 <= n@pre && n@pre <= heap_capacity &&
        1 <= i && i <= n@pre &&
        Zlength(input) == n@pre &&
        BuildPrefixState(S_prefix, input, i) &&
        store_heap(heap, S_prefix, i) *
        IntArray::seg(heap, i, n@pre, sublist(i, n@pre, input)))
   */
  for (int i = 1; i < n; ++i) {
    int x = heap[i];
    /*@ Assert
        exists S_prefix,
          heap == heap@pre && n == n@pre &&
          1 <= n@pre && n@pre <= heap_capacity &&
          1 <= i && i < n@pre &&
          x == input[i] &&
          Zlength(input) == n@pre &&
          BuildPrefixState(S_prefix, input, i) &&
          store_heap(heap, S_prefix, i) *
          IntArray::undef_seg(heap, i, i + 1) *
          IntArray::seg(heap, i + 1, n@pre,
                        sublist(i + 1, n@pre, input))
     */
    push(heap, i, x);
    /*@ Assert
        exists S_prefix,
          heap == heap@pre && n == n@pre &&
          1 <= n@pre && n@pre <= heap_capacity &&
          1 <= i && i < n@pre &&
          x == input[i] &&
          Zlength(input) == n@pre &&
          BuildPrefixState(S_prefix, input, i) &&
          store_heap(
            heap, multiset_insert(S_prefix, x), i + 1
          ) *
          IntArray::seg(heap, i + 1, n@pre,
                        sublist(i + 1, n@pre, input))
     */
    /*@ Assert
        exists S_prefix,
          heap == heap@pre && n == n@pre &&
          1 <= n@pre && n@pre <= heap_capacity &&
          1 <= i && i < n@pre &&
          x == input[i] &&
          Zlength(input) == n@pre &&
          BuildPrefixState(
            multiset_insert(S_prefix, x), input, i + 1
          ) &&
          store_heap(
            heap, multiset_insert(S_prefix, x), i + 1
          ) *
          IntArray::seg(heap, i + 1, n@pre,
                        sublist(i + 1, n@pre, input))
     */
  }
  /*@ Assert
      heap == heap@pre && n == n@pre &&
      store_heap(heap, list_to_multiset(input), n@pre)
   */
}

int pop(int *heap, int n)
/*@ With (S_before : multiset Z)
    Require
      1 <= n &&
      store_heap(heap, S_before, n)
    Ensure
      __return == multiset_max(S_before) &&
      multiset_maximum(S_before, __return) &&
      store_heap(
        heap,
        multiset_remove(S_before, multiset_max(S_before)),
        n - 1
      ) *
      IntArray::undef_seg(heap, n - 1, n)
 */
{
  /*@ Assert
      exists before,
        heap == heap@pre && n == n@pre &&
        1 <= n@pre && n@pre <= heap_capacity &&
        heap_representation(S_before, before, n@pre) &&
        PrefixMaximum(before, n@pre, before[0]) &&
        before[0] == multiset_max(S_before) &&
        multiset_maximum(S_before, before[0]) &&
        IntArray::full(heap, n@pre, before)
   */
  int ret = heap[0];
  /*@ Assert
      exists before,
        heap == heap@pre && n == n@pre &&
        1 <= n@pre && n@pre <= heap_capacity &&
        ret == before[0] &&
        ret == multiset_max(S_before) &&
        heap_representation(S_before, before, n@pre) &&
        PrefixMaximum(before, n@pre, ret) &&
        multiset_maximum(S_before, ret) &&
        IntArray::full(heap, n@pre, before)
   */
  if (n == 1) {
    /*@ Assert
        heap == heap@pre && n == n@pre &&
        n@pre == 1 &&
        ret == multiset_max(S_before) &&
        multiset_maximum(S_before, ret) &&
        store_heap(
          heap,
          multiset_remove(S_before, multiset_max(S_before)),
          0
        ) *
        IntArray::undef_seg(heap, 0, 1)
     */
    return ret;
  }

  heap[0] = heap[n - 1];
  /*@ Assert
      exists before current,
        heap == heap@pre && n == n@pre &&
        1 < n@pre && n@pre <= heap_capacity &&
        ret == before[0] &&
        ret == multiset_max(S_before) &&
        heap_representation(S_before, before, n@pre) &&
        PrefixMaximum(before, n@pre, ret) &&
        multiset_maximum(S_before, ret) &&
        PopLoopState(before, current, n@pre, 0) &&
        IntArray::full(heap, n@pre, current)
   */
  int idx = 0;
  /*@ Inv Assert
      exists before current,
        heap == heap@pre && n == n@pre &&
        1 < n@pre && n@pre <= heap_capacity &&
        ret == before[0] &&
        ret == multiset_max(S_before) &&
        heap_representation(S_before, before, n@pre) &&
        PrefixMaximum(before, n@pre, ret) &&
        multiset_maximum(S_before, ret) &&
        0 <= idx && idx < n@pre - 1 &&
        0 <= idx * 2 + 1 && idx * 2 + 1 <= INT_MAX &&
        PopLoopState(before, current, n@pre, idx) &&
        IntArray::full(heap, n@pre, current)
   */
  while (idx * 2 + 1 < n - 1) {
    int left = idx * 2 + 1;
    int right = left + 1;
    int largest = left;
    /*@ Assert
        exists before current,
          heap == heap@pre && n == n@pre &&
          1 < n@pre && n@pre <= heap_capacity &&
          ret == before[0] &&
          ret == multiset_max(S_before) &&
          heap_representation(S_before, before, n@pre) &&
          PrefixMaximum(before, n@pre, ret) &&
          multiset_maximum(S_before, ret) &&
          0 <= idx && idx < n@pre - 1 &&
          left == idx * 2 + 1 &&
          right == left + 1 &&
          largest == left &&
          0 <= left && left < n@pre - 1 &&
          0 <= right && right <= n@pre - 1 &&
          PopLoopState(before, current, n@pre, idx) &&
          IntArray::full(heap, n@pre, current)
     */
    if (right < n - 1 && heap[left] < heap[right]) {
      largest = right;
    }
    /*@ Assert
        exists before current,
          heap == heap@pre && n == n@pre &&
          1 < n@pre && n@pre <= heap_capacity &&
          ret == before[0] &&
          ret == multiset_max(S_before) &&
          heap_representation(S_before, before, n@pre) &&
          PrefixMaximum(before, n@pre, ret) &&
          multiset_maximum(S_before, ret) &&
          0 <= idx && idx < n@pre - 1 &&
          left == idx * 2 + 1 &&
          right == left + 1 &&
          0 <= largest && largest < n@pre - 1 &&
          PopSelectedChild(current, n@pre - 1, idx, largest) &&
          PopLoopState(before, current, n@pre, idx) &&
          IntArray::full(heap, n@pre, current)
     */
    if (heap[idx] >= heap[largest]) {
      /*@ Assert
          exists before current,
            heap == heap@pre && n == n@pre &&
            1 < n@pre && n@pre <= heap_capacity &&
            ret == before[0] &&
            ret == multiset_max(S_before) &&
            heap_representation(S_before, before, n@pre) &&
            PrefixMaximum(before, n@pre, ret) &&
            multiset_maximum(S_before, ret) &&
            0 <= idx && idx < n@pre - 1 &&
            left == idx * 2 + 1 &&
            right == left + 1 &&
            0 <= left && left < n@pre - 1 &&
            0 <= right && right <= n@pre - 1 &&
            0 <= largest && largest < n@pre - 1 &&
            current[idx] >= current[largest] &&
            PopSelectedChild(current, n@pre - 1, idx, largest) &&
            PopReadyState(before, current, n@pre, ret) &&
            IntArray::full(heap, n@pre, current)
       */
      break;
    }
    int tmp = heap[idx];
    heap[idx] = heap[largest];
    heap[largest] = tmp;
    /*@ Assert
        exists before current,
          heap == heap@pre && n == n@pre &&
          1 < n@pre && n@pre <= heap_capacity &&
          ret == before[0] &&
          ret == multiset_max(S_before) &&
          heap_representation(S_before, before, n@pre) &&
          PrefixMaximum(before, n@pre, ret) &&
          multiset_maximum(S_before, ret) &&
          0 <= idx && idx < n@pre - 1 &&
          left == idx * 2 + 1 &&
          right == left + 1 &&
          0 <= left && left < n@pre - 1 &&
          0 <= right && right <= n@pre - 1 &&
          0 <= largest && largest < n@pre - 1 &&
          idx < largest &&
          tmp == current[largest] &&
          PopLoopState(before, current, n@pre, largest) &&
          IntArray::full(heap, n@pre, current)
     */
    idx = largest;
  }
  /*@ Assert
      exists before current,
        heap == heap@pre && n == n@pre &&
        1 < n@pre && n@pre <= heap_capacity &&
        ret == before[0] &&
        ret == multiset_max(S_before) &&
        heap_representation(S_before, before, n@pre) &&
        PrefixMaximum(before, n@pre, ret) &&
        multiset_maximum(S_before, ret) &&
        0 <= idx && idx < n@pre - 1 &&
        PopReadyState(before, current, n@pre, ret) &&
        IntArray::full(heap, n@pre, current)
   */
  /*@ Assert
      exists before result,
        heap == heap@pre && n == n@pre &&
        1 < n@pre && n@pre <= heap_capacity &&
        0 <= idx && idx < n@pre - 1 &&
        ret == before[0] &&
        ret == multiset_max(S_before) &&
        heap_representation(S_before, before, n@pre) &&
        PrefixMaximum(before, n@pre, ret) &&
        multiset_maximum(S_before, ret) &&
        PopResult(S_before, before, result, n@pre, ret) &&
        IntArray::full(heap, n@pre, result)
   */
  /*@ Assert
      heap == heap@pre && n == n@pre &&
      0 <= idx && idx < n@pre - 1 &&
      ret == multiset_max(S_before) &&
      multiset_maximum(S_before, ret) &&
      store_heap(
        heap,
        multiset_remove(S_before, multiset_max(S_before)),
        n@pre - 1
      ) *
      IntArray::undef_seg(heap, n@pre - 1, n@pre)
   */
  return ret;
}

void heap_sort(int *heap, int n)
/*@ With (input : list Z)
    Require
      0 <= n &&
      n <= heap_capacity &&
      Zlength(input) == n &&
      IntArray::full(heap, n, input)
    Ensure
      exists output,
        Zlength(output) == n &&
        Permutation(input, output) &&
        increasing(output) &&
        IntArray::full(heap, n, output)
 */
{
  build(heap, n) /*@ where input = input */;
  /*@ Assert
      heap == heap@pre && n == n@pre &&
      0 <= n@pre && n@pre <= heap_capacity &&
      Zlength(input) == n@pre &&
      multiset_size(list_to_multiset(input)) == n@pre &&
      HeapSortState(
        input, list_to_multiset(input), nil
      ) &&
      store_heap(
        heap, list_to_multiset(input), n@pre
      ) *
      IntArray::seg(heap, n@pre, n@pre, nil)
   */
  int i = n;
  /*@ Inv Assert
      exists active suffix,
        heap == heap@pre && n == n@pre &&
        0 <= n@pre && n@pre <= heap_capacity &&
        Zlength(input) == n@pre &&
        0 <= i && i <= n@pre &&
        multiset_size(active) == i &&
        Zlength(suffix) == n@pre - i &&
        HeapSortState(input, active, suffix) &&
        store_heap(heap, active, i) *
        IntArray::seg(heap, i, n@pre, suffix)
   */
  while (i > 0) {
    /*@ Assert
        exists active suffix,
          heap == heap@pre && n == n@pre &&
          0 <= n@pre && n@pre <= heap_capacity &&
          Zlength(input) == n@pre &&
          1 <= i && i <= n@pre &&
          multiset_size(active) == i &&
          Zlength(suffix) == n@pre - i &&
          HeapSortState(input, active, suffix) &&
          store_heap(heap, active, i) *
          IntArray::seg(heap, i, n@pre, suffix)
     */
    int extracted = pop(heap, i);
    /*@ Assert
        exists active suffix,
          heap == heap@pre && n == n@pre &&
          0 <= n@pre && n@pre <= heap_capacity &&
          Zlength(input) == n@pre &&
          1 <= i && i <= n@pre &&
          extracted == multiset_max(active) &&
          multiset_maximum(active, extracted) &&
          multiset_size(active) == i &&
          Zlength(suffix) == n@pre - i &&
          HeapSortState(input, active, suffix) &&
          store_heap(
            heap,
            multiset_remove(active, multiset_max(active)),
            i - 1
          ) *
          IntArray::undef_seg(heap, i - 1, i) *
          IntArray::seg(heap, i, n@pre, suffix)
     */
    heap[i - 1] = extracted;
    /*@ Assert
        exists active suffix,
          heap == heap@pre && n == n@pre &&
          0 <= n@pre && n@pre <= heap_capacity &&
          Zlength(input) == n@pre &&
          1 <= i && i <= n@pre &&
          extracted == multiset_max(active) &&
          multiset_maximum(active, extracted) &&
          multiset_size(active) == i &&
          Zlength(suffix) == n@pre - i &&
          HeapSortState(input, active, suffix) &&
          store_heap(
            heap,
            multiset_remove(active, multiset_max(active)),
            i - 1
          ) *
          heap_retired_cell(heap, i - 1, extracted) *
          IntArray::seg(heap, i, n@pre, suffix)
     */
    --i;
    /*@ Assert
        exists active suffix,
          heap == heap@pre && n == n@pre &&
          0 <= n@pre && n@pre <= heap_capacity &&
          Zlength(input) == n@pre &&
          0 <= i && i < n@pre &&
          multiset_size(
            multiset_remove(active, multiset_max(active))
          ) == i &&
          Zlength(cons(extracted, suffix)) == n@pre - i &&
          HeapSortState(
            input,
            multiset_remove(active, multiset_max(active)),
            cons(extracted, suffix)
          ) &&
          store_heap(
            heap,
            multiset_remove(active, multiset_max(active)),
            i
          ) *
          IntArray::seg(
            heap, i, n@pre, cons(extracted, suffix)
          )
     */
  }
  /*@ Assert
      exists output,
        heap == heap@pre && n == n@pre &&
        0 <= n@pre && n@pre <= heap_capacity &&
        i == 0 &&
        Zlength(input) == n@pre &&
        Zlength(output) == n@pre &&
        Permutation(input, output) &&
        increasing(output) &&
        IntArray::full(heap, n@pre, output)
   */
}
