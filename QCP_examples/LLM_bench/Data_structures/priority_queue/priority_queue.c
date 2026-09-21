/*@ Extern Coq (multiset :: * => *) */
/*@ Extern Coq
      (heap_capacity : Z)
      (list_to_multiset : {A} -> list A -> multiset A)
      (multiset_size : {A} -> multiset A -> Z)
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
      (BuildPrefixState : multiset Z -> list Z -> Z -> Prop)
      (heap_parent : Z -> Z)
      (PopLoopState : list Z -> list Z -> Z -> Z -> Prop)
      (PopSelectedChild : list Z -> Z -> Z -> Z -> Prop)
      (HeapSortState :
        list Z -> multiset Z -> list Z -> Prop)
      (Permutation : list Z -> list Z -> Prop)
      (increasing : list Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib */

void push(int *heap, int n, int x)
/*@ With (S_before : multiset Z)
    Require
      0 <= n && n < heap_capacity &&
      store_heap(heap, S_before, n) *
      IntArray::undef_seg(heap, n, n + 1)
    Ensure
      store_heap(
        heap, multiset_insert(S_before, x), n + 1
      )
 */
{
  heap[n] = x;

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

      break;
    }
    int tmp = heap[parent];
    heap[parent] = heap[child];
    heap[child] = tmp;

    child = parent;
  }

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

  }

}

int pop(int *heap, int n)
/*@ With (S_before : multiset Z)
    Require
      1 <= n && n <= heap_capacity &&
      store_heap(heap, S_before, n)
    Ensure
      multiset_maximum(S_before, __return) &&
      store_heap(
        heap,
        multiset_remove(S_before, __return),
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

  if (n == 1) {

    return ret;
  }

  heap[0] = heap[n - 1];

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

      break;
    }
    int tmp = heap[idx];
    heap[idx] = heap[largest];
    heap[largest] = tmp;

    idx = largest;
  }

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
        Permutation(input, output) &&
        increasing(output) &&
        IntArray::full(heap, n, output)
 */
{
  build(heap, n);

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

    int extracted = pop(heap, i);

    heap[i - 1] = extracted;
    --i;

  }

}
