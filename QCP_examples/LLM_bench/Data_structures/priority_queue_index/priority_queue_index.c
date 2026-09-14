#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (multiset :: * => *) */
/*@ Extern Coq
      (heap_capacity : Z)
      (heap_item : Z -> Z -> Z * Z)
      (item_key : Z * Z -> Z)
      (item_data : Z * Z -> Z)
      (pair_list : list Z -> list Z -> list (Z * Z))
      (list_to_multiset : {A} -> list A -> multiset A)
      (multiset_size : {A} -> multiset A -> Z)
      (multiset_equiv : {A} -> multiset A -> multiset A -> Prop)
      (multiset_insert :
        {A} -> multiset A -> A -> multiset A)
      (multiset_remove :
        {A} -> multiset A -> A -> multiset A)
      (multiset_min : multiset (Z * Z) -> Z * Z)
      (multiset_minimum :
        multiset (Z * Z) -> Z * Z -> Prop)
      (store_heap :
        Z -> Z -> multiset (Z * Z) -> Z -> Assertion)
      (heap_representation :
        multiset (Z * Z) -> list Z -> list Z -> Z -> Prop)
      (heap_parent : Z -> Z)
      (KeyWriteState :
        multiset (Z * Z) -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (PushSource :
        list Z -> list Z -> multiset (Z * Z) -> Z -> Z -> Z -> Prop)
      (PushLoopState :
        list Z -> list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (PushResult :
        multiset (Z * Z) -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (BuildPrefixState :
        multiset (Z * Z) -> list Z -> list Z -> Z -> Prop)
      (PrefixMinimum :
        list Z -> list Z -> Z -> Z * Z -> Prop)
      (PopLoopState :
        list Z -> list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (PopSelectedChild : list Z -> Z -> Z -> Z -> Prop)
      (PopReadyState :
        list Z -> list Z -> list Z -> list Z -> Z -> Z * Z -> Prop)
      (PopResult :
        multiset (Z * Z) ->
        list Z -> list Z -> list Z -> list Z -> Z -> Z * Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib */

void push(int *key, int *data, int n, int data_x, int key_x)
/*@ With (S_before : multiset (Z * Z))
    Require
      0 <= n &&
      n < heap_capacity &&
      store_heap(key, data, S_before, n)
    Ensure
      store_heap(
        key, data,
        multiset_insert(S_before, heap_item(key_x, data_x)),
        n + 1
      )
 */
{
  /*@ Assert
      exists key_base data_base,
        key == key@pre && data == data@pre &&
        n == n@pre && data_x == data_x@pre && key_x == key_x@pre &&
        0 <= n@pre && n@pre < heap_capacity &&
        heap_representation(S_before, key_base, data_base, n@pre) &&
        IntArray::full(key, n@pre, key_base) *
        IntArray::undef_seg(key, n@pre, n@pre + 1) *
        IntArray::undef_seg(key, n@pre + 1, heap_capacity) *
        IntArray::full(data, n@pre, data_base) *
        IntArray::undef_seg(data, n@pre, n@pre + 1) *
        IntArray::undef_seg(data, n@pre + 1, heap_capacity)
   */
  key[n] = key_x;
  /*@ Assert
      exists key_base data_base key_written,
        key == key@pre && data == data@pre &&
        n == n@pre && data_x == data_x@pre && key_x == key_x@pre &&
        0 <= n@pre && n@pre < heap_capacity &&
        KeyWriteState(S_before, key_base, data_base,
          key_written, n@pre, key_x@pre) &&
        IntArray::full(key, n@pre + 1, key_written) *
        IntArray::undef_seg(key, n@pre + 1, heap_capacity) *
        IntArray::full(data, n@pre, data_base) *
        IntArray::undef_seg(data, n@pre, n@pre + 1) *
        IntArray::undef_seg(data, n@pre + 1, heap_capacity)
   */
  data[n] = data_x;
  /*@ Assert
      exists key_written data_written,
        key == key@pre && data == data@pre &&
        n == n@pre && data_x == data_x@pre && key_x == key_x@pre &&
        0 <= n@pre && n@pre < heap_capacity &&
        PushSource(key_written, data_written,
          S_before, n@pre, data_x@pre, key_x@pre) &&
        PushLoopState(key_written, data_written,
          key_written, data_written, n@pre, n@pre, data_x@pre, key_x@pre) &&
        IntArray::full(key, n@pre + 1, key_written) *
        IntArray::undef_seg(key, n@pre + 1, heap_capacity) *
        IntArray::full(data, n@pre + 1, data_written) *
        IntArray::undef_seg(data, n@pre + 1, heap_capacity)
   */
  int child = n;
  /*@ Inv Assert
      exists key_written data_written key_current data_current,
        key == key@pre && data == data@pre &&
        n == n@pre && data_x == data_x@pre && key_x == key_x@pre &&
        0 <= n@pre && n@pre < heap_capacity &&
        0 <= child && child <= n@pre &&
        PushSource(key_written, data_written,
          S_before, n@pre, data_x@pre, key_x@pre) &&
        PushLoopState(key_written, data_written,
          key_current, data_current, n@pre, child,
          data_x@pre, key_x@pre) &&
        IntArray::full(key, n@pre + 1, key_current) *
        IntArray::undef_seg(key, n@pre + 1, heap_capacity) *
        IntArray::full(data, n@pre + 1, data_current) *
        IntArray::undef_seg(data, n@pre + 1, heap_capacity)
   */
  while (child > 0) {
    int parent = (child - 1) / 2;
    /*@ Assert
        exists key_written data_written key_current data_current,
          key == key@pre && data == data@pre &&
          n == n@pre && data_x == data_x@pre && key_x == key_x@pre &&
          0 <= n@pre && n@pre < heap_capacity &&
          0 < child && child <= n@pre &&
          0 <= parent && parent < child && parent <= n@pre &&
          parent == heap_parent(child) &&
          PushSource(key_written, data_written,
            S_before, n@pre, data_x@pre, key_x@pre) &&
          PushLoopState(key_written, data_written,
            key_current, data_current, n@pre, child,
            data_x@pre, key_x@pre) &&
          IntArray::full(key, n@pre + 1, key_current) *
          IntArray::undef_seg(key, n@pre + 1, heap_capacity) *
          IntArray::full(data, n@pre + 1, data_current) *
          IntArray::undef_seg(data, n@pre + 1, heap_capacity)
     */
    if (key[parent] <= key[child]) {
      /*@ Assert
          exists key_written data_written key_current data_current,
            key == key@pre && data == data@pre &&
            n == n@pre && data_x == data_x@pre && key_x == key_x@pre &&
            0 <= n@pre && n@pre < heap_capacity &&
            0 < child && child <= n@pre &&
            0 <= parent && parent < child && parent <= n@pre &&
            parent == heap_parent(child) &&
            key_current[parent] <= key_current[child] &&
            PushSource(key_written, data_written,
              S_before, n@pre, data_x@pre, key_x@pre) &&
            PushResult(S_before, key_current, data_current,
              n@pre, data_x@pre, key_x@pre) &&
            IntArray::full(key, n@pre + 1, key_current) *
            IntArray::undef_seg(key, n@pre + 1, heap_capacity) *
            IntArray::full(data, n@pre + 1, data_current) *
            IntArray::undef_seg(data, n@pre + 1, heap_capacity)
       */
      break;
    }
    int tmp_key = key[parent];
    key[parent] = key[child];
    key[child] = tmp_key;

    int tmp_data = data[parent];
    data[parent] = data[child];
    data[child] = tmp_data;
    /*@ Assert
        exists key_written data_written key_current data_current,
          key == key@pre && data == data@pre &&
          n == n@pre && data_x == data_x@pre && key_x == key_x@pre &&
          0 <= n@pre && n@pre < heap_capacity &&
          0 < child && child <= n@pre &&
          0 <= parent && parent < child && parent <= n@pre &&
          parent == heap_parent(child) &&
          tmp_key == key_current[child] &&
          tmp_data == data_current[child] &&
          PushSource(key_written, data_written,
            S_before, n@pre, data_x@pre, key_x@pre) &&
          PushLoopState(key_written, data_written,
            key_current, data_current, n@pre, parent,
            data_x@pre, key_x@pre) &&
          IntArray::full(key, n@pre + 1, key_current) *
          IntArray::undef_seg(key, n@pre + 1, heap_capacity) *
          IntArray::full(data, n@pre + 1, data_current) *
          IntArray::undef_seg(data, n@pre + 1, heap_capacity)
     */
    child = parent;
  }
  /*@ Assert
      exists key_written data_written key_result data_result,
        key == key@pre && data == data@pre &&
        n == n@pre && data_x == data_x@pre && key_x == key_x@pre &&
        0 <= n@pre && n@pre < heap_capacity &&
        0 <= child && child <= n@pre &&
        PushSource(key_written, data_written,
          S_before, n@pre, data_x@pre, key_x@pre) &&
        PushResult(S_before, key_result, data_result,
          n@pre, data_x@pre, key_x@pre) &&
        IntArray::full(key, n@pre + 1, key_result) *
        IntArray::undef_seg(key, n@pre + 1, heap_capacity) *
        IntArray::full(data, n@pre + 1, data_result) *
        IntArray::undef_seg(data, n@pre + 1, heap_capacity)
   */
  /*@ Assert
      key == key@pre && data == data@pre &&
      n == n@pre && data_x == data_x@pre && key_x == key_x@pre &&
      0 <= child && child <= n@pre &&
      store_heap(
        key, data,
        multiset_insert(S_before, heap_item(key_x@pre, data_x@pre)),
        n@pre + 1
      )
   */
}

void build(int *key, int *data, int n)
/*@ With (key_input data_input : list Z)
    Require
      0 <= n &&
      n <= heap_capacity &&
      Zlength(key_input) == n &&
      Zlength(data_input) == n &&
      IntArray::full(key, n, key_input) *
      IntArray::undef_seg(key, n, heap_capacity) *
      IntArray::full(data, n, data_input) *
      IntArray::undef_seg(data, n, heap_capacity)
    Ensure
      store_heap(
        key, data,
        list_to_multiset(pair_list(key_input, data_input)),
        n
      )
 */
{
  /*@ Inv Assert
      (key == key@pre && data == data@pre && n == n@pre &&
       n@pre == 0 && i == 1 &&
       Zlength(key_input) == n@pre &&
       Zlength(data_input) == n@pre &&
       IntArray::full(key, n@pre, key_input) *
       IntArray::undef_seg(key, n@pre, heap_capacity) *
       IntArray::full(data, n@pre, data_input) *
       IntArray::undef_seg(data, n@pre, heap_capacity))
      ||
      (exists S_prefix key_prefix data_prefix,
        key == key@pre && data == data@pre && n == n@pre &&
        1 <= n@pre && n@pre <= heap_capacity &&
        1 <= i && i <= n@pre &&
        Zlength(key_input) == n@pre &&
        Zlength(data_input) == n@pre &&
        BuildPrefixState(S_prefix, key_input, data_input, i) &&
        heap_representation(S_prefix, key_prefix, data_prefix, i) &&
        IntArray::full(key, i, key_prefix) *
        IntArray::seg(key, i, n@pre, sublist(i, n@pre, key_input)) *
        IntArray::undef_seg(key, n@pre, heap_capacity) *
        IntArray::full(data, i, data_prefix) *
        IntArray::seg(data, i, n@pre, sublist(i, n@pre, data_input)) *
        IntArray::undef_seg(data, n@pre, heap_capacity))
   */
  for (int i = 1; i < n; ++i) {
    int data_x = data[i];
    int key_x = key[i];
    /*@ Assert
        exists S_prefix key_base data_base key_written data_written,
          key == key@pre && data == data@pre && n == n@pre &&
          1 <= n@pre && n@pre <= heap_capacity &&
          1 <= i && i < n@pre &&
          data_x == data_input[i] &&
          key_x == key_input[i] &&
          Zlength(key_input) == n@pre &&
          Zlength(data_input) == n@pre &&
          BuildPrefixState(S_prefix, key_input, data_input, i) &&
          heap_representation(S_prefix, key_base, data_base, i) &&
          PushSource(key_written, data_written,
            S_prefix, i, data_x, key_x) &&
          PushLoopState(key_written, data_written,
            key_written, data_written, i, i, data_x, key_x) &&
          IntArray::full(key, i + 1, key_written) *
          IntArray::seg(key, i + 1, n@pre,
                        sublist(i + 1, n@pre, key_input)) *
          IntArray::undef_seg(key, n@pre, heap_capacity) *
          IntArray::full(data, i + 1, data_written) *
          IntArray::seg(data, i + 1, n@pre,
                        sublist(i + 1, n@pre, data_input)) *
          IntArray::undef_seg(data, n@pre, heap_capacity)
     */
    int child = i;
    /*@ Inv Assert
        exists S_prefix key_written data_written key_current data_current,
          key == key@pre && data == data@pre && n == n@pre &&
          data_x == data_input[i] &&
          key_x == key_input[i] &&
          1 <= n@pre && n@pre <= heap_capacity &&
          1 <= i && i < n@pre &&
          0 <= child && child <= i &&
          Zlength(key_input) == n@pre &&
          Zlength(data_input) == n@pre &&
          BuildPrefixState(S_prefix, key_input, data_input, i) &&
          PushSource(key_written, data_written,
            S_prefix, i, data_x, key_x) &&
          PushLoopState(key_written, data_written,
            key_current, data_current, i, child,
            data_x, key_x) &&
          IntArray::full(key, i + 1, key_current) *
          IntArray::seg(key, i + 1, n@pre,
                        sublist(i + 1, n@pre, key_input)) *
          IntArray::undef_seg(key, n@pre, heap_capacity) *
          IntArray::full(data, i + 1, data_current) *
          IntArray::seg(data, i + 1, n@pre,
                        sublist(i + 1, n@pre, data_input)) *
          IntArray::undef_seg(data, n@pre, heap_capacity)
     */
    while (child > 0) {
      int parent = (child - 1) / 2;
      /*@ Assert
          exists S_prefix key_written data_written key_current data_current,
            key == key@pre && data == data@pre && n == n@pre &&
            data_x == data_input[i] &&
            key_x == key_input[i] &&
            1 <= n@pre && n@pre <= heap_capacity &&
            1 <= i && i < n@pre &&
            0 < child && child <= i &&
            0 <= parent && parent < child && parent <= i &&
            parent == heap_parent(child) &&
            Zlength(key_input) == n@pre &&
            Zlength(data_input) == n@pre &&
            BuildPrefixState(S_prefix, key_input, data_input, i) &&
            PushSource(key_written, data_written,
              S_prefix, i, data_x, key_x) &&
            PushLoopState(key_written, data_written,
              key_current, data_current, i, child,
              data_x, key_x) &&
            IntArray::full(key, i + 1, key_current) *
            IntArray::seg(key, i + 1, n@pre,
                          sublist(i + 1, n@pre, key_input)) *
            IntArray::undef_seg(key, n@pre, heap_capacity) *
            IntArray::full(data, i + 1, data_current) *
            IntArray::seg(data, i + 1, n@pre,
                          sublist(i + 1, n@pre, data_input)) *
            IntArray::undef_seg(data, n@pre, heap_capacity)
       */
      if (key[parent] <= key[child]) {
        /*@ Assert
            exists S_prefix key_written data_written key_current data_current,
              key == key@pre && data == data@pre && n == n@pre &&
              data_x == data_input[i] &&
              key_x == key_input[i] &&
              1 <= n@pre && n@pre <= heap_capacity &&
              1 <= i && i < n@pre &&
              0 < child && child <= i &&
              0 <= parent && parent < child && parent <= i &&
              parent == heap_parent(child) &&
              key_current[parent] <= key_current[child] &&
              Zlength(key_input) == n@pre &&
              Zlength(data_input) == n@pre &&
              BuildPrefixState(S_prefix, key_input, data_input, i) &&
              PushSource(key_written, data_written,
                S_prefix, i, data_x, key_x) &&
              PushResult(S_prefix, key_current, data_current,
                i, data_x, key_x) &&
              IntArray::full(key, i + 1, key_current) *
              IntArray::seg(key, i + 1, n@pre,
                            sublist(i + 1, n@pre, key_input)) *
              IntArray::undef_seg(key, n@pre, heap_capacity) *
              IntArray::full(data, i + 1, data_current) *
              IntArray::seg(data, i + 1, n@pre,
                            sublist(i + 1, n@pre, data_input)) *
              IntArray::undef_seg(data, n@pre, heap_capacity)
         */
        break;
      }
      int tmp_key = key[parent];
      key[parent] = key[child];
      key[child] = tmp_key;

      int tmp_data = data[parent];
      data[parent] = data[child];
      data[child] = tmp_data;
      /*@ Assert
          exists S_prefix key_written data_written key_current data_current,
            key == key@pre && data == data@pre && n == n@pre &&
            data_x == data_input[i] &&
            key_x == key_input[i] &&
            1 <= n@pre && n@pre <= heap_capacity &&
            1 <= i && i < n@pre &&
            0 < child && child <= i &&
            0 <= parent && parent < child && parent <= i &&
            parent == heap_parent(child) &&
            tmp_key == key_current[child] &&
            tmp_data == data_current[child] &&
            Zlength(key_input) == n@pre &&
            Zlength(data_input) == n@pre &&
            BuildPrefixState(S_prefix, key_input, data_input, i) &&
            PushSource(key_written, data_written,
              S_prefix, i, data_x, key_x) &&
            PushLoopState(key_written, data_written,
              key_current, data_current, i, parent,
              data_x, key_x) &&
            IntArray::full(key, i + 1, key_current) *
            IntArray::seg(key, i + 1, n@pre,
                          sublist(i + 1, n@pre, key_input)) *
            IntArray::undef_seg(key, n@pre, heap_capacity) *
            IntArray::full(data, i + 1, data_current) *
            IntArray::seg(data, i + 1, n@pre,
                          sublist(i + 1, n@pre, data_input)) *
            IntArray::undef_seg(data, n@pre, heap_capacity)
       */
      child = parent;
    }
    /*@ Assert
        exists S_prefix key_written data_written key_result data_result,
          key == key@pre && data == data@pre && n == n@pre &&
          1 <= n@pre && n@pre <= heap_capacity &&
          1 <= i && i < n@pre &&
          data_x == data_input[i] &&
          key_x == key_input[i] &&
          Zlength(key_input) == n@pre &&
          Zlength(data_input) == n@pre &&
          BuildPrefixState(S_prefix, key_input, data_input, i) &&
          PushSource(key_written, data_written,
            S_prefix, i, data_x, key_x) &&
          PushResult(S_prefix, key_result, data_result,
            i, data_x, key_x) &&
          IntArray::full(key, i + 1, key_result) *
          IntArray::seg(key, i + 1, n@pre,
                        sublist(i + 1, n@pre, key_input)) *
          IntArray::undef_seg(key, n@pre, heap_capacity) *
          IntArray::full(data, i + 1, data_result) *
          IntArray::seg(data, i + 1, n@pre,
                        sublist(i + 1, n@pre, data_input)) *
          IntArray::undef_seg(data, n@pre, heap_capacity) *
          store(&child, child)
     */
    /*@ Assert
        exists S_prefix key_result data_result,
          key == key@pre && data == data@pre && n == n@pre &&
          1 <= n@pre && n@pre <= heap_capacity &&
          1 <= i && i < n@pre &&
          data_x == data_input[i] &&
          key_x == key_input[i] &&
          Zlength(key_input) == n@pre &&
          Zlength(data_input) == n@pre &&
          BuildPrefixState(
            multiset_insert(S_prefix, heap_item(key_x, data_x)),
            key_input, data_input, i + 1
          ) &&
          heap_representation(
            multiset_insert(S_prefix, heap_item(key_x, data_x)),
            key_result, data_result, i + 1
          ) &&
          IntArray::full(key, i + 1, key_result) *
          IntArray::seg(key, i + 1, n@pre,
                        sublist(i + 1, n@pre, key_input)) *
          IntArray::undef_seg(key, n@pre, heap_capacity) *
          IntArray::full(data, i + 1, data_result) *
          IntArray::seg(data, i + 1, n@pre,
                        sublist(i + 1, n@pre, data_input)) *
          IntArray::undef_seg(data, n@pre, heap_capacity) *
          store(&child, child)
     */
  }
  /*@ Assert
      key == key@pre && data == data@pre && n == n@pre &&
      store_heap(
        key, data,
        list_to_multiset(pair_list(key_input, data_input)),
        n@pre
      )
   */
}

void pop(int *key, int *data, int n, int *data_out, int *key_out)
/*@ With (S_before : multiset (Z * Z))
    Require
      1 <= n &&
      store_heap(key, data, S_before, n) *
      has_int_permission(data_out) *
      has_int_permission(key_out)
    Ensure exists popped,
      *key_out == item_key(popped) &&
      *data_out == item_data(popped) &&
      multiset_minimum(S_before, popped) &&
      store_heap(
        key, data,
        multiset_remove(S_before, popped),
        n - 1
      )
 */
{
  /*@ Assert
      exists before_key before_data popped,
        key == key@pre && data == data@pre &&
        data_out == data_out@pre && key_out == key_out@pre &&
        n == n@pre &&
        1 <= n@pre && n@pre <= heap_capacity &&
        heap_representation(S_before, before_key, before_data, n@pre) &&
        PrefixMinimum(before_key, before_data,
          n@pre, popped) &&
        multiset_minimum(S_before, popped) &&
        IntArray::full(key, n@pre, before_key) *
        IntArray::undef_seg(key, n@pre, heap_capacity) *
        IntArray::full(data, n@pre, before_data) *
        IntArray::undef_seg(data, n@pre, heap_capacity) *
        has_int_permission(data_out) *
        has_int_permission(key_out)
   */
  int result_key = key[0];
  int result_data = data[0];
  /*@ Assert
      exists before_key before_data popped,
        key == key@pre && data == data@pre &&
        data_out == data_out@pre && key_out == key_out@pre &&
        n == n@pre &&
        result_key == item_key(popped) &&
        result_data == item_data(popped) &&
        1 <= n@pre && n@pre <= heap_capacity &&
        heap_representation(S_before, before_key, before_data, n@pre) &&
        PrefixMinimum(before_key, before_data,
          n@pre, popped) &&
        multiset_minimum(S_before, popped) &&
        IntArray::full(key, n@pre, before_key) *
        IntArray::undef_seg(key, n@pre, heap_capacity) *
        IntArray::full(data, n@pre, before_data) *
        IntArray::undef_seg(data, n@pre, heap_capacity) *
        has_int_permission(data_out) *
        has_int_permission(key_out)
   */
  if (n == 1) {
      /*@ Assert
        exists popped,
        key == key@pre && data == data@pre &&
        data_out == data_out@pre && key_out == key_out@pre &&
        n@pre == 1 &&
        result_key == item_key(popped) &&
        result_data == item_data(popped) &&
        multiset_minimum(S_before, popped) &&
        store_heap(
          key, data,
          multiset_remove(S_before, popped),
          0
        ) *
        store(&n, n@pre) *
        has_int_permission(data_out) *
        has_int_permission(key_out)
     */
      *key_out = result_key;
      *data_out = result_data;
    return;
  }

  /*@ Assert
      exists before_key before_data popped,
        key == key@pre && data == data@pre &&
        data_out == data_out@pre && key_out == key_out@pre &&
        n == n@pre &&
        result_key == item_key(popped) &&
        result_data == item_data(popped) &&
        1 < n@pre && n@pre <= heap_capacity &&
        0 <= n@pre - 1 && n@pre - 1 < n@pre &&
        n@pre - 1 <= INT_MAX &&
        heap_representation(S_before, before_key, before_data, n@pre) &&
        PrefixMinimum(before_key, before_data,
          n@pre, popped) &&
        multiset_minimum(S_before, popped) &&
        IntArray::full(key, n@pre, before_key) *
        IntArray::undef_seg(key, n@pre, heap_capacity) *
        IntArray::full(data, n@pre, before_data) *
        IntArray::undef_seg(data, n@pre, heap_capacity) *
        has_int_permission(data_out) *
        has_int_permission(key_out)
   */
  key[0] = key[n - 1];
  data[0] = data[n - 1];
  /*@ Assert
      exists before_key before_data current_key current_data popped,
        key == key@pre && data == data@pre &&
        data_out == data_out@pre && key_out == key_out@pre &&
        n == n@pre &&
        result_key == item_key(popped) &&
        result_data == item_data(popped) &&
        1 < n@pre && n@pre <= heap_capacity &&
        heap_representation(S_before, before_key, before_data, n@pre) &&
        PrefixMinimum(before_key, before_data,
          n@pre, popped) &&
        multiset_minimum(S_before, popped) &&
        PopLoopState(before_key, before_data,
          current_key, current_data, n@pre, 0) &&
        IntArray::full(key, n@pre, current_key) *
        IntArray::undef_seg(key, n@pre, heap_capacity) *
        IntArray::full(data, n@pre, current_data) *
        IntArray::undef_seg(data, n@pre, heap_capacity) *
        has_int_permission(data_out) *
        has_int_permission(key_out)
   */
  int idx = 0;
  /*@ Inv Assert
      exists before_key before_data current_key current_data popped,
        key == key@pre && data == data@pre &&
        data_out == data_out@pre && key_out == key_out@pre &&
        n == n@pre &&
        result_key == item_key(popped) &&
        result_data == item_data(popped) &&
        1 < n@pre && n@pre <= heap_capacity &&
        0 <= idx && idx < n@pre - 1 &&
        0 <= idx * 2 + 1 && idx * 2 + 1 <= INT_MAX &&
        heap_representation(S_before, before_key, before_data, n@pre) &&
        PrefixMinimum(before_key, before_data,
          n@pre, popped) &&
        multiset_minimum(S_before, popped) &&
        PopLoopState(before_key, before_data,
          current_key, current_data, n@pre, idx) &&
        IntArray::full(key, n@pre, current_key) *
        IntArray::undef_seg(key, n@pre, heap_capacity) *
        IntArray::full(data, n@pre, current_data) *
        IntArray::undef_seg(data, n@pre, heap_capacity) *
        has_int_permission(data_out) *
        has_int_permission(key_out)
   */
  while (idx * 2 + 1 < n - 1) {
    int left = idx * 2 + 1;
    int right = left + 1;
    int smallest = left;
    /*@ Assert
        exists before_key before_data current_key current_data popped,
          key == key@pre && data == data@pre &&
          data_out == data_out@pre && key_out == key_out@pre &&
          n == n@pre &&
          result_key == item_key(popped) &&
          result_data == item_data(popped) &&
          1 < n@pre && n@pre <= heap_capacity &&
          0 <= idx && idx < n@pre - 1 &&
          left == idx * 2 + 1 &&
          right == left + 1 &&
          smallest == left &&
          0 <= left && left < n@pre - 1 &&
          0 <= right && right <= n@pre - 1 &&
          heap_representation(S_before, before_key, before_data, n@pre) &&
          PrefixMinimum(before_key, before_data,
            n@pre, popped) &&
          multiset_minimum(S_before, popped) &&
          PopLoopState(before_key, before_data,
            current_key, current_data, n@pre, idx) &&
          IntArray::full(key, n@pre, current_key) *
          IntArray::undef_seg(key, n@pre, heap_capacity) *
          IntArray::full(data, n@pre, current_data) *
          IntArray::undef_seg(data, n@pre, heap_capacity) *
          has_int_permission(data_out) *
          has_int_permission(key_out)
     */
    if (right < n - 1 && key[right] < key[left]) {
      smallest = right;
    }
    /*@ Assert
        exists before_key before_data current_key current_data popped,
          key == key@pre && data == data@pre &&
          data_out == data_out@pre && key_out == key_out@pre &&
          n == n@pre &&
          result_key == item_key(popped) &&
          result_data == item_data(popped) &&
          1 < n@pre && n@pre <= heap_capacity &&
          0 <= idx && idx < n@pre - 1 &&
          left == idx * 2 + 1 &&
          right == left + 1 &&
          0 <= smallest && smallest < n@pre - 1 &&
          PopSelectedChild(current_key, n@pre - 1, idx, smallest) &&
          heap_representation(S_before, before_key, before_data, n@pre) &&
          PrefixMinimum(before_key, before_data,
            n@pre, popped) &&
          multiset_minimum(S_before, popped) &&
          PopLoopState(before_key, before_data,
            current_key, current_data, n@pre, idx) &&
          IntArray::full(key, n@pre, current_key) *
          IntArray::undef_seg(key, n@pre, heap_capacity) *
          IntArray::full(data, n@pre, current_data) *
          IntArray::undef_seg(data, n@pre, heap_capacity) *
          has_int_permission(data_out) *
          has_int_permission(key_out)
     */
    if (key[idx] <= key[smallest]) {
      /*@ Assert
          exists before_key before_data current_key current_data popped,
            key == key@pre && data == data@pre &&
            data_out == data_out@pre && key_out == key_out@pre &&
            n == n@pre &&
            result_key == item_key(popped) &&
            result_data == item_data(popped) &&
            1 < n@pre && n@pre <= heap_capacity &&
            0 <= idx && idx < n@pre - 1 &&
            left == idx * 2 + 1 &&
            right == left + 1 &&
            0 <= left && left < n@pre - 1 &&
            0 <= right && right <= n@pre - 1 &&
            0 <= smallest && smallest < n@pre - 1 &&
            current_key[idx] <= current_key[smallest] &&
            PopSelectedChild(current_key, n@pre - 1, idx, smallest) &&
            heap_representation(S_before, before_key, before_data, n@pre) &&
            PrefixMinimum(before_key, before_data,
              n@pre, popped) &&
            multiset_minimum(S_before, popped) &&
            PopReadyState(before_key, before_data,
              current_key, current_data, n@pre, popped) &&
            IntArray::full(key, n@pre, current_key) *
            IntArray::undef_seg(key, n@pre, heap_capacity) *
            IntArray::full(data, n@pre, current_data) *
            IntArray::undef_seg(data, n@pre, heap_capacity) *
            has_int_permission(data_out) *
            has_int_permission(key_out)
       */
      break;
    }
    int tmp_key = key[idx];
    key[idx] = key[smallest];
    key[smallest] = tmp_key;

    int tmp_data = data[idx];
    data[idx] = data[smallest];
    data[smallest] = tmp_data;
    /*@ Assert
        exists before_key before_data current_key current_data popped,
          key == key@pre && data == data@pre &&
          data_out == data_out@pre && key_out == key_out@pre &&
          n == n@pre &&
          result_key == item_key(popped) &&
          result_data == item_data(popped) &&
          1 < n@pre && n@pre <= heap_capacity &&
          0 <= idx && idx < n@pre - 1 &&
          left == idx * 2 + 1 &&
          right == left + 1 &&
          0 <= left && left < n@pre - 1 &&
          0 <= right && right <= n@pre - 1 &&
          0 <= smallest && smallest < n@pre - 1 &&
          idx < smallest &&
          tmp_key == current_key[smallest] &&
          tmp_data == current_data[smallest] &&
          heap_representation(S_before, before_key, before_data, n@pre) &&
          PrefixMinimum(before_key, before_data,
            n@pre, popped) &&
          multiset_minimum(S_before, popped) &&
          PopLoopState(before_key, before_data,
            current_key, current_data, n@pre, smallest) &&
          IntArray::full(key, n@pre, current_key) *
          IntArray::undef_seg(key, n@pre, heap_capacity) *
          IntArray::full(data, n@pre, current_data) *
          IntArray::undef_seg(data, n@pre, heap_capacity) *
          has_int_permission(data_out) *
          has_int_permission(key_out)
     */
    idx = smallest;
  }
  /*@ Assert
      exists before_key before_data current_key current_data popped,
        key == key@pre && data == data@pre &&
        data_out == data_out@pre && key_out == key_out@pre &&
        n == n@pre &&
        result_key == item_key(popped) &&
        result_data == item_data(popped) &&
        1 < n@pre && n@pre <= heap_capacity &&
        0 <= idx && idx < n@pre - 1 &&
        heap_representation(S_before, before_key, before_data, n@pre) &&
        PrefixMinimum(before_key, before_data,
          n@pre, popped) &&
        multiset_minimum(S_before, popped) &&
        PopReadyState(before_key, before_data,
          current_key, current_data, n@pre, popped) &&
        IntArray::full(key, n@pre, current_key) *
        IntArray::undef_seg(key, n@pre, heap_capacity) *
        IntArray::full(data, n@pre, current_data) *
        IntArray::undef_seg(data, n@pre, heap_capacity) *
        has_int_permission(data_out) *
        has_int_permission(key_out)
   */
  /*@ Assert
      exists before_key before_data result_key_values result_data_values popped,
        key == key@pre && data == data@pre &&
        data_out == data_out@pre && key_out == key_out@pre &&
        n == n@pre &&
        result_key == item_key(popped) &&
        result_data == item_data(popped) &&
        1 < n@pre && n@pre <= heap_capacity &&
        0 <= idx && idx < n@pre - 1 &&
        heap_representation(S_before, before_key, before_data, n@pre) &&
        PrefixMinimum(before_key, before_data,
          n@pre, popped) &&
        multiset_minimum(S_before, popped) &&
        PopResult(S_before, before_key, before_data,
          result_key_values, result_data_values, n@pre, popped) &&
        IntArray::full(key, n@pre, result_key_values) *
        IntArray::undef_seg(key, n@pre, heap_capacity) *
        IntArray::full(data, n@pre, result_data_values) *
        IntArray::undef_seg(data, n@pre, heap_capacity) *
        has_int_permission(data_out) *
        has_int_permission(key_out)
   */
  /*@ Assert
      exists popped,
      key == key@pre && data == data@pre &&
      data_out == data_out@pre && key_out == key_out@pre &&
      n == n@pre &&
      result_key == item_key(popped) &&
      result_data == item_data(popped) &&
      0 <= idx && idx < n@pre - 1 &&
      multiset_minimum(S_before, popped) &&
      store_heap(
        key, data,
        multiset_remove(S_before, popped),
        n@pre - 1
      ) *
      has_int_permission(data_out) *
      has_int_permission(key_out)
   */
  *key_out = result_key;
  *data_out = result_data;
  return;
}
