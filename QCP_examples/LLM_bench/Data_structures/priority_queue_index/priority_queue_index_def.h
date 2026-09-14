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
;

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
;

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
;
