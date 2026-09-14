#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (partial_map :: *) */
/*@ Extern Coq
      (heap_capacity : Z)
      (heap_item : Z -> Z -> Z * Z)
      (item_key : Z * Z -> Z)
      (item_data : Z * Z -> Z)
      (pair_list : list Z -> list Z -> list (Z * Z))
      (absent : Z)
      (partial_map_get : partial_map -> Z -> option Z)
      (partial_map_add : partial_map -> Z -> Z -> partial_map)
      (partial_map_update : partial_map -> Z -> Z -> partial_map)
      (partial_map_update_or_add : partial_map -> Z -> Z -> partial_map)
      (partial_map_remove : partial_map -> Z -> partial_map)
      (partial_map_absent : partial_map -> Z -> Prop)
      (partial_map_present : partial_map -> Z -> Z -> Prop)
      (partial_map_contains : partial_map -> Z -> Prop)
      (partial_map_minimum : partial_map -> Z * Z -> Prop)
      (partial_map_decrease_key_pre :
        partial_map -> Z -> Z -> Prop)
      (partial_map_update_or_add_pre :
        partial_map -> Z -> Z -> Prop)
      (partial_map_update_or_add_size :
        partial_map -> Z -> Z -> Z -> Z -> Prop)
      (store_heap :
        Z -> Z -> Z -> Z -> Z -> partial_map -> Z -> Assertion)
      (store_sift_up :
        Z -> Z -> Z -> Z -> Z -> partial_map -> Z -> Z -> Assertion)
      (store_sift_down :
        Z -> Z -> Z -> Z -> Z -> partial_map -> Z -> Z -> Assertion)
      (heap_representation :
        partial_map ->
        list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (heap_parent : Z -> Z)
      (heap_data_absent :
        partial_map -> Z -> Prop)
      (heap_data_present :
        partial_map -> Z -> Prop)
      (heap_index_of :
        partial_map -> list Z -> list Z -> Z -> Z -> Prop)
      (SiftUpState :
        partial_map ->
        list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (SelectedChild :
        list Z -> Z -> Z -> Z -> Prop)
      (SiftDownState :
        partial_map ->
        list Z -> list Z -> list Z -> Z -> Z -> Z -> Prop)
      (PushWriteState :
        partial_map ->
        list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (DecreaseKeyWriteState :
        partial_map ->
        list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (PopRootState :
        partial_map ->
        list Z -> list Z -> list Z -> Z -> Z -> Z * Z -> Prop)
      (PopMarkedState :
        partial_map ->
        list Z -> list Z -> list Z -> Z -> Z -> Z * Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_lib */

void pqdk_sift_up(int *key, int *data, int *pos, int data_bound,
                  int n, int idx)
/*@ With (M : partial_map) (capacity : Z)
    Require
      0 <= idx && idx < n &&
      n <= capacity && capacity <= heap_capacity &&
      store_sift_up(
        key, data, pos, data_bound, capacity, M, n, idx
      )
    Ensure
      store_heap(
        key, data, pos, data_bound, capacity, M, n
      )
 */
;

void pqdk_sift_down(int *key, int *data, int *pos, int data_bound,
                    int n, int idx)
/*@ With (M : partial_map) (capacity : Z)
    Require
      0 <= idx && idx < n &&
      n <= capacity && capacity <= heap_capacity &&
      store_sift_down(
        key, data, pos, data_bound, capacity, M, n, idx
      )
    Ensure
      store_heap(
        key, data, pos, data_bound, capacity, M, n
      )
 */
;

void pqdk_push(int *key, int *data, int *pos, int *size,
               int data_bound, int data_x, int key_x)
/*@ With (M_before : partial_map) (n capacity : Z)
    Require
      0 <= n && n < capacity && capacity <= heap_capacity &&
      0 <= data_x && data_x < data_bound &&
      partial_map_absent(M_before, data_x) &&
      store(size, int, n) *
      store_heap(
        key, data, pos, data_bound, capacity, M_before, n
      )
    Ensure
      store(size, int, n + 1) *
      store_heap(
        key, data, pos, data_bound, capacity,
        partial_map_add(M_before, data_x, key_x), n + 1
      )
 */
;

void pqdk_decrease_key(int *key, int *data, int *pos, int *size,
                       int data_bound, int data_x, int key_x)
/*@ With (M_before : partial_map) (n capacity : Z)
    Require
      0 <= n && n <= capacity && capacity <= heap_capacity &&
      0 <= data_x && data_x < data_bound &&
      partial_map_decrease_key_pre(
        M_before, data_x, key_x
      ) &&
      store(size, int, n) *
      store_heap(
        key, data, pos, data_bound, capacity, M_before, n
      )
    Ensure
      store(size, int, n) *
      store_heap(
        key, data, pos, data_bound, capacity,
        partial_map_update(M_before, data_x, key_x), n
      )
 */
;

void pqdk_update_or_push(int *key, int *data, int *pos, int *size,
                         int data_bound, int data_x, int key_x)
/*@ With (M_before : partial_map) (n capacity : Z)
    Require
      0 <= n && n < capacity && capacity <= heap_capacity &&
      0 <= data_x && data_x < data_bound &&
      partial_map_update_or_add_pre(
        M_before, data_x, key_x
      ) &&
      store(size, int, n) *
      store_heap(
        key, data, pos, data_bound, capacity, M_before, n
      )
    Ensure exists n_after,
      partial_map_update_or_add_size(
        M_before, n, n_after, data_x, key_x
      ) &&
      store(size, int, n_after) *
      store_heap(
        key, data, pos, data_bound, capacity,
        partial_map_update_or_add(M_before, data_x, key_x), n_after
      )
 */
;

void pqdk_pop(int *key, int *data, int *pos, int *size,
              int data_bound, int *data_out, int *key_out)
/*@ With (M_before : partial_map) (n capacity : Z)
    Require
      1 <= n && n <= capacity && capacity <= heap_capacity &&
      store(size, int, n) *
      store_heap(
        key, data, pos, data_bound, capacity, M_before, n
      ) *
      has_int_permission(data_out) *
      has_int_permission(key_out)
    Ensure exists popped,
      *key_out == item_key(popped) &&
      *data_out == item_data(popped) &&
      partial_map_minimum(M_before, popped) &&
      store(size, int, n - 1) *
      store_heap(
        key, data, pos, data_bound, capacity,
        partial_map_remove(M_before, item_data(popped)), n - 1
      )
 */
;
