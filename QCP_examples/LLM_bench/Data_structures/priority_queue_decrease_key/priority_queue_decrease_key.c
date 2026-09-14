#include "priority_queue_decrease_key_def.h"

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
{
  int child = idx;
  /*@ Inv Assert
      exists key_values data_values pos_values,
        key == key@pre && data == data@pre &&
        pos == pos@pre && data_bound == data_bound@pre &&
        n == n@pre && idx == idx@pre &&
        n@pre <= capacity && capacity <= heap_capacity &&
        0 <= child && child < n@pre &&
        SiftUpState(
          M, key_values, data_values, pos_values,
          data_bound@pre, n@pre, child
        ) &&
        IntArray::full(key, n@pre, key_values) *
        IntArray::undef_seg(key, n@pre, capacity) *
        IntArray::full(data, n@pre, data_values) *
        IntArray::undef_seg(data, n@pre, capacity) *
        IntArray::full(pos, data_bound@pre, pos_values)
   */
  while (child > 0) {
    int parent = (child - 1) / 2;
    /*@ Assert
        exists key_values data_values pos_values,
          key == key@pre && data == data@pre &&
          pos == pos@pre && data_bound == data_bound@pre &&
          n == n@pre && idx == idx@pre &&
        n@pre <= capacity && capacity <= heap_capacity &&
          0 < child && child < n@pre &&
          0 <= parent && parent < child && parent < n@pre &&
          parent == heap_parent(child) &&
          SiftUpState(
            M, key_values, data_values, pos_values,
            data_bound@pre, n@pre, child
          ) &&
          IntArray::full(key, n@pre, key_values) *
          IntArray::undef_seg(key, n@pre, capacity) *
          IntArray::full(data, n@pre, data_values) *
          IntArray::undef_seg(data, n@pre, capacity) *
          IntArray::full(pos, data_bound@pre, pos_values)
     */
    if (key[parent] <= key[child]) {
      break;
    }

    int tmp_key = key[parent];
    int tmp_data = data[parent];
    /*@ Assert
        exists key_values data_values pos_values,
          key == key@pre && data == data@pre &&
          pos == pos@pre && data_bound == data_bound@pre &&
          n == n@pre && idx == idx@pre &&
        n@pre <= capacity && capacity <= heap_capacity &&
          0 < child && child < n@pre &&
          0 <= parent && parent < child && parent < n@pre &&
          parent == heap_parent(child) &&
          key_values[parent] > key_values[child] &&
          tmp_key == key_values[parent] &&
          tmp_data == data_values[parent] &&
          0 <= data_values[parent] &&
          data_values[parent] < data_bound@pre &&
          0 <= data_values[child] &&
          data_values[child] < data_bound@pre &&
          SiftUpState(
            M, key_values, data_values, pos_values,
            data_bound@pre, n@pre, child
          ) &&
          IntArray::full(key, n@pre, key_values) *
          IntArray::undef_seg(key, n@pre, capacity) *
          IntArray::full(data, n@pre, data_values) *
          IntArray::undef_seg(data, n@pre, capacity) *
          IntArray::full(pos, data_bound@pre, pos_values)
     */
    pos[data[parent]] = child;
    pos[data[child]] = parent;
    key[parent] = key[child];
    data[parent] = data[child];
    key[child] = tmp_key;
    data[child] = tmp_data;
    /*@ Assert
        exists key_values data_values pos_values,
          key == key@pre && data == data@pre &&
          pos == pos@pre && data_bound == data_bound@pre &&
          n == n@pre && idx == idx@pre &&
        n@pre <= capacity && capacity <= heap_capacity &&
          0 < child && child < n@pre &&
          0 <= parent && parent < child && parent < n@pre &&
          parent == heap_parent(child) &&
          tmp_key == key_values[child] &&
          tmp_data == data_values[child] &&
          0 <= data_values[parent] &&
          data_values[parent] < data_bound@pre &&
          0 <= data_values[child] &&
          data_values[child] < data_bound@pre &&
          SiftUpState(
            M, key_values, data_values, pos_values,
            data_bound@pre, n@pre, parent
          ) &&
          IntArray::full(key, n@pre, key_values) *
          IntArray::undef_seg(key, n@pre, capacity) *
          IntArray::full(data, n@pre, data_values) *
          IntArray::undef_seg(data, n@pre, capacity) *
          IntArray::full(pos, data_bound@pre, pos_values)
     */
    child = parent;
  }
}

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
{
  int current = idx;
  /*@ Inv Assert
      exists key_values data_values pos_values,
        key == key@pre && data == data@pre &&
        pos == pos@pre && data_bound == data_bound@pre &&
        n == n@pre && idx == idx@pre &&
        n@pre <= capacity && capacity <= heap_capacity &&
        0 <= current && current < n@pre &&
        SiftDownState(
          M, key_values, data_values, pos_values,
          data_bound@pre, n@pre, current
        ) &&
        IntArray::full(key, n@pre, key_values) *
        IntArray::undef_seg(key, n@pre, capacity) *
        IntArray::full(data, n@pre, data_values) *
        IntArray::undef_seg(data, n@pre, capacity) *
        IntArray::full(pos, data_bound@pre, pos_values)
   */
  while (current * 2 + 1 < n) {
    int left = current * 2 + 1;
    int right = left + 1;
    int smallest = left;
    /*@ Assert
        exists key_values data_values pos_values,
          key == key@pre && data == data@pre &&
          pos == pos@pre && data_bound == data_bound@pre &&
          n == n@pre && idx == idx@pre &&
        n@pre <= capacity && capacity <= heap_capacity &&
          0 <= current && current < n@pre &&
          left == current * 2 + 1 &&
          right == left + 1 &&
          smallest == left &&
          0 <= left && left < n@pre &&
          0 <= right &&
          SiftDownState(
            M, key_values, data_values, pos_values,
            data_bound@pre, n@pre, current
          ) &&
          IntArray::full(key, n@pre, key_values) *
          IntArray::undef_seg(key, n@pre, capacity) *
          IntArray::full(data, n@pre, data_values) *
          IntArray::undef_seg(data, n@pre, capacity) *
          IntArray::full(pos, data_bound@pre, pos_values)
     */

    if (right < n && key[right] < key[left]) {
      smallest = right;
    }
    /*@ Assert
        exists key_values data_values pos_values,
          key == key@pre && data == data@pre &&
          pos == pos@pre && data_bound == data_bound@pre &&
          n == n@pre && idx == idx@pre &&
        n@pre <= capacity && capacity <= heap_capacity &&
          0 <= current && current < n@pre &&
          left == current * 2 + 1 &&
          right == left + 1 &&
          0 <= smallest && smallest < n@pre &&
          SelectedChild(
            key_values, n@pre, current, smallest
          ) &&
          SiftDownState(
            M, key_values, data_values, pos_values,
            data_bound@pre, n@pre, current
          ) &&
          IntArray::full(key, n@pre, key_values) *
          IntArray::undef_seg(key, n@pre, capacity) *
          IntArray::full(data, n@pre, data_values) *
          IntArray::undef_seg(data, n@pre, capacity) *
          IntArray::full(pos, data_bound@pre, pos_values)
     */

    if (key[current] <= key[smallest]) {
      break;
    }

    int tmp_key = key[current];
    int tmp_data = data[current];
    /*@ Assert
        exists key_values data_values pos_values,
          key == key@pre && data == data@pre &&
          pos == pos@pre && data_bound == data_bound@pre &&
          n == n@pre && idx == idx@pre &&
        n@pre <= capacity && capacity <= heap_capacity &&
          0 <= current && current < n@pre &&
          left == current * 2 + 1 &&
          right == left + 1 &&
          0 <= left && left < n@pre &&
          0 <= right &&
          0 <= smallest && smallest < n@pre &&
          current < smallest &&
          key_values[current] > key_values[smallest] &&
          tmp_key == key_values[current] &&
          tmp_data == data_values[current] &&
          0 <= data_values[current] &&
          data_values[current] < data_bound@pre &&
          0 <= data_values[smallest] &&
          data_values[smallest] < data_bound@pre &&
          SelectedChild(
            key_values, n@pre, current, smallest
          ) &&
          SiftDownState(
            M, key_values, data_values, pos_values,
            data_bound@pre, n@pre, current
          ) &&
          IntArray::full(key, n@pre, key_values) *
          IntArray::undef_seg(key, n@pre, capacity) *
          IntArray::full(data, n@pre, data_values) *
          IntArray::undef_seg(data, n@pre, capacity) *
          IntArray::full(pos, data_bound@pre, pos_values)
     */
    pos[data[current]] = smallest;
    pos[data[smallest]] = current;
    key[current] = key[smallest];
    data[current] = data[smallest];
    key[smallest] = tmp_key;
    data[smallest] = tmp_data;
    /*@ Assert
        exists key_values data_values pos_values,
          key == key@pre && data == data@pre &&
          pos == pos@pre && data_bound == data_bound@pre &&
          n == n@pre && idx == idx@pre &&
        n@pre <= capacity && capacity <= heap_capacity &&
          0 <= current && current < n@pre &&
          left == current * 2 + 1 &&
          right == left + 1 &&
          0 <= left && left < n@pre &&
          0 <= right &&
          0 <= smallest && smallest < n@pre &&
          current < smallest &&
          tmp_key > key_values[current] &&
          tmp_key == key_values[smallest] &&
          tmp_data == data_values[smallest] &&
          0 <= data_values[current] &&
          data_values[current] < data_bound@pre &&
          0 <= data_values[smallest] &&
          data_values[smallest] < data_bound@pre &&
          SiftDownState(
            M, key_values, data_values, pos_values,
            data_bound@pre, n@pre, smallest
          ) &&
          IntArray::full(key, n@pre, key_values) *
          IntArray::undef_seg(key, n@pre, capacity) *
          IntArray::full(data, n@pre, data_values) *
          IntArray::undef_seg(data, n@pre, capacity) *
          IntArray::full(pos, data_bound@pre, pos_values)
     */
    current = smallest;
  }
}

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
{
  int n0 = *size;
  /*@ Assert
      exists key_values data_values pos_values,
        key == key@pre && data == data@pre &&
        pos == pos@pre && size == size@pre &&
        data_bound == data_bound@pre &&
        data_x == data_x@pre && key_x == key_x@pre &&
        n0 == n &&
        0 <= n && n < capacity && capacity <= heap_capacity &&
        0 <= data_x@pre && data_x@pre < data_bound@pre &&
        partial_map_absent(
          M_before, data_x@pre
        ) &&
        heap_representation(
          M_before, key_values, data_values, pos_values,
          data_bound@pre, n
        ) &&
        store(size, int, n) *
        IntArray::full(key, n, key_values) *
        IntArray::undef_seg(key, n, capacity) *
        IntArray::full(data, n, data_values) *
        IntArray::undef_seg(data, n, capacity) *
        IntArray::full(pos, data_bound@pre, pos_values)
   */
  key[n0] = key_x;
  data[n0] = data_x;
  pos[data_x] = n0;
  *size = n0 + 1;
  /*@ Assert
      exists key_values data_values pos_values,
        key == key@pre && data == data@pre &&
        pos == pos@pre && size == size@pre &&
        data_bound == data_bound@pre &&
        data_x == data_x@pre && key_x == key_x@pre &&
        n0 == n &&
        0 <= n && n < capacity && capacity <= heap_capacity &&
        PushWriteState(
          M_before, key_values, data_values, pos_values,
          data_bound@pre, n, data_x@pre, key_x@pre
        ) &&
        store(size, int, n + 1) *
        IntArray::full(key, n + 1, key_values) *
        IntArray::undef_seg(key, n + 1, capacity) *
        IntArray::full(data, n + 1, data_values) *
        IntArray::undef_seg(data, n + 1, capacity) *
        IntArray::full(pos, data_bound@pre, pos_values)
   */
  /*@ Assert
      key == key@pre && data == data@pre &&
        pos == pos@pre && size == size@pre &&
        data_bound == data_bound@pre &&
        data_x == data_x@pre && key_x == key_x@pre &&
        n0 == n &&
        0 <= n && n < capacity && capacity <= heap_capacity &&
        store(size, int, n + 1) *
        store_sift_up(
          key, data, pos, data_bound@pre, capacity,
          partial_map_add(M_before, data_x@pre, key_x@pre), n + 1, n
        )
   */
  pqdk_sift_up(key, data, pos, data_bound, n0 + 1, n0);
}

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
{
  /*@ Assert
      exists key_values data_values pos_values,
        key == key@pre && data == data@pre &&
        pos == pos@pre && size == size@pre &&
        data_bound == data_bound@pre &&
        data_x == data_x@pre && key_x == key_x@pre &&
        0 <= n && n <= capacity && capacity <= heap_capacity &&
        0 <= data_x@pre && data_x@pre < data_bound@pre &&
        partial_map_decrease_key_pre(
          M_before, data_x@pre, key_x@pre
        ) &&
        heap_representation(
          M_before, key_values, data_values, pos_values,
          data_bound@pre, n
        ) &&
        store(size, int, n) *
        IntArray::full(key, n, key_values) *
        IntArray::undef_seg(key, n, capacity) *
        IntArray::full(data, n, data_values) *
        IntArray::undef_seg(data, n, capacity) *
        IntArray::full(pos, data_bound@pre, pos_values)
   */
  int n0 = *size;
  int idx = pos[data_x];
  /*@ Assert
      exists key_values data_values pos_values,
        key == key@pre && data == data@pre &&
        pos == pos@pre && size == size@pre &&
        data_bound == data_bound@pre &&
        data_x == data_x@pre && key_x == key_x@pre &&
        n0 == n &&
        0 <= n && n <= capacity && capacity <= heap_capacity &&
        0 <= idx && idx < n &&
        partial_map_decrease_key_pre(
          M_before, data_x@pre, key_x@pre
        ) &&
        heap_index_of(
          M_before, data_values, pos_values, data_x@pre, idx
        ) &&
        heap_representation(
          M_before, key_values, data_values, pos_values,
          data_bound@pre, n
        ) &&
        store(size, int, n) *
        IntArray::full(key, n, key_values) *
        IntArray::undef_seg(key, n, capacity) *
        IntArray::full(data, n, data_values) *
        IntArray::undef_seg(data, n, capacity) *
        IntArray::full(pos, data_bound@pre, pos_values)
   */
  key[idx] = key_x;
  /*@ Assert
      exists key_values data_values pos_values,
        key == key@pre && data == data@pre &&
        pos == pos@pre && size == size@pre &&
        data_bound == data_bound@pre &&
        data_x == data_x@pre && key_x == key_x@pre &&
        n0 == n &&
        0 <= n && n <= capacity && capacity <= heap_capacity &&
        0 <= idx && idx < n &&
        DecreaseKeyWriteState(
          M_before, key_values, data_values, pos_values,
          data_bound@pre, n, data_x@pre, key_x@pre, idx
        ) &&
        store(size, int, n) *
        IntArray::full(key, n, key_values) *
        IntArray::undef_seg(key, n, capacity) *
        IntArray::full(data, n, data_values) *
        IntArray::undef_seg(data, n, capacity) *
        IntArray::full(pos, data_bound@pre, pos_values)
   */
  /*@ Assert
      key == key@pre && data == data@pre &&
        pos == pos@pre && size == size@pre &&
        data_bound == data_bound@pre &&
        data_x == data_x@pre && key_x == key_x@pre &&
        n0 == n &&
        0 <= n && n <= capacity && capacity <= heap_capacity &&
        0 <= idx && idx < n &&
        store(size, int, n) *
        store_sift_up(
          key, data, pos, data_bound@pre, capacity,
          partial_map_update(M_before, data_x@pre, key_x@pre), n, idx
        )
   */
  pqdk_sift_up(key, data, pos, data_bound, n0, idx);
}

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
{
  /*@ Assert
      exists key_values data_values pos_values,
        key == key@pre && data == data@pre &&
        pos == pos@pre && size == size@pre &&
        data_bound == data_bound@pre &&
        data_x == data_x@pre && key_x == key_x@pre &&
        0 <= n && n < capacity && capacity <= heap_capacity &&
        0 <= data_x@pre && data_x@pre < data_bound@pre &&
        partial_map_update_or_add_pre(
          M_before, data_x@pre, key_x@pre
        ) &&
        heap_representation(
          M_before, key_values, data_values, pos_values,
          data_bound@pre, n
        ) &&
        store(size, int, n) *
        IntArray::full(key, n, key_values) *
        IntArray::undef_seg(key, n, capacity) *
        IntArray::full(data, n, data_values) *
        IntArray::undef_seg(data, n, capacity) *
        IntArray::full(pos, data_bound@pre, pos_values)
   */
  int idx = pos[data_x];
  if (idx < 0) {
    /*@ Assert
        key == key@pre && data == data@pre &&
        pos == pos@pre && size == size@pre &&
        data_bound == data_bound@pre &&
        data_x == data_x@pre && key_x == key_x@pre &&
        idx == idx &&
        0 <= n && n < capacity && capacity <= heap_capacity &&
        0 <= data_x@pre && data_x@pre < data_bound@pre &&
        partial_map_absent(
          M_before, data_x@pre
        ) &&
        store(size, int, n) *
        store_heap(
          key, data, pos, data_bound@pre, capacity, M_before, n
        )
     */
    pqdk_push(key, data, pos, size, data_bound, data_x, key_x);
  } else {
    /*@ Assert
        key == key@pre && data == data@pre &&
        pos == pos@pre && size == size@pre &&
        data_bound == data_bound@pre &&
        data_x == data_x@pre && key_x == key_x@pre &&
        idx == idx &&
        0 <= n && n < capacity && capacity <= heap_capacity &&
        0 <= data_x@pre && data_x@pre < data_bound@pre &&
        partial_map_decrease_key_pre(
          M_before, data_x@pre, key_x@pre
        ) &&
        store(size, int, n) *
        store_heap(
          key, data, pos, data_bound@pre, capacity, M_before, n
        )
     */
    pqdk_decrease_key(key, data, pos, size, data_bound, data_x, key_x);
  }
  /*@ Assert
      exists n_after,
        key == key@pre && data == data@pre &&
        pos == pos@pre && size == size@pre &&
        data_bound == data_bound@pre &&
        data_x == data_x@pre && key_x == key_x@pre &&
        idx == idx &&
        partial_map_update_or_add_size(
          M_before, n, n_after, data_x@pre, key_x@pre
        ) &&
        store(size, int, n_after) *
        store_heap(
          key, data, pos, data_bound@pre, capacity,
          partial_map_update_or_add(M_before, data_x@pre, key_x@pre), n_after
        )
   */
}

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
{
  /*@ Assert
      exists key_values data_values pos_values,
        key == key@pre && data == data@pre &&
        pos == pos@pre && size == size@pre &&
        data_bound == data_bound@pre &&
        data_out == data_out@pre && key_out == key_out@pre &&
        1 <= n && n <= capacity && capacity <= heap_capacity &&
        heap_representation(
          M_before, key_values, data_values, pos_values,
          data_bound@pre, n
        ) &&
        store(size, int, n) *
        IntArray::full(key, n, key_values) *
        IntArray::undef_seg(key, n, capacity) *
        IntArray::full(data, n, data_values) *
        IntArray::undef_seg(data, n, capacity) *
        IntArray::full(pos, data_bound@pre, pos_values) *
        has_int_permission(data_out) *
        has_int_permission(key_out)
   */
  int n0 = *size;
  int result_key = key[0];
  int result_data = data[0];
  *key_out = result_key;
  *data_out = result_data;
  /*@ Assert
      exists key_values data_values pos_values,
        key == key@pre && data == data@pre &&
        pos == pos@pre && size == size@pre &&
        data_bound == data_bound@pre &&
        data_out == data_out@pre && key_out == key_out@pre &&
        n0 == n &&
        result_key == key_values[0] &&
        result_data == data_values[0] &&
        1 <= n && n <= capacity && capacity <= heap_capacity &&
        0 <= result_data && result_data < data_bound@pre &&
        heap_representation(
          M_before, key_values, data_values, pos_values,
          data_bound@pre, n
        ) &&
        store(size, int, n) *
        IntArray::full(key, n, key_values) *
        IntArray::undef_seg(key, n, capacity) *
        IntArray::full(data, n, data_values) *
        IntArray::undef_seg(data, n, capacity) *
        IntArray::full(pos, data_bound@pre, pos_values) *
        store(data_out, int, result_data) *
        store(key_out, int, result_key)
   */
  pos[result_data] = -1;

  if (n0 == 1) {
    *size = 0;
    /*@ Assert
        exists popped,
          key == key@pre && data == data@pre &&
          pos == pos@pre && size == size@pre &&
          data_bound == data_bound@pre &&
          data_out == data_out@pre && key_out == key_out@pre &&
          n0 == n && n == 1 &&
          result_key == item_key(popped) &&
          result_data == item_data(popped) &&
          partial_map_minimum(M_before, popped) &&
          store(size, int, 0) *
          store_heap(
            key, data, pos, data_bound@pre, capacity,
            partial_map_remove(M_before, item_data(popped)), 0
          ) *
          store(data_out, int, result_data) *
          store(key_out, int, result_key)
     */
    return;
  }
  /*@ Assert
      exists popped key_values data_values pos_values,
        key == key@pre && data == data@pre &&
        pos == pos@pre && size == size@pre &&
        data_bound == data_bound@pre &&
        data_out == data_out@pre && key_out == key_out@pre &&
        n0 == n && 1 < n &&
        1 <= n && n <= capacity && capacity <= heap_capacity &&
        result_key == item_key(popped) &&
        result_data == item_data(popped) &&
        0 <= n - 1 && n - 1 < n &&
        0 <= data_values[n - 1] &&
        data_values[n - 1] < data_bound@pre &&
        PopMarkedState(
          M_before, key_values, data_values, pos_values,
          data_bound@pre, n, popped
        ) &&
        store(size, int, n) *
        IntArray::full(key, n, key_values) *
        IntArray::undef_seg(key, n, capacity) *
        IntArray::full(data, n, data_values) *
        IntArray::undef_seg(data, n, capacity) *
        IntArray::full(pos, data_bound@pre, pos_values) *
        store(data_out, int, result_data) *
        store(key_out, int, result_key)
   */

  pos[data[n0 - 1]] = 0;
  key[0] = key[n0 - 1];
  data[0] = data[n0 - 1];
  /*@ Assert
      exists popped key_values data_values pos_values,
        key == key@pre && data == data@pre &&
        pos == pos@pre && size == size@pre &&
        data_bound == data_bound@pre &&
        data_out == data_out@pre && key_out == key_out@pre &&
        n0 == n && 1 < n &&
        0 < n - 1 && n - 1 <= capacity &&
        capacity <= heap_capacity &&
        result_key == item_key(popped) &&
        result_data == item_data(popped) &&
        partial_map_minimum(M_before, popped) &&
        0 <= data_values[0] && data_values[0] < data_bound@pre &&
        SiftDownState(
          partial_map_remove(M_before, item_data(popped)),
          key_values, data_values, pos_values,
          data_bound@pre, n - 1, 0
        ) &&
        store(size, int, n) *
        IntArray::full(key, n - 1, key_values) *
        IntArray::undef_seg(key, n - 1, capacity) *
        IntArray::full(data, n - 1, data_values) *
        IntArray::undef_seg(data, n - 1, capacity) *
        IntArray::full(pos, data_bound@pre, pos_values) *
          store(data_out, int, result_data) *
          store(key_out, int, result_key)
   */
  *size = n0 - 1;
  /*@ Assert
      exists popped key_values data_values pos_values,
        key == key@pre && data == data@pre &&
        pos == pos@pre && size == size@pre &&
        data_bound == data_bound@pre &&
        data_out == data_out@pre && key_out == key_out@pre &&
        n0 == n && 1 < n &&
        0 < n - 1 && n - 1 <= capacity &&
        capacity <= heap_capacity &&
        result_key == item_key(popped) &&
        result_data == item_data(popped) &&
        partial_map_minimum(M_before, popped) &&
        0 <= data_values[0] && data_values[0] < data_bound@pre &&
        SiftDownState(
          partial_map_remove(M_before, item_data(popped)),
          key_values, data_values, pos_values,
          data_bound@pre, n - 1, 0
        ) &&
        store(size, int, n - 1) *
        IntArray::full(key, n - 1, key_values) *
        IntArray::undef_seg(key, n - 1, capacity) *
        IntArray::full(data, n - 1, data_values) *
        IntArray::undef_seg(data, n - 1, capacity) *
        IntArray::full(pos, data_bound@pre, pos_values) *
        store(data_out, int, result_data) *
        store(key_out, int, result_key)
   */
  /*@ Assert
      exists popped,
        key == key@pre && data == data@pre &&
        pos == pos@pre && size == size@pre &&
        data_bound == data_bound@pre &&
        data_out == data_out@pre && key_out == key_out@pre &&
        n0 == n && 1 < n &&
        0 < n - 1 && n - 1 <= capacity &&
        capacity <= heap_capacity &&
        result_key == item_key(popped) &&
        result_data == item_data(popped) &&
        partial_map_minimum(M_before, popped) &&
        store(size, int, n - 1) *
        store_sift_down(
          key, data, pos, data_bound@pre, capacity,
          partial_map_remove(M_before, item_data(popped)), n - 1, 0
        ) *
        store(data_out, int, result_data) *
        store(key_out, int, result_key)
   */
  pqdk_sift_down(key, data, pos, data_bound, n0 - 1, 0);
}
