



/*@ Extern Coq (permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (increasing : list Z -> Prop) */
/*@ Extern Coq (same_outside_range : list Z -> list Z -> Z -> Z -> Prop) */
/*@ Extern Coq (partitioned_at : list Z -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (sorted_range : list Z -> Z -> Z -> Prop) */
/*@ Extern Coq (partition_scan_inv : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (strict_increasing : list Z -> Prop) */
/*@ Extern Coq (dedup_scan_inv : list Z -> list Z -> list Z -> Z -> Z -> Prop) */
/*@ Extern Coq (discretize_result : list Z -> Z -> list Z -> Z -> Prop) */
/*@ Extern Coq (query_forward_result : list Z -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (query_forward_search_inv : list Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_lib */

void swap(int *arr, int i, int j)
/*@ With n l
    Require 0 <= i && i < n && 0 <= j && j < n &&
            IntArray::full(arr, n, l)
    Ensure IntArray::full(arr, n,
             replace_Znth(j, Znth(i, l, 0), replace_Znth(i, Znth(j, l, 0), l)))
*/
{
    int tmp = arr[i];
    arr[i] = arr[j];
    arr[j] = tmp;
}

int partition(int *arr, int n, int low, int high)
/*@ With l
    Require 0 <= low && low <= high && high < n &&
            IntArray::full(arr, n, l)
    Ensure low <= __return && __return <= high &&
            exists l1,
              permutation(l, l1) &&
              same_outside_range(l, l1, low, high) &&
              partitioned_at(l1, low, high, __return) &&
              IntArray::full(arr, n, l1)
*/
{
    int pivot = arr[high];
    int i = low - 1;
    /*@ Inv Assert
        exists l1,
          arr == arr@pre && n == n@pre &&
          low == low@pre && high == high@pre &&
          pivot == Znth(high, l, 0) &&
          0 <= low && low <= high && high < n &&
          low - 1 <= i && i < j && j <= high &&
          partition_scan_inv(l, l1, low, high, pivot, i, j) &&
          IntArray::full(arr, n, l1)
    */
    for (int j = low; j < high; j++) {
        if (arr[j] <= pivot) {
            i++;
            swap(arr, i, j);
        }
    }
    swap(arr, i + 1, high);
    return i + 1;
}

void quicksort_range(int *arr, int n, int left, int right)
/*@ With l
    Require 0 <= n && 0 <= left && -1 <= right && right < n &&
            IntArray::full(arr, n, l)
    Ensure exists l1,
            permutation(l, l1) &&
            same_outside_range(l, l1, left, right) &&
            sorted_range(l1, left, right) &&
            IntArray::full(arr, n, l1)
*/
{
    if (left < right) {
        int p = partition(arr, n, left, right);
        if (p > left) {
            quicksort_range(arr, n, left, p - 1);
        }
        if (p < right) {
            quicksort_range(arr, n, p + 1, right);
        }
    }
}

void int_array_quicksort(int *arr, int n)
/*@ With l
    Require 1 <= n && n <= 50000 &&
            IntArray::full(arr, n, l)
    Ensure exists l1,
            permutation(l, l1) &&
            increasing(l1) &&
            IntArray::full(arr, n, l1)
*/
{
    quicksort_range(arr, n, 0, n - 1);
}

int discretize(const int *src, int n, int *dest_map) 
/*@ With src_l
    Require Zlength(src_l) == n &&
            1 <= n && n <= 50000 &&
            IntArray::full(src, n, src_l) *
            IntArray::undef_full(dest_map, n)
    Ensure exists out_l,
            discretize_result(src_l, n, out_l, __return) &&
            IntArray::full(src, n, src_l) *
            IntArray::full(dest_map, n, out_l)
*/
{
    /*@ Inv Assert
        Zlength(src_l) == n@pre &&
        1 <= n@pre && n@pre <= 50000 &&
        0 <= i && i <= n@pre &&
        src == src@pre && dest_map == dest_map@pre && n == n@pre &&
        IntArray::full(src@pre, n@pre, src_l) *
        IntArray::full(dest_map@pre, i, sublist(0, i, src_l)) *
        IntArray::undef_seg(dest_map@pre, i, n@pre)
    */
    for (int i = 0; i < n; i++) {
        dest_map[i] = src[i];
    }
    /*@ Assert
        Zlength(src_l) == n@pre &&
        1 <= n@pre && n@pre <= 50000 &&
        src == src@pre && dest_map == dest_map@pre && n == n@pre &&
        IntArray::full(src@pre, n@pre, src_l) *
        IntArray::full(dest_map@pre, n@pre, src_l)
    */
    int_array_quicksort(dest_map, n);
    int slow = 0;
    /*@ Inv Assert
        exists sorted_l cur_l,
          Zlength(src_l) == n@pre &&
          1 <= n@pre && n@pre <= 50000 &&
          src == src@pre && dest_map == dest_map@pre && n == n@pre &&
          0 <= slow && slow < fast && 1 <= fast && fast <= n@pre &&
          dedup_scan_inv(src_l, sorted_l, cur_l, slow, fast) &&
          IntArray::full(src@pre, n@pre, src_l) *
          IntArray::full(dest_map@pre, n@pre, cur_l)
    */
    for (int fast = 1; fast < n; fast++) {
        if (dest_map[fast] != dest_map[slow]) {
            slow++;
            dest_map[slow] = dest_map[fast];
        }
    }
    /*@ Assert
        exists out_l,
          Zlength(src_l) == n@pre &&
          1 <= n@pre && n@pre <= 50000 &&
          src == src@pre && dest_map == dest_map@pre && n == n@pre &&
          discretize_result(src_l, n@pre, out_l, slow + 1) &&
          IntArray::full(src@pre, n@pre, src_l) *
          IntArray::full(dest_map@pre, n@pre, out_l)
    */
    return slow + 1;
}

int query_forward(const int *map, int map_size, int target) 
/*@ With map_l
    Require Zlength(map_l) == map_size &&
            0 <= map_size && map_size <= 50000 &&
            strict_increasing(map_l) &&
            IntArray::full(map, map_size, map_l)
    Ensure query_forward_result(map_l, map_size, target, __return) &&
           IntArray::full(map, map_size, map_l)
*/
{
    int low = 0;
    int high = map_size - 1;
    
    /*@ Inv Assert
        Zlength(map_l) == map_size@pre &&
        0 <= map_size@pre && map_size@pre <= 50000 &&
        strict_increasing(map_l) &&
        map == map@pre && map_size == map_size@pre && target == target@pre &&
        0 <= low && low <= high + 1 && high < map_size@pre &&
        query_forward_search_inv(map_l, map_size@pre, target@pre, low, high) &&
        IntArray::full(map@pre, map_size@pre, map_l)
    */
    while (low <= high) {
        int mid = low + (high - low) / 2;
        /*@ Assert
            Zlength(map_l) == map_size@pre &&
            0 <= map_size@pre && map_size@pre <= 50000 &&
            strict_increasing(map_l) &&
            map == map@pre && map_size == map_size@pre && target == target@pre &&
            0 <= low && low <= mid && mid <= high && high < map_size@pre &&
            query_forward_search_inv(map_l, map_size@pre, target@pre, low, high) &&
            IntArray::full(map@pre, map_size@pre, map_l)
        */
        if (map[mid] == target) {
            return mid;
        } else if (map[mid] < target) {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    /*@ Assert
        Zlength(map_l) == map_size@pre &&
        0 <= map_size@pre && map_size@pre <= 50000 &&
        strict_increasing(map_l) &&
        map == map@pre && map_size == map_size@pre && target == target@pre &&
        0 <= low && low <= high + 1 && high < map_size@pre &&
        query_forward_search_inv(map_l, map_size@pre, target@pre, low, high) &&
        query_forward_result(map_l, map_size@pre, target@pre, -1) &&
        IntArray::full(map@pre, map_size@pre, map_l)
    */
    return -1; 
}
