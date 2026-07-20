#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (Permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (increasing : list Z -> Prop) */
/*@ Extern Coq (same_outside_range : list Z -> list Z -> Z -> Z -> Prop) */
/*@ Extern Coq (partitioned_at : list Z -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (range_nondecreasing : list Z -> Z -> Z -> Prop) */
/*@ Extern Coq (partition_outer_inv : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (partition_right_scan_inv : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (partition_left_scan_inv : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (partition_hole_outer_inv : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (partition_hole_left_scan_inv : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib */

int partition(int *arr, int low, int high)
/*@ With (l : list Z) (n : Z)
    Require Zlength(l) == n && 1 <= n && n <= 50000 &&
            0 <= low && low <= high && high < n &&
            IntArray::full(arr, n, l)
    Ensure low <= __return && __return <= high &&
            exists l1,
              Permutation(l, l1) &&
              same_outside_range(l, l1, low, high) &&
              partitioned_at(l1, low, high, __return) &&
              IntArray::full(arr, n, l1)
*/
{
  int pivot = arr[low];
  int i = low;
  int j = high;

  /*@ Inv Assert
      exists l1,
        arr == arr@pre &&
        low == low@pre && high == high@pre &&
        pivot == Znth(low, l, 0) &&
        Zlength(l) == n && 1 <= n && n <= 50000 &&
        0 <= low && low <= high && high < n &&
        low <= i && i <= j && j <= high &&
        partition_hole_outer_inv(l, l1, low, high, pivot, i, j) &&
        IntArray::full(arr, n, l1)
  */
  while (1) {
    /*@ Inv Assert
        exists l1,
          arr == arr@pre &&
          low == low@pre && high == high@pre &&
          pivot == Znth(low, l, 0) &&
          Zlength(l) == n && 1 <= n && n <= 50000 &&
          0 <= low && low <= high && high < n &&
          low <= i && i <= j && j <= high &&
          partition_hole_outer_inv(l, l1, low, high, pivot, i, j) &&
          IntArray::full(arr, n, l1)
    */
    while (i < j && arr[j] > pivot) {
      j--;
    }
    if (i < j) {
      arr[i] = arr[j];
      i++;
    }
    else {
      break;
    }
    /*@ Inv Assert
        exists l1,
          arr == arr@pre &&
          low == low@pre && high == high@pre &&
          pivot == Znth(low, l, 0) &&
          Zlength(l) == n && 1 <= n && n <= 50000 &&
          0 <= low && low <= high && high < n &&
          low <= i && i <= j && j <= high &&
          partition_hole_left_scan_inv(l, l1, low, high, pivot, i, j) &&
          IntArray::full(arr, n, l1)
    */
    while (i < j && arr[i] <= pivot) {
      i++;
    }
    if (i < j) {
      arr[j] = arr[i];
      j--;
    }
    else {
      break;
    }
  }

  arr[i] = pivot;
  return i;
}

void quicksort_range(int *arr, int left, int right)
/*@ With (l : list Z) (n : Z)
    Require Zlength(l) == n && 0 <= n && n <= 50000 &&
            0 <= left && left <= right && right < n &&
            IntArray::full(arr, n, l)
    Ensure exists l1,
            Permutation(l, l1) &&
            same_outside_range(l, l1, left, right) &&
            range_nondecreasing(l1, left, right) &&
            IntArray::full(arr, n, l1)
*/
{
  int p = partition(arr, left, right) /*@ where n = n */;
  if (p > left) {
    quicksort_range(arr, left, p - 1) /*@ where n = n */;
  }
  if (p < right) {
    quicksort_range(arr, p + 1, right) /*@ where n = n */;
  }
}

void quicksort(int *arr, int n)
/*@ With (l : list Z)
    Require Zlength(l) == n && 0 <= n && n <= 50000 &&
            IntArray::full(arr, n, l)
    Ensure exists l1,
            Permutation(l, l1) &&
            increasing(l1) &&
            Zlength(l1) == n &&
            IntArray::full(arr, n, l1)
*/
{
  if (n > 0) {
    quicksort_range(arr, 0, n - 1) /*@ where n = n */;
  }
}
