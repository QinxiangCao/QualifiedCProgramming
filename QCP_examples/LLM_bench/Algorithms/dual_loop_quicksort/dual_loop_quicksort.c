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
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.dual_loop_quicksort.dual_loop_quicksort_lib */

void swap(int *arr, int i, int j)
/*@ With (n0 : Z) (l : list Z)
    Require 0 <= i && i < n0 && 0 <= j && j < n0 &&
            IntArray::full(arr, n0, l)
    Ensure IntArray::full(arr, n0,
             replace_Znth(j, Znth(i, l, 0), replace_Znth(i, Znth(j, l, 0), l)))
*/
{
  int tmp = arr[i];
  arr[i] = arr[j];
  arr[j] = tmp;
}

int partition_two_loop(int *arr, int n, int low, int high)
/*@ With (l : list Z)
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
        arr == arr@pre && n == n@pre &&
        low == low@pre && high == high@pre &&
        pivot == Znth(low, l, 0) &&
        Zlength(l) == n && 1 <= n && n <= 50000 &&
        0 <= low && low <= high && high < n &&
        low <= i && i <= j && j <= high &&
        partition_outer_inv(l, l1, low, high, pivot, i, j) &&
        IntArray::full(arr, n, l1)
  */
  while (i < j) {
    /*@ Inv Assert
        exists l1,
          arr == arr@pre && n == n@pre &&
          low == low@pre && high == high@pre &&
          pivot == Znth(low, l, 0) &&
          Zlength(l) == n && 1 <= n && n <= 50000 &&
          0 <= low && low <= high && high < n &&
          low <= i && i <= j && j <= high &&
          partition_right_scan_inv(l, l1, low, high, pivot, i, j) &&
          IntArray::full(arr, n, l1)
    */
    while (i < j && arr[j] >= pivot) {
      j--;
    }
    /*@ Inv Assert
        exists l1,
          arr == arr@pre && n == n@pre &&
          low == low@pre && high == high@pre &&
          pivot == Znth(low, l, 0) &&
          Zlength(l) == n && 1 <= n && n <= 50000 &&
          0 <= low && low <= high && high < n &&
          low <= i && i <= j && j <= high &&
          partition_left_scan_inv(l, l1, low, high, pivot, i, j) &&
          IntArray::full(arr, n, l1)
    */
    while (i < j && arr[i] <= pivot) {
      i++;
    }
    if (i < j) {
      swap(arr, i, j);
    }
  }

  swap(arr, low, i);
  return i;
}

void quicksort_range(int *arr, int n, int left, int right)
/*@ With (l : list Z)
    Require Zlength(l) == n && 0 <= n && n <= 50000 &&
            0 <= left && left <= right + 1 && right < n &&
            IntArray::full(arr, n, l)
    Ensure exists l1,
            Permutation(l, l1) &&
            same_outside_range(l, l1, left, right) &&
            range_nondecreasing(l1, left, right) &&
            IntArray::full(arr, n, l1)
*/
{
  if (left < right) {
    int p = partition_two_loop(arr, n, left, right);
    if (p > left) {
      quicksort_range(arr, n, left, p - 1);
    }
    if (p < right) {
      quicksort_range(arr, n, p + 1, right);
    }
  }
}

void dual_loop_quicksort(int *arr, int n)
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
    quicksort_range(arr, n, 0, n - 1);
  }
}
