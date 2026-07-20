#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (increasing : list Z -> Prop) */
/*@ Extern Coq (sorted_range : list Z -> Z -> Z -> Prop) */
/*@ Extern Coq (same_outside_range : list Z -> list Z -> Z -> Z -> Prop) */
/*@ Extern Coq (partitioned_at : list Z -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (partition_scan_inv : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.quicksort_lomuto_index.quicksort_lib */

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

void quicksort(int *arr, int n)
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
