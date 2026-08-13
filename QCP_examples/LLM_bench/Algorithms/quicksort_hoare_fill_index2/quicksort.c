



/*@ Extern Coq (Permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (increasing : list Z -> Prop) */
/*@ Extern Coq (same_outside_range : list Z -> list Z -> Z -> Z -> Prop) */
/*@ Extern Coq (partitioned_at : list Z -> Z -> Z -> Z -> Prop) */
/*@ Extern Coq (range_nondecreasing : list Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib */

int partition(int *arr, int low, int high)
/*@ With (l : list Z) (n : Z)
    Require 1 <= n && n <= 50000 &&
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
        pivot == l[low] &&
        1 <= n && n <= 50000 &&
        0 <= low && low <= high && high < n &&
        low <= i && i <= j && j <= high &&
        Permutation(l, replace_Znth(i, pivot, l1)) &&
        same_outside_range(l, l1, low, high) &&
        (forall (k: Z), (low <= k && k < i) => (l1[k] <= pivot)) &&
        (forall (k: Z), (j < k && k <= high) => (pivot <= l1[k])) &&
        IntArray::full(arr, n, l1)
      by array_length
  */
  while (1) {
    /*@ Inv Assert
        exists l1,
          arr == arr@pre &&
          low == low@pre && high == high@pre &&
          pivot == l[low] &&
          1 <= n && n <= 50000 &&
          0 <= low && low <= high && high < n &&
          low <= i && i <= j && j <= high &&
          Permutation(l, replace_Znth(i, pivot, l1)) &&
          same_outside_range(l, l1, low, high) &&
          (forall (k: Z), (low <= k && k < i) => (l1[k] <= pivot)) &&
          (forall (k: Z), (j < k && k <= high) => (pivot <= l1[k])) &&
          IntArray::full(arr, n, l1)
        by array_length
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
          pivot == l[low] &&
          1 <= n && n <= 50000 &&
          0 <= low && low <= high && high < n &&
          low <= i && i <= j && j <= high &&
          Permutation(l, replace_Znth(j, pivot, l1)) &&
          same_outside_range(l, l1, low, high) &&
          (forall (k: Z), (low <= k && k < i) => (l1[k] <= pivot)) &&
          (forall (k: Z), (j < k && k <= high) => (pivot <= l1[k])) &&
          IntArray::full(arr, n, l1)
        by array_length
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
  return i /*@ by array_length */;
}

void quicksort_range(int *arr, int left, int right)
/*@ With (l : list Z) (n : Z)
    Require 0 <= n && n <= 50000 &&
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
  if (p > left + 1) {
    quicksort_range(arr, left, p - 1) /*@ where n = n */;
  }
  if (p < right - 1) {
    quicksort_range(arr, p + 1, right) /*@ where n = n */;
  }
  return /*@ by array_length */;
}

void quicksort(int *arr, int n)
/*@ With (l : list Z)
    Require 0 <= n && n <= 50000 &&
            IntArray::full(arr, n, l)
    Ensure exists l1,
            Permutation(l, l1) &&
            increasing(l1) &&
            IntArray::full(arr, n, l1)
*/
{
  if (n > 0) {
    quicksort_range(arr, 0, n - 1) /*@ where n = n */;
  }
  return /*@ by array_length */;
}
