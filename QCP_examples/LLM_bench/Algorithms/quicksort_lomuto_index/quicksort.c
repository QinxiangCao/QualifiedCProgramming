



/*@ Extern Coq (Permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (increasing : list Z -> Prop) */
/*@ Extern Coq (range_nondecreasing : list Z -> Z -> Z -> Prop) */
/*@ Extern Coq (same_outside_range : list Z -> list Z -> Z -> Z -> Prop) */
/*@ Extern Coq (partitioned_at : list Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib */

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
              Permutation(l, l1) &&
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
        pivot == l[high] &&
        0 <= low && low <= high && high < n &&
        low - 1 <= i && i < j && j <= high &&
        Permutation(l, l1) &&
        same_outside_range(l, l1, low, high) &&
        l1[high] == pivot &&
        (forall (k: Z), (low <= k && k <= i) => (l1[k] <= pivot)) &&
        (forall (k: Z), (i < k && k < j) => (pivot < l1[k])) &&
        IntArray::full(arr, n, l1)
      by array_length
  */
  for (int j = low; j < high; j++) {
    if (arr[j] <= pivot) {
      i++;
      swap(arr, i, j);
    }
  }

  swap(arr, i + 1, high);
  return i + 1 /*@ by array_length */;
}

void quicksort_range(int *arr, int n, int left, int right)
/*@ With l
    Require 0 <= n && 0 <= left && -1 <= right && right < n &&
            IntArray::full(arr, n, l)
    Ensure exists l1,
            Permutation(l, l1) &&
            same_outside_range(l, l1, left, right) &&
            range_nondecreasing(l1, left, right) &&
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
  return /*@ by array_length */;
}

void quicksort(int *arr, int n)
/*@ With l
    Require 1 <= n && n <= 50000 &&
            IntArray::full(arr, n, l)
    Ensure exists l1,
            Permutation(l, l1) &&
            increasing(l1) &&
            IntArray::full(arr, n, l1)
*/
{
  quicksort_range(arr, n, 0, n - 1);
  return /*@ by array_length */;
}
