/*@ Extern Coq (Permutation : list Z -> list Z -> Prop) */
/*@ Extern Coq (increasing : list Z -> Prop) */
/*@ Extern Coq (upperbound : Z -> list Z -> Prop) */
/*@ Extern Coq (lowerbound : Z -> list Z -> Prop) */
/*@ Extern Coq (prefix_suffix_sorted : list Z -> list Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_LLM.bubble_sort_lib */

void bubble_sort(int *arr, int n)
/*@ With (l: list Z)
    Require
      n >= 0 && n <= 100000 &&
      Zlength(l) == n &&
      IntArray::full(arr, n, l)
    Ensure
      exists l1,
        Permutation(l, l1) &&
        increasing(l1) &&
        Zlength(l1) == n &&
        IntArray::full(arr, n, l1)
 */
{
  int i;
  int j;

  /*@ Inv Assert
      (arr == arr@pre &&
       n == n@pre &&
       n == 0 &&
       i == 0 &&
       Zlength(l) == n &&
       IntArray::full(arr, n, l) *
       has_int_permission(&j))
      ||
      (exists a,
        arr == arr@pre &&
        n == n@pre &&
        1 <= n &&
        Zlength(a) == n &&
        0 <= i && i <= n - 1 &&
        Permutation(l, a) &&
        increasing(sublist(n - i, n, a)) &&
        (forall (p: Z) (q: Z),
          (0 <= p && p < n - i && n - i <= q && q < n) =>
          (Znth(p, a, 0) <= Znth(q, a, 0))) &&
        IntArray::full(arr, n, a) *
        has_int_permission(&j))
  */
  for (i = 0; i < n - 1; i++) {
    /*@ Inv Assert
        exists a,
          arr == arr@pre &&
          n == n@pre &&
          Zlength(a) == n &&
          0 <= i && i < n - 1 &&
          0 <= j && j <= n - 1 - i &&
          Permutation(l, a) &&
          increasing(sublist(n - i, n, a)) &&
          (forall (p: Z) (q: Z),
            (0 <= p && p < n - i && n - i <= q && q < n) =>
            (Znth(p, a, 0) <= Znth(q, a, 0))) &&
          (forall (p: Z),
            (0 <= p && p < j) =>
            (Znth(p, a, 0) <= Znth(j, a, 0))) &&
          IntArray::full(arr, n, a)
    */
    for (j = 0; j < n - 1 - i; j++) {
      if (arr[j] > arr[j + 1]) {
        int tmp = arr[j];
        arr[j] = arr[j + 1];
        arr[j + 1] = tmp;
      }
    }
  }
}

void bubble_sort_alter(int *arr, int n)
/*@ With (l: list Z)
    Require
      n >= 0 && n <= 100000 &&
      Zlength(l) == n &&
      IntArray::full(arr, n, l)
    Ensure
      exists l1,
        Permutation(l, l1) &&
        increasing(l1) &&
        Zlength(l1) == n &&
        IntArray::full(arr, n, l1)
 */
{
  int i;
  int j;

  /*@ Destruct $ all with
      zero: n == 0;
      normal: n > 0
  */

  /*@ Inv
      zero:
        arr == arr@pre &&
        n == n@pre &&
        n == 0 &&
        i == 0 &&
        Zlength(l) == n &&
        IntArray::full(arr, n, l) *
        has_int_permission(&j);
      normal:
        exists a,
          arr == arr@pre &&
          n == n@pre &&
          1 <= n &&
          Zlength(a) == n &&
          0 <= i && i <= n - 1 &&
          Permutation(l, a) &&
          increasing(sublist(n - i, n, a)) &&
          (forall (p: Z) (q: Z),
            (0 <= p && p < n - i && n - i <= q && q < n) =>
            (Znth(p, a, 0) <= Znth(q, a, 0))) &&
          IntArray::full(arr, n, a) *
          has_int_permission(&j)
      with
      zero ==> zero
      normal ==> normal
  */
  for (i = 0; i < n - 1; i++) {
    /*@ Inv
        normal:
          exists a,
            arr == arr@pre &&
            n == n@pre &&
            Zlength(a) == n &&
            0 <= i && i < n - 1 &&
            0 <= j && j <= n - 1 - i &&
            Permutation(l, a) &&
            increasing(sublist(n - i, n, a)) &&
            (forall (p: Z) (q: Z),
              (0 <= p && p < n - i && n - i <= q && q < n) =>
              (Znth(p, a, 0) <= Znth(q, a, 0))) &&
            (forall (p: Z),
              (0 <= p && p < j) =>
              (Znth(p, a, 0) <= Znth(j, a, 0))) &&
            IntArray::full(arr, n, a)
        with
        normal ==> normal
    */
    for (j = 0; j < n - 1 - i; j++) {
      if (arr[j] > arr[j + 1]) {
        int tmp = arr[j];
        arr[j] = arr[j + 1];
        arr[j + 1] = tmp;
      }
    }
  }
}

void bubble_sort_alter1(int *arr, int n)
/*@ With (l: list Z)
    Require
      n >= 0 && n <= 100000 &&
      Zlength(l) == n &&
      IntArray::full(arr, n, l)
    Ensure
      exists l1,
        Permutation(l, l1) &&
        increasing(l1) &&
        Zlength(l1) == n &&
        IntArray::full(arr, n, l1)
 */
{
  int i;
  int j;

  /*@ Destruct $ all with
      zero: n == 0;
      normal: n > 0
  */

  /*@ Inv
      zero:
        arr == arr@pre &&
        n == n@pre &&
        n == 0 &&
        i == 0 &&
        Zlength(l) == n &&
        IntArray::full(arr, n, l) *
        has_int_permission(&j);
      normal:
        exists a,
          arr == arr@pre &&
          n == n@pre &&
          1 <= n &&
          Zlength(a) == n &&
          0 <= i && i <= n - 1 &&
          Permutation(l, a) &&
          increasing(sublist(n - i, n, a)) &&
          (forall (p: Z) (q: Z),
            (0 <= p && p < n - i && n - i <= q && q < n) =>
            (Znth(p, a, 0) <= Znth(q, a, 0))) &&
          IntArray::full(arr, n, a) *
          has_int_permission(&j)
  */
  for (i = 0; i < n - 1; i++) {
    /*@ Inv
        exists a,
          arr == arr@pre &&
          n == n@pre &&
          Zlength(a) == n &&
          0 <= i && i < n - 1 &&
          0 <= j && j <= n - 1 - i &&
          Permutation(l, a) &&
          increasing(sublist(n - i, n, a)) &&
          (forall (p: Z) (q: Z),
            (0 <= p && p < n - i && n - i <= q && q < n) =>
            (Znth(p, a, 0) <= Znth(q, a, 0))) &&
          (forall (p: Z),
            (0 <= p && p < j) =>
            (Znth(p, a, 0) <= Znth(j, a, 0))) &&
          IntArray::full(arr, n, a)
    */
    for (j = 0; j < n - 1 - i; j++) {
      if (arr[j] > arr[j + 1]) {
        int tmp = arr[j];
        arr[j] = arr[j + 1];
        arr[j + 1] = tmp;
      }
    }
  }
}
