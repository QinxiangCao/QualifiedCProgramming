/*@ Extern Coq (sum : list Z -> Z) */



int arr_sum(int n, int *a)
/*@ With l
    Require 0 < n && n < 100 && IntArray::full(a, n, l) && (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100))
    Ensure  __return == sum(l) && IntArray::full(a, n, l) 
*/
{
  int i;
  i = 0;
  int ret;
  ret = 0;
    /*@ Inv Assert
      0 < n@pre && n@pre < 100 && a == a@pre && n == n@pre &&
      0 <= i && i <= n &&
      (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100)) &&
      ret == sum(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
    */
  while (i < n) {
    ret += a[i];
    ++i;
  }
  return ret;
}

int arr_sum_do_while(int n, int *a)
/*@ With l
    Require 0 < n && n < 100 && IntArray::full(a, n, l) && (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100))
    Ensure  __return == sum(l) && IntArray::full(a, n, l)
*/
{
  int i = 0;
  int ret = 0;
  do {
    ret += a[i];
    ++i;
    } /*@ Inv Assert
        0 < n@pre && n@pre < 100 && a == a@pre && n == n@pre &&
        0 <= i && i <= n &&
        (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100)) &&
        ret == sum(sublist(0, i, l)) &&
        IntArray::full(a, n, l)
      */ while (i != n);
  return ret;
}

int arr_sum_for(int n, int *a)
/*@ With l
    Require 0 < n && n < 100 && IntArray::full(a, n, l) && (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100))
    Ensure  __return == sum(l) && IntArray::full(a, n, l)
*/
{
  int i;
  int ret = 0;
    /*@ Inv Assert
      0 < n@pre && n@pre < 100 && a == a@pre && n == n@pre &&
      0 <= i && i <= n &&
      (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100)) &&
      ret == sum(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
    */
  for (i = 0; i < n; ++i) {
    ret += a[i];
  }
  return ret;
}

int arr_sum_which_implies(int n, int *a)
/*@ With l
    Require 0 < n && n < 100 && (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100)) && IntArray::full(a, n, l)
    Ensure  __return == sum(l) && IntArray::full(a, n, l)
*/
{
  int i;
  int ret = 0;
    /*@ Inv Assert
      0 < n@pre && n@pre < 100 && a == a@pre && n == n@pre &&
      0 <= i && i <= n@pre &&
      (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100)) &&
      ret == sum(sublist(0, i, l)) &&
      IntArray::full(a, n@pre, l)
    */
  for (i = 0; i < n; ++i) {
    ret += a[i];
  }
  return ret;
}

int arr_sum_update(int n, int *a)
/*@ With l
    Require 0 < n && n < 100 && (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100)) && IntArray::full(a, n, l)
    Ensure  exists l1, __return == sum(l) && n == Zlength(l1) &&
            (forall (i: Z), (0 <= i && i < n) => l1[i] == 0) &&
            IntArray::full(a, n, l1)
*/
{
  int i;
  int ret = 0;
  /*@ Inv Assert
      exists l1, 
      0 < n@pre && n@pre < 100 && a == a@pre && n == n@pre &&
      0 <= i && i <= n@pre && n == Zlength(l) && n == Zlength(l1) && 
      (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100)) &&
      (forall (k: Z), (0 <= k && k < i) => l1[k] == 0) &&
      (forall (k: Z), (i <= k && k < n) => l1[k] == l[k]) &&
      ret == sum(sublist(0, i, l)) &&
      IntArray::full(a, n@pre, l1)
  */
  for (i = 0; i < n; ++i) {
    ret += a[i];
    a[i] = 0;
  }
  return ret;
}


int arr_sum_pointer(int n, int *a)
/*@ With l
    Require 0 < n && n < 100 && IntArray::full(a, n, l) && (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100))
    Ensure  __return == sum(l) && IntArray::full(a, n, l)
*/
{
  int i = 0;
  int ret = 0;
  int *endp = a + n;
  /*@ Inv Assert
      0 < n@pre && n@pre < 100 && a == a@pre && n == n@pre &&
      0 <= i && i <= n@pre &&
      (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100)) &&
      n@pre == Zlength(l) && endp == a + n * sizeof(int) &&
      ret == sum(sublist(0, i, l)) && IntArray::full(a, n@pre, l) */
  while (endp - (a + i) != 0) {
    /*@ Assert
      0 < n@pre && n@pre < 100 && a == a@pre && n == n@pre &&
      0 <= i && i < n@pre && endp != a + i * sizeof(int) &&
      (forall (i: Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100)) &&
      n@pre == Zlength(l) && endp == a + n * sizeof(int) &&
      ret == sum(sublist(0, i, l)) && IntArray::full(a, n@pre, l) */
    ret += *(a + i);
    ++i;
  }
  return ret;
}
