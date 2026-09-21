/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (Power2 : Z -> Z)
      (RangeMaxValue : list Z -> Z -> Z -> Z -> Prop)
      (STBasePrefix : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (STBuiltBeforeLevel : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (STLevelPrefix : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (STBuilt : list Z -> list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_lib */

void build(int *arr, int n, int K, int *st)
/*@ With (l : list Z) (st0 : list Z)
    Require
      1 <= n && n <= 100000 && 1 <= K && K <= 30 &&
      n * K <= 1000000 && n < Power2(K) &&
      Forall(Z::le(-2147483648), l) && Forall(Z::ge(2147483647), l) &&
      IntArray::full(arr, n, l) * IntArray::full(st, n * K, st0)
    Ensure
      exists st_l,
      STBuilt(l, st_l, K, n) &&
      IntArray::full(arr, n, l) * IntArray::full(st, n * K, st_l)
 */
{
  /*@ Inv Assert
      exists st_l,
      arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
      1 <= n && n <= 100000 && 1 <= K && K <= 30 && n * K <= 1000000 &&
      0 <= idx && idx <= n * K &&
      IntArray::full(arr, n, l) * IntArray::full(st, n * K, st_l)
   */
  for (int idx = 0; idx < n * K; ++idx) {
    st[idx] = 0;
  }

  /*@ Inv Assert
      exists st_l,
      arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
      1 <= n && n <= 100000 && 1 <= K && K <= 30 && n * K <= 1000000 &&
      0 <= i && i <= n && STBasePrefix(l, st_l, K, n, i) &&
      IntArray::full(arr, n, l) * IntArray::full(st, n * K, st_l)
   */
  for (int i = 0; i < n; ++i) {
    /*@ Assert
        exists st_l,
        arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
        1 <= n && n <= 100000 && 1 <= K && K <= 30 && n * K <= 1000000 &&
        0 <= i && i < n &&
        0 <= i * K && i * K < n * K && STBasePrefix(l, st_l, K, n, i) &&
        IntArray::full(arr, n, l) * IntArray::full(st, n * K, st_l)
     */
    st[i * K] = arr[i];
  }

  int half = 1;
  int len = 2;
  /*@ Inv Assert
      exists st_l,
      arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
      1 <= n && n <= 100000 && 1 <= K && K <= 30 && n * K <= 1000000 &&
      1 <= j && j <= K && half == Power2(j - 1) && len == Power2(j) &&
      STBuiltBeforeLevel(l, st_l, K, n, j) &&
      IntArray::full(arr, n, l) * IntArray::full(st, n * K, st_l)
   */
  for (int j = 1; j < K; ++j) {
    /*@ Inv Assert
        exists st_l,
        arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
        1 <= n && n <= 100000 && 1 <= K && K <= 30 && n * K <= 1000000 &&
        1 <= j && j < K && half == Power2(j - 1) && len == Power2(j) &&
        0 <= i && i <= n &&
        STBuiltBeforeLevel(l, st_l, K, n, j) &&
        STLevelPrefix(l, st_l, K, n, j, i) &&
        IntArray::full(arr, n, l) * IntArray::full(st, n * K, st_l)
     */
    for (int i = 0; i + len <= n; ++i) {
      /*@ Assert
          exists st_l,
          arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
          1 <= n && n <= 100000 && 1 <= K && K <= 30 && n * K <= 1000000 &&
          1 <= j && j < K && half == Power2(j - 1) && len == Power2(j) &&
          0 <= i && i + len <= n &&
          0 <= i * K + j - 1 && i * K + j - 1 < n * K &&
          0 <= (i + half) * K + j - 1 && (i + half) * K + j - 1 < n * K &&
          0 <= i * K + j && i * K + j < n * K &&
          STBuiltBeforeLevel(l, st_l, K, n, j) &&
          STLevelPrefix(l, st_l, K, n, j, i) &&
          IntArray::full(arr, n, l) * IntArray::full(st, n * K, st_l)
       */
      int a = st[i * K + j - 1];
      int b = st[(i + half) * K + j - 1];
      if (a >= b) {
        st[i * K + j] = a;
      } else {
        st[i * K + j] = b;
      }
    }
    half = len;
    len = len * 2;
  }
}

int query(int *st, int n, int K, int left, int right)
/*@ With (l : list Z) (st_l : list Z)
    Require
      1 <= n && n <= 100000 && 1 <= K && K <= 30 &&
      n * K <= 1000000 && n < Power2(K) &&
      0 <= left && left <= right && right < n &&
      Zlength(l) == n && STBuilt(l, st_l, K, n) &&
      IntArray::full(st, n * K, st_l)
    Ensure
      RangeMaxValue(l, left, right + 1, __return) &&
      IntArray::full(st, n * K, st_l)
 */
{
  int len = right - left + 1;
  int k = 0;
  int pow = 1;

  /*@ Inv Assert
      st == st@pre && n == n@pre && K == K@pre &&
      left == left@pre && right == right@pre &&
      n <= 100000 && 1 <= K && K <= 30 &&
      n * K <= 1000000 && n < Power2(K) &&
      0 <= left && left <= right && right < n &&
      len == right - left + 1 &&
      0 <= k && k < K && pow == Power2(k) && 1 <= pow && pow <= len &&
      STBuilt(l, st_l, K, n) && IntArray::full(st, n * K, st_l)
   */
  while (pow * 2 <= len) {
    pow = pow * 2;
    k++;
  }

  /*@ Assert
      st == st@pre && n == n@pre && K == K@pre &&
      left == left@pre && right == right@pre &&
      n <= 100000 && 1 <= K && K <= 30 &&
      n * K <= 1000000 && n < Power2(K) &&
      0 <= left && left <= right && right < n &&
      len == right - left + 1 &&
      0 <= k && k < K && pow == Power2(k) && 1 <= pow && pow <= len &&
      len < pow * 2 &&
      0 <= left * K + k && left * K + k < n * K &&
      0 <= (right - pow + 1) * K + k && (right - pow + 1) * K + k < n * K &&
      STBuilt(l, st_l, K, n) && IntArray::full(st, n * K, st_l)
   */
  int a = st[left * K + k];
  int b = st[(right - pow + 1) * K + k];
  if (a >= b) {
    return a;
  } else {
    return b;
  }
}
