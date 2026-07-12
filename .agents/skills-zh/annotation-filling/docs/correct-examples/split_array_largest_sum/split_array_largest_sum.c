#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq
      (PrefixSplitState : list Z -> Z -> Z -> Z -> Z -> Prop)
      (CanSplit : list Z -> Z -> Z -> Prop)
      (CannotSplit : list Z -> Z -> Z -> Prop)
      (MinimizedMaxSegmentSum : list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_lib */

int check(int *arr, int n, int m, int cap)
/*@ With (l : list Z)
    Require
      1 <= n && n <= 100000 &&
      1 <= m && m <= n &&
      0 <= cap && cap <= 1000000000 &&
      Zlength(l) == n &&
      IntArray::full(arr, n, l) &&
      (forall (i : Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100000000))
    Ensure
      IntArray::full(arr, n, l) &&
      0 <= __return && __return <= 1 &&
      (__return == 1 => CanSplit(l, m, cap)) &&
      (__return == 0 => CannotSplit(l, m, cap))
 */
{
  int cnt = 1;
  int cur = 0;
  /*@ Inv Assert
      arr == arr@pre && n == n@pre && m == m@pre && cap == cap@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= m@pre && m@pre <= n@pre &&
      0 <= cap@pre && cap@pre <= 1000000000 &&
      Zlength(l) == n@pre &&
      IntArray::full(arr, n@pre, l) &&
      (forall (k : Z), (0 <= k && k < n@pre) => (0 <= l[k] && l[k] < 100000000)) &&
      0 <= i && i <= n@pre &&
      1 <= cnt && cnt <= i + 1 &&
      0 <= cur && cur <= cap@pre &&
      PrefixSplitState(l, cap@pre, i, cnt, cur)
   */
  for (int i = 0; i < n; ++i) {
    int x = arr[i];
    if (x > cap) {
      return 0;
    }
    if (cur + x > cap) {
      cnt = cnt + 1;
      cur = x;
    } else {
      cur = cur + x;
    }
  }
  if (cnt <= m) {
    return 1;
  } else {
    return 0;
  }
}

int splitArrayLargestSum(int *arr, int n, int m)
/*@ With (l : list Z)
    Require
      exists ans,
      1 <= n && n <= 100000 &&
      1 <= m && m <= n &&
      Zlength(l) == n &&
      IntArray::full(arr, n, l) &&
      (forall (i : Z), (0 <= i && i < n) => (0 <= l[i] && l[i] < 100000000)) &&

      MinimizedMaxSegmentSum(l, m, ans) &&
      0 <= ans &&
      ans <= 1000000000

    Ensure
      MinimizedMaxSegmentSum(l, m, __return) &&
      IntArray::full(arr, n, l)
 */
{
  int left = 0;
  int right = 1000000000;

  /*@ Inv Assert
      exists res,
      arr == arr@pre && n == n@pre && m == m@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= m@pre && m@pre <= n@pre &&
      Zlength(l) == n@pre &&
      IntArray::full(arr, n@pre, l) &&
      (forall (i : Z), (0 <= i && i < n@pre) => (0 <= l[i] && l[i] < 100000000)) &&

      0 <= left && right <= 1000000000 &&
      left <= right &&
      left <= res && res <= right &&
      MinimizedMaxSegmentSum(l, m, res)
   */
  while (left < right) {
    int mid = left + (right - left) / 2;
    int ok = check(arr, n, m, mid);
    if (ok) {
      right = mid;
    } else {
      left = mid + 1;
    }
  }

  return left;
}
