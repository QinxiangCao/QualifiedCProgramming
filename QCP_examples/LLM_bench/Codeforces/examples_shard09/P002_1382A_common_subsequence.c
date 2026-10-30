/*@ Import Lean
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_lib
*/

/*
 * Codeforces 1382/A - Common Subsequence  (rating 800, BRUTE FORCE)
 *
 * A common subsequence of minimum length has length 1 whenever the two arrays
 * share any value at all, so it is enough to look for one common element; if
 * none exists no common non-empty subsequence exists either.
 */

// #include <stdio.h>
#include "string.h"

/*@ Extern Coq
      (Spec : list Z -> list Z -> option (list Z) -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_lib */

#define MAXV 1001

/* solver: pure.  Returns a value present in both arrays, or 0 if there is
 * none (values are >= 1, so 0 is safe as "not found"). */
static int solver(const int *a, int n, const int *b, int m)
/* QCP_INSERT_BEGIN:shard09-P002-solver-contract */
/*@ With (left : list Z) (right : list Z)
    Require
      1 <= n && n <= 1000 && 1 <= m && m <= 1000 && 
      (forall i, (0 <= i && i < n) => (1 <= left[i] && left[i] <= 1000)) && 
      (forall i, (0 <= i && i < m) => (1 <= right[i] && right[i] <= 1000)) &&
      n == Zlength(left) && m == Zlength(right) && 
      IntArray::full(a, n, left) * IntArray::full(b, m, right)
    Ensure
      exists (out : option (list Z)),
        Spec(left, right, out) &&
        ((out == None && __return == 0) || out == Some(cons(__return, nil))) && IntArray::full(a, n, left) * IntArray::full(b, m, right)
*/
/* QCP_INSERT_END:shard09-P002-solver-contract */
{
    char seen[MAXV];
    /*@ Assert
          a == a@pre && n == n@pre && b == b@pre && m == m@pre &&
          1 <= n@pre && n@pre <= 1000 &&
          1 <= m@pre && m@pre <= 1000 &&
          n@pre == Zlength(left) && m@pre == Zlength(right) &&
          (forall k,
            (0 <= k && k < n@pre) =>
              (1 <= left[k] && left[k] <= 1000)) &&
          (forall k,
            (0 <= k && k < m@pre) =>
              (1 <= right[k] && right[k] <= 1000)) &&
          0 <= sizeof(char[1001]) && sizeof(char[1001]) < INT_MAX &&
          IntArray::full(a@pre, n@pre, left) *
          IntArray::full(b@pre, m@pre, right) *
          CharArray::undef_full(
            pointer_offset(seen, 0, signed char),
            sizeof(char[1001]))
    */
    memset(seen, 0, sizeof seen);
    /*@ Inv Assert
          exists seen_l,
            a == a@pre && n == n@pre && b == b@pre && m == m@pre &&
            1 <= n@pre && n@pre <= 1000 &&
            1 <= m@pre && m@pre <= 1000 &&
            n@pre == Zlength(left) && m@pre == Zlength(right) &&
            (forall k,
              (0 <= k && k < n@pre) =>
                (1 <= left[k] && left[k] <= 1000)) &&
            (forall k,
              (0 <= k && k < m@pre) =>
                (1 <= right[k] && right[k] <= 1000)) &&
            0 <= i && i <= n@pre &&
            Zlength(seen_l) == 1001 &&
            (forall v,
              (0 <= v && v < 1001) =>
                (seen_l[v] == 0 || seen_l[v] == 1)) &&
            (forall k,
              (0 <= k && k < i) => seen_l[left[k]] == 1) &&
            (forall v,
              (0 <= v && v < 1001 && seen_l[v] == 1) =>
                (exists k,
                  0 <= k && k < i && left[k] == v)) &&
            IntArray::full(a@pre, n@pre, left) *
            IntArray::full(b@pre, m@pre, right) *
            CharArray::full(seen, 1001, seen_l)
    */
    for (int i = 0; i < n; i++)
        seen[a[i]] = 1;
    /*@ Inv Assert
          exists seen_l,
            a == a@pre && n == n@pre && b == b@pre && m == m@pre &&
            1 <= n@pre && n@pre <= 1000 &&
            1 <= m@pre && m@pre <= 1000 &&
            n@pre == Zlength(left) && m@pre == Zlength(right) &&
            (forall k,
              (0 <= k && k < n@pre) =>
                (1 <= left[k] && left[k] <= 1000)) &&
            (forall k,
              (0 <= k && k < m@pre) =>
                (1 <= right[k] && right[k] <= 1000)) &&
            0 <= j && j <= m@pre &&
            Zlength(seen_l) == 1001 &&
            (forall v,
              (0 <= v && v < 1001) =>
                (seen_l[v] == 0 || seen_l[v] == 1)) &&
            (forall k,
              (0 <= k && k < n@pre) => seen_l[left[k]] == 1) &&
            (forall v,
              (0 <= v && v < 1001 && seen_l[v] == 1) =>
                (exists k,
                  0 <= k && k < n@pre && left[k] == v)) &&
            (forall k,
              (0 <= k && k < j) => seen_l[right[k]] == 0) &&
            IntArray::full(a@pre, n@pre, left) *
            IntArray::full(b@pre, m@pre, right) *
            CharArray::full(seen, 1001, seen_l)
    */
    for (int j = 0; j < m; j++)
        if (seen[b[j]])
            return b[j];
    return 0;
}

// int main(void)
// {
//     int t;
//     if (scanf("%d", &t) != 1)
//         return 0;
//     while (t--) {
//         int n, m;
//         static int a[1005], b[1005];
//         scanf("%d %d", &n, &m);
//         for (int i = 0; i < n; i++)
//             scanf("%d", &a[i]);
//         for (int j = 0; j < m; j++)
//             scanf("%d", &b[j]);
//         int v = solver(a, n, b, m);
//         if (v)
//             printf("YES\n1 %d\n", v);
//         else
//             printf("NO\n");
//     }
//     return 0;
// }
