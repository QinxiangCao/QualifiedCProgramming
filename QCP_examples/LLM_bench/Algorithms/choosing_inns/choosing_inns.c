#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq
      (CountsZeroPrefix : list Z -> Z -> Prop)
      (CountsZeroFull : Z -> list Z -> Prop)
      (CopyCountsPrefix : list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (ChoosingPrefixState : list Z -> list Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
      (ChoosingInnsAnswer : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_lib */

void initCounts(int *seen, int *good, int k)
/*@ Require
      1 <= k && k <= 50 &&
      IntArray::undef_full(seen, k) *
      IntArray::undef_full(good, k)
    Ensure
      exists seen_l good_l,
      CountsZeroFull(k, seen_l) &&
      CountsZeroFull(k, good_l) &&
      IntArray::full(seen, k, seen_l) *
      IntArray::full(good, k, good_l)
 */
{
  /*@ Inv Assert
      exists seen_l good_l,
      seen == seen@pre && good == good@pre && k == k@pre &&
      1 <= k@pre && k@pre <= 50 &&
      0 <= i && i <= k@pre &&
      CountsZeroPrefix(seen_l, i) &&
      CountsZeroPrefix(good_l, i) &&
      IntArray::seg(seen@pre, 0, i, seen_l) *
      IntArray::undef_seg(seen@pre, i, k@pre) *
      IntArray::seg(good@pre, 0, i, good_l) *
      IntArray::undef_seg(good@pre, i, k@pre)
   */
  for (int i = 0; i < k; ++i) {
    seen[i] = 0;
    good[i] = 0;
    /*@ Assert
      exists seen_l good_l,
      seen == seen@pre && good == good@pre && k == k@pre &&
      1 <= k@pre && k@pre <= 50 &&
      0 <= i && i < k@pre &&
      CountsZeroPrefix(seen_l, i + 1) &&
      CountsZeroPrefix(good_l, i + 1) &&
      IntArray::seg(seen@pre, 0, i + 1, seen_l) *
      IntArray::undef_seg(seen@pre, i + 1, k@pre) *
      IntArray::seg(good@pre, 0, i + 1, good_l) *
      IntArray::undef_seg(good@pre, i + 1, k@pre)
     */
  }
}

void copyCounts(int *seen, int *good, int k)
/*@ With (seen_l : list Z) (good_old : list Z)
    Require
      1 <= k && k <= 50 &&
      Zlength(seen_l) == k &&
      Zlength(good_old) == k &&
      IntArray::full(seen, k, seen_l) *
      IntArray::full(good, k, good_old) &&
      (forall (idx : Z), (0 <= idx && idx < k) => (0 <= seen_l[idx] && seen_l[idx] <= 200000)) &&
      (forall (idx : Z), (0 <= idx && idx < k) => (0 <= good_old[idx] && good_old[idx] <= 200000))
    Ensure
      IntArray::full(seen, k, seen_l) *
      IntArray::full(good, k, seen_l) &&
      (forall (idx : Z), (0 <= idx && idx < k) => (0 <= seen_l[idx] && seen_l[idx] <= 200000))
 */
{
  /*@ Inv Assert
      exists good_cur,
      seen == seen@pre && good == good@pre && k == k@pre &&
      1 <= k@pre && k@pre <= 50 &&
      Zlength(seen_l) == k@pre &&
      Zlength(good_old) == k@pre &&
      0 <= i && i <= k@pre &&
      CopyCountsPrefix(seen_l, good_old, good_cur, i, k@pre) &&
      IntArray::full(seen@pre, k@pre, seen_l) *
      IntArray::full(good@pre, k@pre, good_cur) &&
      (forall (idx : Z), (0 <= idx && idx < k@pre) => (0 <= seen_l[idx] && seen_l[idx] <= 200000)) &&
      (forall (idx : Z), (0 <= idx && idx < k@pre) => (0 <= good_cur[idx] && good_cur[idx] <= 200000))
   */
  for (int i = 0; i < k; ++i) {
    good[i] = seen[i];
    /*@ Assert
      exists good_cur,
      seen == seen@pre && good == good@pre && k == k@pre &&
      1 <= k@pre && k@pre <= 50 &&
      Zlength(seen_l) == k@pre &&
      Zlength(good_old) == k@pre &&
      0 <= i && i < k@pre &&
      CopyCountsPrefix(seen_l, good_old, good_cur, i + 1, k@pre) &&
      IntArray::full(seen@pre, k@pre, seen_l) *
      IntArray::full(good@pre, k@pre, good_cur) &&
      (forall (idx : Z), (0 <= idx && idx < k@pre) => (0 <= seen_l[idx] && seen_l[idx] <= 200000)) &&
      (forall (idx : Z), (0 <= idx && idx < k@pre) => (0 <= good_cur[idx] && good_cur[idx] <= 200000))
     */
  }
}

long long countChoosingInns(
    int *colors, int *costs, int n, int k, int p,
    int *seen, int *good)
/*@ With (colors_l : list Z) (costs_l : list Z)
    Require
      exists ans,
      0 <= n && n <= 200000 &&
      1 <= k && k <= 50 &&
      0 <= p && p <= 100 &&
      Zlength(colors_l) == n &&
      Zlength(costs_l) == n &&
      ChoosingInnsAnswer(colors_l, costs_l, n, k, p, ans) &&
      0 <= ans && ans <= 19999900000 &&
      IntArray::full(colors, n, colors_l) *
      IntArray::full(costs, n, costs_l) *
      IntArray::undef_full(seen, k) *
      IntArray::undef_full(good, k) &&
      (forall (idx : Z), (0 <= idx && idx < n) => (0 <= colors_l[idx] && colors_l[idx] < k)) &&
      (forall (idx : Z), (0 <= idx && idx < n) => (0 <= costs_l[idx] && costs_l[idx] <= 100))
    Ensure
      exists seen_l good_l,
      ChoosingInnsAnswer(colors_l, costs_l, n, k, p, __return) &&
      0 <= __return && __return <= 19999900000 &&
      IntArray::full(colors, n, colors_l) *
      IntArray::full(costs, n, costs_l) *
      IntArray::full(seen, k, seen_l) *
      IntArray::full(good, k, good_l)
 */
{
  long long answer = 0;

  initCounts(seen, good, k);
  /*@ Assert
      exists seen_l good_l ans,
      colors == colors@pre && costs == costs@pre &&
      n == n@pre && k == k@pre && p == p@pre &&
      seen == seen@pre && good == good@pre &&
      answer == 0 &&
      0 <= n@pre && n@pre <= 200000 &&
      1 <= k@pre && k@pre <= 50 &&
      0 <= p@pre && p@pre <= 100 &&
      Zlength(colors_l) == n@pre &&
      Zlength(costs_l) == n@pre &&
      ChoosingInnsAnswer(colors_l, costs_l, n@pre, k@pre, p@pre, ans) &&
      CountsZeroFull(k@pre, seen_l) &&
      CountsZeroFull(k@pre, good_l) &&
      ChoosingPrefixState(colors_l, costs_l, 0, k@pre, p@pre, 0, seen_l, good_l) &&
      IntArray::full(colors@pre, n@pre, colors_l) *
      IntArray::full(costs@pre, n@pre, costs_l) *
      IntArray::full(seen@pre, k@pre, seen_l) *
      IntArray::full(good@pre, k@pre, good_l) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= colors_l[idx] && colors_l[idx] < k@pre)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= costs_l[idx] && costs_l[idx] <= 100))
   */

  /*@ Inv Assert
      exists seen_l good_l ans,
      colors == colors@pre && costs == costs@pre &&
      n == n@pre && k == k@pre && p == p@pre &&
      seen == seen@pre && good == good@pre &&
      0 <= n@pre && n@pre <= 200000 &&
      1 <= k@pre && k@pre <= 50 &&
      0 <= p@pre && p@pre <= 100 &&
      Zlength(colors_l) == n@pre &&
      Zlength(costs_l) == n@pre &&
      0 <= i && i <= n@pre &&
      0 <= answer && answer <= 19999900000 &&
      ChoosingInnsAnswer(colors_l, costs_l, n@pre, k@pre, p@pre, ans) &&
      ChoosingPrefixState(colors_l, costs_l, i, k@pre, p@pre, answer, seen_l, good_l) &&
      IntArray::full(colors@pre, n@pre, colors_l) *
      IntArray::full(costs@pre, n@pre, costs_l) *
      IntArray::full(seen@pre, k@pre, seen_l) *
      IntArray::full(good@pre, k@pre, good_l) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= colors_l[idx] && colors_l[idx] < k@pre)) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= costs_l[idx] && costs_l[idx] <= 100)) &&
      (forall (idx : Z), (0 <= idx && idx < k@pre) => (0 <= seen_l[idx] && seen_l[idx] <= i)) &&
      (forall (idx : Z), (0 <= idx && idx < k@pre) => (0 <= good_l[idx] && good_l[idx] <= i))
   */
  for (int i = 0; i < n; ++i) {
    {
      int c = colors[i];
      int cost = costs[i];
      /*@ Assert
        exists seen_l good_l ans,
        colors == colors@pre && costs == costs@pre &&
        n == n@pre && k == k@pre && p == p@pre &&
        seen == seen@pre && good == good@pre &&
        c == colors_l[i] && cost == costs_l[i] &&
        0 <= n@pre && n@pre <= 200000 &&
        1 <= k@pre && k@pre <= 50 &&
        0 <= p@pre && p@pre <= 100 &&
        Zlength(colors_l) == n@pre &&
        Zlength(costs_l) == n@pre &&
        0 <= i && i < n@pre &&
        0 <= c && c < k@pre &&
        0 <= cost && cost <= 100 &&
        0 <= answer && answer <= 19999900000 &&
        0 <= seen_l[c] && seen_l[c] <= i &&
        0 <= good_l[c] && good_l[c] <= i &&
        answer + seen_l[c] <= 9223372036854775807 &&
        answer + good_l[c] <= 9223372036854775807 &&
        seen_l[c] + 1 <= INT_MAX &&
        ChoosingInnsAnswer(colors_l, costs_l, n@pre, k@pre, p@pre, ans) &&
        ChoosingPrefixState(colors_l, costs_l, i, k@pre, p@pre, answer, seen_l, good_l) &&
        IntArray::full(colors@pre, n@pre, colors_l) *
        IntArray::full(costs@pre, n@pre, costs_l) *
        IntArray::full(seen@pre, k@pre, seen_l) *
        IntArray::full(good@pre, k@pre, good_l) &&
        (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= colors_l[idx] && colors_l[idx] < k@pre)) &&
        (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= costs_l[idx] && costs_l[idx] <= 100)) &&
        (forall (idx : Z), (0 <= idx && idx < k@pre) => (0 <= seen_l[idx] && seen_l[idx] <= i)) &&
        (forall (idx : Z), (0 <= idx && idx < k@pre) => (0 <= good_l[idx] && good_l[idx] <= i))
       */
      if (cost <= p) {
        answer = answer + seen[c];
        seen[c] = seen[c] + 1;
        /*@ Assert
          exists seen_next seen_l good_l ans,
          colors == colors@pre && costs == costs@pre &&
          n == n@pre && k == k@pre && p == p@pre &&
          seen == seen@pre && good == good@pre &&
          c == colors_l[i] && cost == costs_l[i] &&
          0 <= n@pre && n@pre <= 200000 &&
          1 <= k@pre && k@pre <= 50 &&
          0 <= p@pre && p@pre <= 100 &&
          0 <= cost && cost <= p@pre &&
          Zlength(colors_l) == n@pre &&
          Zlength(costs_l) == n@pre &&
          Zlength(seen_next) == k@pre &&
          0 <= i && i < n@pre &&
          0 <= c && c < k@pre &&
          0 <= answer && answer <= 19999900000 &&
          seen_next == replace_Znth(c, seen_l[c] + 1, seen_l) &&
          ChoosingInnsAnswer(colors_l, costs_l, n@pre, k@pre, p@pre, ans) &&
          ChoosingPrefixState(colors_l, costs_l, i, k@pre, p@pre, answer - seen_l[c], seen_l, good_l) &&
          IntArray::full(colors@pre, n@pre, colors_l) *
          IntArray::full(costs@pre, n@pre, costs_l) *
          IntArray::full(seen@pre, k@pre, seen_next) *
          IntArray::full(good@pre, k@pre, good_l) &&
          (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= colors_l[idx] && colors_l[idx] < k@pre)) &&
          (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= costs_l[idx] && costs_l[idx] <= 100)) &&
          (forall (idx : Z), (0 <= idx && idx < k@pre) => (0 <= seen_next[idx] && seen_next[idx] <= i + 1)) &&
          (forall (idx : Z), (0 <= idx && idx < k@pre) => (0 <= good_l[idx] && good_l[idx] <= i))
         */
        copyCounts(seen, good, k);
        /*@ Assert
          exists seen_next ans,
          colors == colors@pre && costs == costs@pre &&
          n == n@pre && k == k@pre && p == p@pre &&
          seen == seen@pre && good == good@pre &&
          c == colors_l[i] && cost == costs_l[i] &&
          0 <= n@pre && n@pre <= 200000 &&
          1 <= k@pre && k@pre <= 50 &&
          0 <= p@pre && p@pre <= 100 &&
          Zlength(colors_l) == n@pre &&
          Zlength(costs_l) == n@pre &&
          Zlength(seen_next) == k@pre &&
          0 <= i && i < n@pre &&
          0 <= c && c < k@pre &&
          0 <= answer && answer <= 19999900000 &&
          ChoosingInnsAnswer(colors_l, costs_l, n@pre, k@pre, p@pre, ans) &&
          ChoosingPrefixState(colors_l, costs_l, i + 1, k@pre, p@pre, answer, seen_next, seen_next) &&
          IntArray::full(colors@pre, n@pre, colors_l) *
          IntArray::full(costs@pre, n@pre, costs_l) *
          IntArray::full(seen@pre, k@pre, seen_next) *
          IntArray::full(good@pre, k@pre, seen_next) &&
          (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= colors_l[idx] && colors_l[idx] < k@pre)) &&
          (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= costs_l[idx] && costs_l[idx] <= 100)) &&
          (forall (idx : Z), (0 <= idx && idx < k@pre) => (0 <= seen_next[idx] && seen_next[idx] <= i + 1))
         */
      } else {
        answer = answer + good[c];
        seen[c] = seen[c] + 1;
        /*@ Assert
          exists seen_next seen_l good_l ans,
          colors == colors@pre && costs == costs@pre &&
          n == n@pre && k == k@pre && p == p@pre &&
          seen == seen@pre && good == good@pre &&
          c == colors_l[i] && cost == costs_l[i] &&
          0 <= n@pre && n@pre <= 200000 &&
          1 <= k@pre && k@pre <= 50 &&
          0 <= p@pre && p@pre <= 100 &&
          p@pre < cost && cost <= 100 &&
          Zlength(colors_l) == n@pre &&
          Zlength(costs_l) == n@pre &&
          Zlength(seen_next) == k@pre &&
          Zlength(good_l) == k@pre &&
          0 <= i && i < n@pre &&
          0 <= c && c < k@pre &&
          0 <= answer && answer <= 19999900000 &&
          seen_next == replace_Znth(c, seen_l[c] + 1, seen_l) &&
          ChoosingInnsAnswer(colors_l, costs_l, n@pre, k@pre, p@pre, ans) &&
          ChoosingPrefixState(colors_l, costs_l, i, k@pre, p@pre, answer - good_l[c], seen_l, good_l) &&
          ChoosingPrefixState(colors_l, costs_l, i + 1, k@pre, p@pre, answer, seen_next, good_l) &&
          IntArray::full(colors@pre, n@pre, colors_l) *
          IntArray::full(costs@pre, n@pre, costs_l) *
          IntArray::full(seen@pre, k@pre, seen_next) *
          IntArray::full(good@pre, k@pre, good_l) &&
          (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= colors_l[idx] && colors_l[idx] < k@pre)) &&
          (forall (idx : Z), (0 <= idx && idx < n@pre) => (0 <= costs_l[idx] && costs_l[idx] <= 100)) &&
          (forall (idx : Z), (0 <= idx && idx < k@pre) => (0 <= seen_next[idx] && seen_next[idx] <= i + 1)) &&
          (forall (idx : Z), (0 <= idx && idx < k@pre) => (0 <= good_l[idx] && good_l[idx] <= i + 1))
         */
      }
    }
  }

  /*@ Assert
      exists seen_l good_l,
      colors == colors@pre && costs == costs@pre &&
      n == n@pre && k == k@pre && p == p@pre &&
      seen == seen@pre && good == good@pre &&
      0 <= n@pre && n@pre <= 200000 &&
      1 <= k@pre && k@pre <= 50 &&
      0 <= p@pre && p@pre <= 100 &&
      Zlength(colors_l) == n@pre &&
      Zlength(costs_l) == n@pre &&
      0 <= answer && answer <= 19999900000 &&
      ChoosingInnsAnswer(colors_l, costs_l, n@pre, k@pre, p@pre, answer) &&
      IntArray::full(colors@pre, n@pre, colors_l) *
      IntArray::full(costs@pre, n@pre, costs_l) *
      IntArray::full(seen@pre, k@pre, seen_l) *
      IntArray::full(good@pre, k@pre, good_l)
   */
  return answer;
}
