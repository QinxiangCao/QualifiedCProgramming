



/*@ Extern Coq
      (CountsZeroPrefix : list Z -> Z -> Prop)
      (CountsZeroFull : Z -> list Z -> Prop)
      (CopyCountsPrefix : list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (ChoosingInputSafe : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (CountArraySafe : list Z -> Z -> Z -> Prop)
      (ChoosingPrefixDataSafe : list Z -> list Z -> Z -> Z -> list Z -> list Z -> Prop)
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
      CountArraySafe(seen_l, k, 200000) &&
      CountArraySafe(good_old, k, 200000) &&
      IntArray::full(seen, k, seen_l) *
      IntArray::full(good, k, good_old)
    Ensure
      IntArray::full(seen, k, seen_l) *
      IntArray::full(good, k, seen_l) &&
      CountArraySafe(seen_l, k, 200000)
 */
{
  /*@ Inv Assert
      exists good_cur,
      seen == seen@pre && good == good@pre && k == k@pre &&
      1 <= k@pre && k@pre <= 50 &&
      0 <= i && i <= k@pre &&
      CountArraySafe(seen_l, k@pre, 200000) &&
      CountArraySafe(good_old, k@pre, 200000) &&
      CountArraySafe(good_cur, k@pre, 200000) &&
      CopyCountsPrefix(seen_l, good_old, good_cur, i, k@pre) &&
      IntArray::full(seen@pre, k@pre, seen_l) *
      IntArray::full(good@pre, k@pre, good_cur)
   */
  for (int i = 0; i < k; ++i) {
    good[i] = seen[i];
    /*@ Assert
      exists good_cur,
      seen == seen@pre && good == good@pre && k == k@pre &&
      1 <= k@pre && k@pre <= 50 &&
      0 <= i && i < k@pre &&
      CountArraySafe(seen_l, k@pre, 200000) &&
      CountArraySafe(good_old, k@pre, 200000) &&
      CountArraySafe(good_cur, k@pre, 200000) &&
      CopyCountsPrefix(seen_l, good_old, good_cur, i + 1, k@pre) &&
      IntArray::full(seen@pre, k@pre, seen_l) *
      IntArray::full(good@pre, k@pre, good_cur)
     */
  }
}

long long countChoosingInns(
    int *colors, int *costs, int n, int k, int p,
    int *seen, int *good)
/*@ With (colors_l : list Z) (costs_l : list Z)
    Require
      ChoosingInputSafe(colors_l, costs_l, n, k, p) &&
      IntArray::full(colors, n, colors_l) *
      IntArray::full(costs, n, costs_l) *
      IntArray::undef_full(seen, k) *
      IntArray::undef_full(good, k)
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
      exists seen_l good_l,
      colors == colors@pre && costs == costs@pre &&
      n == n@pre && k == k@pre && p == p@pre &&
      seen == seen@pre && good == good@pre &&
      answer == 0 &&
      ChoosingInputSafe(colors_l, costs_l, n@pre, k@pre, p@pre) &&
      CountsZeroFull(k@pre, seen_l) &&
      CountsZeroFull(k@pre, good_l) &&
      ChoosingPrefixDataSafe(colors_l, costs_l, 0, k@pre, seen_l, good_l) &&
      ChoosingPrefixState(colors_l, costs_l, 0, k@pre, p@pre, 0, seen_l, good_l) &&
      IntArray::full(colors@pre, n@pre, colors_l) *
      IntArray::full(costs@pre, n@pre, costs_l) *
      IntArray::full(seen@pre, k@pre, seen_l) *
      IntArray::full(good@pre, k@pre, good_l)
   */

  /*@ Inv Assert
      exists seen_l good_l,
      colors == colors@pre && costs == costs@pre &&
      n == n@pre && k == k@pre && p == p@pre &&
      seen == seen@pre && good == good@pre &&
      ChoosingInputSafe(colors_l, costs_l, n@pre, k@pre, p@pre) &&
      0 <= i && i <= n@pre &&
      0 <= answer && answer <= 19999900000 &&
      ChoosingPrefixDataSafe(colors_l, costs_l, i, k@pre, seen_l, good_l) &&
      ChoosingPrefixState(colors_l, costs_l, i, k@pre, p@pre, answer, seen_l, good_l) &&
      IntArray::full(colors@pre, n@pre, colors_l) *
      IntArray::full(costs@pre, n@pre, costs_l) *
      IntArray::full(seen@pre, k@pre, seen_l) *
      IntArray::full(good@pre, k@pre, good_l)
   */
  for (int i = 0; i < n; ++i) {
    {
      int c = colors[i];
      int cost = costs[i];
      /*@ Assert
        exists seen_l good_l,
        colors == colors@pre && costs == costs@pre &&
        n == n@pre && k == k@pre && p == p@pre &&
        seen == seen@pre && good == good@pre &&
        c == colors_l[i] && cost == costs_l[i] &&
        ChoosingInputSafe(colors_l, costs_l, n@pre, k@pre, p@pre) &&
        0 <= i && i < n@pre &&
        0 <= c && c < k@pre &&
        0 <= cost && cost <= 100 &&
        0 <= answer && answer <= 19999900000 &&
        0 <= seen_l[c] && seen_l[c] <= i &&
        0 <= good_l[c] && good_l[c] <= i &&
        answer + seen_l[c] <= 9223372036854775807 &&
        answer + good_l[c] <= 9223372036854775807 &&
        seen_l[c] + 1 <= INT_MAX &&
        ChoosingPrefixDataSafe(colors_l, costs_l, i, k@pre, seen_l, good_l) &&
        ChoosingPrefixState(colors_l, costs_l, i, k@pre, p@pre, answer, seen_l, good_l) &&
        IntArray::full(colors@pre, n@pre, colors_l) *
        IntArray::full(costs@pre, n@pre, costs_l) *
        IntArray::full(seen@pre, k@pre, seen_l) *
        IntArray::full(good@pre, k@pre, good_l)
       */
      if (cost <= p) {
        answer = answer + seen[c];
        seen[c] = seen[c] + 1;
        /*@ Assert
          exists seen_next seen_l good_l,
          colors == colors@pre && costs == costs@pre &&
          n == n@pre && k == k@pre && p == p@pre &&
          seen == seen@pre && good == good@pre &&
          c == colors_l[i] && cost == costs_l[i] &&
          ChoosingInputSafe(colors_l, costs_l, n@pre, k@pre, p@pre) &&
          0 <= cost && cost <= p@pre &&
          0 <= i && i < n@pre &&
          0 <= c && c < k@pre &&
          0 <= answer && answer <= 19999900000 &&
          seen_next == replace_Znth(c, seen_l[c] + 1, seen_l) &&
          ChoosingPrefixDataSafe(colors_l, costs_l, i, k@pre, seen_l, good_l) &&
          ChoosingPrefixDataSafe(colors_l, costs_l, i + 1, k@pre, seen_next, good_l) &&
          ChoosingPrefixState(colors_l, costs_l, i, k@pre, p@pre, answer - seen_l[c], seen_l, good_l) &&
          CountArraySafe(seen_next, k@pre, 200000) &&
          CountArraySafe(good_l, k@pre, 200000) &&
          IntArray::full(colors@pre, n@pre, colors_l) *
          IntArray::full(costs@pre, n@pre, costs_l) *
          IntArray::full(seen@pre, k@pre, seen_next) *
          IntArray::full(good@pre, k@pre, good_l)
         */
        copyCounts(seen, good, k);
        /*@ Assert
          exists seen_next,
          colors == colors@pre && costs == costs@pre &&
          n == n@pre && k == k@pre && p == p@pre &&
          seen == seen@pre && good == good@pre &&
          c == colors_l[i] && cost == costs_l[i] &&
          ChoosingInputSafe(colors_l, costs_l, n@pre, k@pre, p@pre) &&
          0 <= i && i < n@pre &&
          0 <= c && c < k@pre &&
          0 <= answer && answer <= 19999900000 &&
          ChoosingPrefixDataSafe(colors_l, costs_l, i + 1, k@pre, seen_next, seen_next) &&
          ChoosingPrefixState(colors_l, costs_l, i + 1, k@pre, p@pre, answer, seen_next, seen_next) &&
          IntArray::full(colors@pre, n@pre, colors_l) *
          IntArray::full(costs@pre, n@pre, costs_l) *
          IntArray::full(seen@pre, k@pre, seen_next) *
          IntArray::full(good@pre, k@pre, seen_next)
         */
      } else {
        answer = answer + good[c];
        seen[c] = seen[c] + 1;
        /*@ Assert
          exists seen_next seen_l good_l,
          colors == colors@pre && costs == costs@pre &&
          n == n@pre && k == k@pre && p == p@pre &&
          seen == seen@pre && good == good@pre &&
          c == colors_l[i] && cost == costs_l[i] &&
          ChoosingInputSafe(colors_l, costs_l, n@pre, k@pre, p@pre) &&
          p@pre < cost && cost <= 100 &&
          0 <= i && i < n@pre &&
          0 <= c && c < k@pre &&
          0 <= answer && answer <= 19999900000 &&
          seen_next == replace_Znth(c, seen_l[c] + 1, seen_l) &&
          ChoosingPrefixDataSafe(colors_l, costs_l, i, k@pre, seen_l, good_l) &&
          ChoosingPrefixDataSafe(colors_l, costs_l, i + 1, k@pre, seen_next, good_l) &&
          ChoosingPrefixState(colors_l, costs_l, i, k@pre, p@pre, answer - good_l[c], seen_l, good_l) &&
          ChoosingPrefixState(colors_l, costs_l, i + 1, k@pre, p@pre, answer, seen_next, good_l) &&
          IntArray::full(colors@pre, n@pre, colors_l) *
          IntArray::full(costs@pre, n@pre, costs_l) *
          IntArray::full(seen@pre, k@pre, seen_next) *
          IntArray::full(good@pre, k@pre, good_l)
         */
      }
    }
  }

  /*@ Assert
      exists seen_l good_l,
      colors == colors@pre && costs == costs@pre &&
      n == n@pre && k == k@pre && p == p@pre &&
      seen == seen@pre && good == good@pre &&
      ChoosingInputSafe(colors_l, costs_l, n@pre, k@pre, p@pre) &&
      0 <= answer && answer <= 19999900000 &&
      ChoosingInnsAnswer(colors_l, costs_l, n@pre, k@pre, p@pre, answer) &&
      IntArray::full(colors@pre, n@pre, colors_l) *
      IntArray::full(costs@pre, n@pre, costs_l) *
      IntArray::full(seen@pre, k@pre, seen_l) *
      IntArray::full(good@pre, k@pre, good_l)
   */
  return answer;
}
