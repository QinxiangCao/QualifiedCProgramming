



/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (eq : {A} -> A -> A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (InnsCopiedPrefix : list Z -> list Z -> list Z -> Z -> Z -> Prop)
      (InnsPrefixCounts : list Z -> list Z -> Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
      (InnsPairAnswer : list Z -> list Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_lib */

void initCounts(int *seen, int *good, int k)
/*@ Require
      1 <= k && k <= 50 &&
      IntArray::undef_full(seen, k) *
      IntArray::undef_full(good, k)
    Ensure
      exists seen_l good_l,
      Zlength(seen_l) == k && Forall(eq(0), seen_l) &&
      Zlength(good_l) == k && Forall(eq(0), good_l) &&
      IntArray::full(seen, k, seen_l) *
      IntArray::full(good, k, good_l)
 */
{
  /*@ Inv Assert
      exists seen_l good_l,
      seen == seen@pre && good == good@pre && k == k@pre &&
      1 <= k@pre && k@pre <= 50 &&
      0 <= i && i <= k@pre &&
      Zlength(seen_l) == i && Forall(eq(0), seen_l) &&
      Zlength(good_l) == i && Forall(eq(0), good_l) &&
      IntArray::seg(seen@pre, 0, i, seen_l) *
      IntArray::undef_seg(seen@pre, i, k@pre) *
      IntArray::seg(good@pre, 0, i, good_l) *
      IntArray::undef_seg(good@pre, i, k@pre)
   */
  for (int i = 0; i < k; ++i) {
    seen[i] = 0;
    good[i] = 0;

  }
}

void copyCounts(int *seen, int *good, int k)
/*@ With (seen_l : list Z) (good_old : list Z)
    Require
      1 <= k && k <= 50 &&
      Zlength(seen_l) == k && Forall(Z::le(0), seen_l) && Forall(Z::ge(200000), seen_l) &&
      Zlength(good_old) == k && Forall(Z::le(0), good_old) && Forall(Z::ge(200000), good_old) &&
      IntArray::full(seen, k, seen_l) *
      IntArray::full(good, k, good_old)
    Ensure
      IntArray::full(seen, k, seen_l) *
      IntArray::full(good, k, seen_l)
 */
{
  /*@ Inv Assert
      exists good_cur,
      seen == seen@pre && good == good@pre && k == k@pre &&
      1 <= k@pre && k@pre <= 50 &&
      0 <= i && i <= k@pre &&
      Zlength(seen_l) == k@pre && Forall(Z::le(0), seen_l) && Forall(Z::ge(200000), seen_l) &&
      Zlength(good_old) == k@pre && Forall(Z::le(0), good_old) && Forall(Z::ge(200000), good_old) &&
      Zlength(good_cur) == k@pre && Forall(Z::le(0), good_cur) && Forall(Z::ge(200000), good_cur) &&
      InnsCopiedPrefix(seen_l, good_old, good_cur, i, k@pre) &&
      IntArray::full(seen@pre, k@pre, seen_l) *
      IntArray::full(good@pre, k@pre, good_cur)
   */
  for (int i = 0; i < k; ++i) {
    good[i] = seen[i];

  }
}

long long countChoosingInns(
    int *colors, int *costs, int n, int k, int p)
/*@ With (colors_l : list Z) (costs_l : list Z)
    Require
      0 <= n && n <= 200000 && 1 <= k && k <= 50 && 0 <= p && p <= 100 && Zlength(colors_l) == n && Zlength(costs_l) == n && Forall(Z::le(0), colors_l) && Forall(Z::ge(k - 1), colors_l) && Forall(Z::le(0), costs_l) && Forall(Z::ge(100), costs_l) &&
      IntArray::full(colors, n, colors_l) *
      IntArray::full(costs, n, costs_l)
    Ensure
      InnsPairAnswer(colors_l, costs_l, n, p, __return) &&
      IntArray::full(colors, n, colors_l) *
      IntArray::full(costs, n, costs_l)
 */
{
  int seen[50];
  int good[50];
  long long answer = 0;

  /*@ Assert
      colors == colors@pre && costs == costs@pre && n == n@pre &&
      k == k@pre && p == p@pre && answer == 0 &&
      0 <= n && n <= 200000 && 1 <= k && k <= 50 && 0 <= p && p <= 100 && Zlength(colors_l) == n && Zlength(costs_l) == n && Forall(Z::le(0), colors_l) && Forall(Z::ge(k - 1), colors_l) && Forall(Z::le(0), costs_l) && Forall(Z::ge(100), costs_l) &&
      IntArray::full(colors, n, colors_l) *
      IntArray::full(costs, n, costs_l) *
      IntArray::undef_full(pointer_offset(seen, 0, sizeof(int), int), k) *
      IntArray::undef_full(pointer_offset(good, 0, sizeof(int), int), k) *
      IntArray::undef_seg(seen, k, 50) *
      IntArray::undef_seg(good, k, 50)
   */
  initCounts(seen, good, k);
  

  /*@ Inv Assert
      exists seen_l good_l,
      colors == colors@pre && costs == costs@pre &&
      n == n@pre && k == k@pre && p == p@pre &&
      0 <= n@pre && n@pre <= 200000 && 1 <= k@pre && k@pre <= 50 && 0 <= p@pre && p@pre <= 100 && Zlength(colors_l) == n@pre && Zlength(costs_l) == n@pre && Forall(Z::le(0), colors_l) && Forall(Z::ge(k@pre - 1), colors_l) && Forall(Z::le(0), costs_l) && Forall(Z::ge(100), costs_l) &&
      0 <= i && i <= n@pre &&
      0 <= answer && answer <= 19999900000 &&
      0 <= i && i <= Zlength(colors_l) && Zlength(costs_l) == Zlength(colors_l) && Zlength(seen_l) == k@pre && Forall(Z::le(0), seen_l) && Forall(Z::ge(i), seen_l) && Zlength(good_l) == k@pre && Forall(Z::le(0), good_l) && Forall(Z::ge(i), good_l) &&
      InnsPrefixCounts(colors_l, costs_l, i, k@pre, p@pre, answer, seen_l, good_l) &&
      IntArray::full(colors@pre, n@pre, colors_l) *
      IntArray::full(costs@pre, n@pre, costs_l) *
      IntArray::full(seen, k@pre, seen_l) *
      IntArray::full(good, k@pre, good_l) *
      IntArray::undef_seg(seen, k@pre, 50) *
      IntArray::undef_seg(good, k@pre, 50)
   */
  for (int i = 0; i < n; ++i) {
    {
      int c = colors[i];
      int cost = costs[i];
      /*@ Assert
        exists seen_l good_l,
        colors == colors@pre && costs == costs@pre &&
        n == n@pre && k == k@pre && p == p@pre &&
          c == colors_l[i] && cost == costs_l[i] &&
        0 <= n@pre && n@pre <= 200000 && 1 <= k@pre && k@pre <= 50 && 0 <= p@pre && p@pre <= 100 && Zlength(colors_l) == n@pre && Zlength(costs_l) == n@pre && Forall(Z::le(0), colors_l) && Forall(Z::ge(k@pre - 1), colors_l) && Forall(Z::le(0), costs_l) && Forall(Z::ge(100), costs_l) &&
        0 <= i && i < n@pre &&
        0 <= c && c < k@pre &&
        0 <= cost && cost <= 100 &&
        0 <= answer && answer <= 19999900000 &&
        0 <= seen_l[c] && seen_l[c] <= i &&
        0 <= good_l[c] && good_l[c] <= i &&
        answer + seen_l[c] <= 9223372036854775807 &&
        answer + good_l[c] <= 9223372036854775807 &&
        seen_l[c] + 1 <= INT_MAX &&
        0 <= i && i <= Zlength(colors_l) && Zlength(costs_l) == Zlength(colors_l) && Zlength(seen_l) == k@pre && Forall(Z::le(0), seen_l) && Forall(Z::ge(i), seen_l) && Zlength(good_l) == k@pre && Forall(Z::le(0), good_l) && Forall(Z::ge(i), good_l) &&
        InnsPrefixCounts(colors_l, costs_l, i, k@pre, p@pre, answer, seen_l, good_l) &&
        IntArray::full(colors@pre, n@pre, colors_l) *
        IntArray::full(costs@pre, n@pre, costs_l) *
        IntArray::full(seen, k@pre, seen_l) *
        IntArray::full(good, k@pre, good_l) *
      IntArray::undef_seg(seen, k@pre, 50) *
      IntArray::undef_seg(good, k@pre, 50)
       */
      if (cost <= p) {
        answer = answer + seen[c];
        seen[c] = seen[c] + 1;
        /*@ Assert
          exists seen_next seen_l good_l,
          colors == colors@pre && costs == costs@pre &&
          n == n@pre && k == k@pre && p == p@pre &&
              c == colors_l[i] && cost == costs_l[i] &&
          0 <= n@pre && n@pre <= 200000 && 1 <= k@pre && k@pre <= 50 && 0 <= p@pre && p@pre <= 100 && Zlength(colors_l) == n@pre && Zlength(costs_l) == n@pre && Forall(Z::le(0), colors_l) && Forall(Z::ge(k@pre - 1), colors_l) && Forall(Z::le(0), costs_l) && Forall(Z::ge(100), costs_l) &&
          0 <= cost && cost <= p@pre &&
          0 <= i && i < n@pre &&
          0 <= c && c < k@pre &&
          0 <= answer && answer <= 19999900000 &&
          seen_next == replace_Znth(c, seen_l[c] + 1, seen_l) &&
          0 <= i && i <= Zlength(colors_l) && Zlength(costs_l) == Zlength(colors_l) && Zlength(seen_l) == k@pre && Forall(Z::le(0), seen_l) && Forall(Z::ge(i), seen_l) && Zlength(good_l) == k@pre && Forall(Z::le(0), good_l) && Forall(Z::ge(i), good_l) &&
          0 <= i + 1 && i + 1 <= Zlength(colors_l) && Zlength(costs_l) == Zlength(colors_l) && Zlength(seen_next) == k@pre && Forall(Z::le(0), seen_next) && Forall(Z::ge(i + 1), seen_next) && Zlength(good_l) == k@pre && Forall(Z::le(0), good_l) && Forall(Z::ge(i + 1), good_l) &&
          InnsPrefixCounts(colors_l, costs_l, i, k@pre, p@pre, answer - seen_l[c], seen_l, good_l) &&
          Zlength(seen_next) == k@pre && Forall(Z::le(0), seen_next) && Forall(Z::ge(200000), seen_next) &&
          Zlength(good_l) == k@pre && Forall(Z::le(0), good_l) && Forall(Z::ge(200000), good_l) &&
          IntArray::full(colors@pre, n@pre, colors_l) *
          IntArray::full(costs@pre, n@pre, costs_l) *
          IntArray::full(pointer_offset(seen, 0, sizeof(int), int), k@pre, seen_next) *
          IntArray::full(pointer_offset(good, 0, sizeof(int), int), k@pre, good_l) *
      IntArray::undef_seg(seen, k@pre, 50) *
      IntArray::undef_seg(good, k@pre, 50)
         */
        copyCounts(seen, good, k);
        /*@ Assert
          exists seen_next,
          colors == colors@pre && costs == costs@pre &&
          n == n@pre && k == k@pre && p == p@pre &&
              c == colors_l[i] && cost == costs_l[i] &&
          0 <= n@pre && n@pre <= 200000 && 1 <= k@pre && k@pre <= 50 && 0 <= p@pre && p@pre <= 100 && Zlength(colors_l) == n@pre && Zlength(costs_l) == n@pre && Forall(Z::le(0), colors_l) && Forall(Z::ge(k@pre - 1), colors_l) && Forall(Z::le(0), costs_l) && Forall(Z::ge(100), costs_l) &&
          0 <= i && i < n@pre &&
          0 <= c && c < k@pre &&
          0 <= answer && answer <= 19999900000 &&
          0 <= i + 1 && i + 1 <= Zlength(colors_l) && Zlength(costs_l) == Zlength(colors_l) && Zlength(seen_next) == k@pre && Forall(Z::le(0), seen_next) && Forall(Z::ge(i + 1), seen_next) && Zlength(seen_next) == k@pre && Forall(Z::le(0), seen_next) && Forall(Z::ge(i + 1), seen_next) &&
          InnsPrefixCounts(colors_l, costs_l, i + 1, k@pre, p@pre, answer, seen_next, seen_next) &&
          IntArray::full(colors@pre, n@pre, colors_l) *
          IntArray::full(costs@pre, n@pre, costs_l) *
          IntArray::full(seen, k@pre, seen_next) *
          IntArray::full(good, k@pre, seen_next) *
      IntArray::undef_seg(seen, k@pre, 50) *
      IntArray::undef_seg(good, k@pre, 50)
         */
      } else {
        answer = answer + good[c];
        seen[c] = seen[c] + 1;
        /*@ Assert
          exists seen_next seen_l good_l,
          colors == colors@pre && costs == costs@pre &&
          n == n@pre && k == k@pre && p == p@pre &&
              c == colors_l[i] && cost == costs_l[i] &&
          0 <= n@pre && n@pre <= 200000 && 1 <= k@pre && k@pre <= 50 && 0 <= p@pre && p@pre <= 100 && Zlength(colors_l) == n@pre && Zlength(costs_l) == n@pre && Forall(Z::le(0), colors_l) && Forall(Z::ge(k@pre - 1), colors_l) && Forall(Z::le(0), costs_l) && Forall(Z::ge(100), costs_l) &&
          p@pre < cost && cost <= 100 &&
          0 <= i && i < n@pre &&
          0 <= c && c < k@pre &&
          0 <= answer && answer <= 19999900000 &&
          seen_next == replace_Znth(c, seen_l[c] + 1, seen_l) &&
          0 <= i && i <= Zlength(colors_l) && Zlength(costs_l) == Zlength(colors_l) && Zlength(seen_l) == k@pre && Forall(Z::le(0), seen_l) && Forall(Z::ge(i), seen_l) && Zlength(good_l) == k@pre && Forall(Z::le(0), good_l) && Forall(Z::ge(i), good_l) &&
          0 <= i + 1 && i + 1 <= Zlength(colors_l) && Zlength(costs_l) == Zlength(colors_l) && Zlength(seen_next) == k@pre && Forall(Z::le(0), seen_next) && Forall(Z::ge(i + 1), seen_next) && Zlength(good_l) == k@pre && Forall(Z::le(0), good_l) && Forall(Z::ge(i + 1), good_l) &&
          InnsPrefixCounts(colors_l, costs_l, i, k@pre, p@pre, answer - good_l[c], seen_l, good_l) &&
          InnsPrefixCounts(colors_l, costs_l, i + 1, k@pre, p@pre, answer, seen_next, good_l) &&
          IntArray::full(colors@pre, n@pre, colors_l) *
          IntArray::full(costs@pre, n@pre, costs_l) *
          IntArray::full(seen, k@pre, seen_next) *
          IntArray::full(good, k@pre, good_l) *
      IntArray::undef_seg(seen, k@pre, 50) *
      IntArray::undef_seg(good, k@pre, 50)
         */
      }
    }
  }

  
  /*@ Assert
      colors == colors@pre && costs == costs@pre && n == n@pre && k == k@pre && p == p@pre &&
      InnsPairAnswer(colors_l, costs_l, n, p, answer) &&
      IntArray::full(colors, n, colors_l) * IntArray::full(costs, n, costs_l) *
      IntArray::undef_full(seen, 50) * IntArray::undef_full(good, 50)
   */
  return answer;
}
