#include "verification_stdlib.h"
#include "verification_list.h"
#include "array2_def.h"

/*@ Extern Coq
      (StreetlightMinimumEnergy : list Z -> list Z -> Z -> Z -> Prop)
      (StreetlightPrefixProgress : list Z -> list Z -> Z -> Prop)
      (StreetlightInfRows : list (list Z) -> Z -> Z -> Prop)
      (StreetlightInfProgress : list (list Z) -> Z -> Z -> Z -> Prop)
      (StreetlightLengthsDone : list Z -> list Z -> list (list Z) -> list (list Z) -> Z -> Z -> Z -> Prop)
      (StreetlightLeftProgress : list Z -> list Z -> list (list Z) -> list (list Z) -> Z -> Z -> Z -> Z -> Prop)
      (StreetlightLeftEndpointReady : list Z -> list Z -> list (list Z) -> list (list Z) -> Z -> Z -> Z -> Z -> Prop)
      (StreetlightFinalCandidates : list Z -> list Z -> list (list Z) -> list (list Z) -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.streetlight.streetlight_lib */

int solve(int *pos, int *power, int n, int c,
          int *pre, int *dp_l, int *dp_r)
/*@ With (pos_l power_l : list Z)
         (dp_l_init dp_r_init : list (list Z))
    Require
      1 <= n && n <= 50 &&
      1 <= c && c <= n &&
      Zlength(pos_l) == n &&
      Zlength(power_l) == n &&
      (forall (i : Z),
        (0 <= i && i < n) =>
          (0 <= pos_l[i] && pos_l[i] <= 8000)) &&
      (forall (i : Z),
        (0 <= i && i + 1 < n) => pos_l[i] < pos_l[i + 1]) &&
      (forall (i : Z),
        (0 <= i && i < n) =>
          (1 <= power_l[i] && power_l[i] <= 100)) &&
      IntArray::full(pos, n, pos_l) *
      IntArray::full(power, n, power_l) *
      IntArray::undef_full(pre, n + 1) *
      IntArray2::full(dp_l, n, n, dp_l_init) *
      IntArray2::full(dp_r, n, n, dp_r_init)
    Ensure
      exists pre_l dp_l_final dp_r_final,
      StreetlightMinimumEnergy(pos_l, power_l, c - 1, __return) &&
      0 <= __return && __return <= 1960000000 &&
      IntArray::full(pos, n, pos_l) *
      IntArray::full(power, n, power_l) *
      IntArray::full(pre, n + 1, pre_l) *
      IntArray2::full(dp_l, n, n, dp_l_final) *
      IntArray2::full(dp_r, n, n, dp_r_final)
 */
{
  int width = n;
  int inf = 2147483647;
  int start = c - 1;

  pre[0] = 0;
  /*@ Inv Assert
      exists prefix_l,
      pos == pos@pre && power == power@pre && n == n@pre &&
      c == c@pre && pre == pre@pre && dp_l == dp_l@pre &&
      dp_r == dp_r@pre && width == n@pre &&
      inf == 2147483647 && start == c@pre - 1 &&
      1 <= n@pre && n@pre <= 50 &&
      1 <= c@pre && c@pre <= n@pre &&
      0 <= i && i <= n@pre &&
      Zlength(pos_l) == n@pre && Zlength(power_l) == n@pre &&
      (forall (k : Z),
        (0 <= k && k < n@pre) =>
          (0 <= pos_l[k] && pos_l[k] <= 8000)) &&
      (forall (k : Z),
        (0 <= k && k + 1 < n@pre) => pos_l[k] < pos_l[k + 1]) &&
      (forall (k : Z),
        (0 <= k && k < n@pre) =>
          (1 <= power_l[k] && power_l[k] <= 100)) &&
      (forall (k : Z),
        (0 <= k && k <= i) =>
          (0 <= prefix_l[k] && prefix_l[k] <= 5000)) &&
      StreetlightPrefixProgress(power_l, prefix_l, i) &&
      IntArray::full(pos, n@pre, pos_l) *
      IntArray::full(power, n@pre, power_l) *
      IntArray::seg(pre, 0, i + 1, prefix_l) *
      IntArray::undef_seg(pre, i + 1, n@pre + 1) *
      IntArray2::full(dp_l, n@pre, n@pre, dp_l_init) *
      IntArray2::full(dp_r, n@pre, n@pre, dp_r_init)
   */
  for (int i = 0; i < n; ++i) {
    pre[i + 1] = pre[i] + power[i];
  }
  int total = pre[n];

  /*@ Inv Assert
      exists prefix_l left_table right_table,
      pos == pos@pre && power == power@pre && n == n@pre &&
      c == c@pre && pre == pre@pre && dp_l == dp_l@pre &&
      dp_r == dp_r@pre && width == n@pre &&
      inf == 2147483647 && start == c@pre - 1 &&
      total == prefix_l[n@pre] &&
      1 <= n@pre && n@pre <= 50 &&
      1 <= c@pre && c@pre <= n@pre &&
      0 <= row && row <= n@pre &&
      1 <= total && total <= 5000 &&
      Zlength(pos_l) == n@pre && Zlength(power_l) == n@pre &&
      (forall (k : Z),
        (0 <= k && k < n@pre) =>
          (0 <= pos_l[k] && pos_l[k] <= 8000)) &&
      (forall (k : Z),
        (0 <= k && k + 1 < n@pre) => pos_l[k] < pos_l[k + 1]) &&
      (forall (k : Z),
        (0 <= k && k < n@pre) =>
          (1 <= power_l[k] && power_l[k] <= 100)) &&
      (forall (k : Z),
        (0 <= k && k <= n@pre) =>
          (0 <= prefix_l[k] && prefix_l[k] <= 5000)) &&
      StreetlightPrefixProgress(power_l, prefix_l, n@pre) &&
      StreetlightInfRows(left_table, n@pre, row) &&
      StreetlightInfRows(right_table, n@pre, row) &&
      IntArray::full(pos, n@pre, pos_l) *
      IntArray::full(power, n@pre, power_l) *
      IntArray::full(pre, n@pre + 1, prefix_l) *
      IntArray2::full(dp_l, n@pre, n@pre, left_table) *
      IntArray2::full(dp_r, n@pre, n@pre, right_table)
   */
  for (int row = 0; row < n; ++row) {
    /*@ Inv Assert
        exists prefix_l left_table right_table,
        pos == pos@pre && power == power@pre && n == n@pre &&
        c == c@pre && pre == pre@pre && dp_l == dp_l@pre &&
        dp_r == dp_r@pre && width == n@pre &&
        inf == 2147483647 && start == c@pre - 1 &&
        total == prefix_l[n@pre] &&
        1 <= n@pre && n@pre <= 50 &&
        1 <= c@pre && c@pre <= n@pre &&
        0 <= row && row < n@pre &&
        0 <= col && col <= n@pre &&
        1 <= total && total <= 5000 &&
        Zlength(pos_l) == n@pre && Zlength(power_l) == n@pre &&
        (forall (k : Z),
          (0 <= k && k < n@pre) =>
            (0 <= pos_l[k] && pos_l[k] <= 8000)) &&
        (forall (k : Z),
          (0 <= k && k + 1 < n@pre) => pos_l[k] < pos_l[k + 1]) &&
        (forall (k : Z),
          (0 <= k && k < n@pre) =>
            (1 <= power_l[k] && power_l[k] <= 100)) &&
        (forall (k : Z),
          (0 <= k && k <= n@pre) =>
            (0 <= prefix_l[k] && prefix_l[k] <= 5000)) &&
        StreetlightPrefixProgress(power_l, prefix_l, n@pre) &&
        StreetlightInfProgress(left_table, n@pre, row, col) &&
        StreetlightInfProgress(right_table, n@pre, row, col) &&
        IntArray::full(pos, n@pre, pos_l) *
        IntArray::full(power, n@pre, power_l) *
        IntArray::full(pre, n@pre + 1, prefix_l) *
        IntArray2::full(dp_l, n@pre, n@pre, left_table) *
        IntArray2::full(dp_r, n@pre, n@pre, right_table)
     */
    for (int col = 0; col < n; ++col) {
      *(dp_l + row * width + col) = inf;
      *(dp_r + row * width + col) = inf;
    }
  }

  *(dp_l + start * width + start) = 0;
  *(dp_r + start * width + start) = 0;

  /*@ Inv Assert
      exists prefix_l left_table right_table,
      pos == pos@pre && power == power@pre && n == n@pre &&
      c == c@pre && pre == pre@pre && dp_l == dp_l@pre &&
      dp_r == dp_r@pre && width == n@pre &&
      inf == 2147483647 && start == c@pre - 1 &&
      total == prefix_l[n@pre] &&
      1 <= n@pre && n@pre <= 50 &&
      1 <= c@pre && c@pre <= n@pre &&
      0 <= start && start < n@pre &&
      2 <= len && len <= n@pre + 1 &&
      1 <= total && total <= 5000 &&
      Zlength(pos_l) == n@pre && Zlength(power_l) == n@pre &&
      (forall (k : Z),
        (0 <= k && k < n@pre) =>
          (0 <= pos_l[k] && pos_l[k] <= 8000)) &&
      (forall (k : Z),
        (0 <= k && k + 1 < n@pre) => pos_l[k] < pos_l[k + 1]) &&
      (forall (k : Z),
        (0 <= k && k < n@pre) =>
          (1 <= power_l[k] && power_l[k] <= 100)) &&
      (forall (k : Z),
        (0 <= k && k <= n@pre) =>
          (0 <= prefix_l[k] && prefix_l[k] <= 5000)) &&
      (forall (pending_right : Z),
        (start + len - 1 <= pending_right && pending_right < n@pre) =>
          left_table[start][pending_right] == inf) &&
      (forall (pending_left : Z),
        (0 <= pending_left && pending_left <= start - len + 1) =>
          right_table[pending_left][start] == inf) &&
      StreetlightPrefixProgress(power_l, prefix_l, n@pre) &&
      StreetlightLengthsDone(pos_l, power_l, left_table, right_table,
        n@pre, start, len) &&
      IntArray::full(pos, n@pre, pos_l) *
      IntArray::full(power, n@pre, power_l) *
      IntArray::full(pre, n@pre + 1, prefix_l) *
      IntArray2::full(dp_l, n@pre, n@pre, left_table) *
      IntArray2::full(dp_r, n@pre, n@pre, right_table)
   */
  for (int len = 2; len <= n; ++len) {
    int first_left = start - len + 1;
    if (first_left < 0) {
      first_left = 0;
    }

    int last_left = start;
    if (last_left + len > n) {
      last_left = n - len;
    }

    /*@ Inv Assert
        exists prefix_l left_table right_table,
        pos == pos@pre && power == power@pre && n == n@pre &&
        c == c@pre && pre == pre@pre && dp_l == dp_l@pre &&
        dp_r == dp_r@pre && width == n@pre &&
        inf == 2147483647 && start == c@pre - 1 &&
        total == prefix_l[n@pre] &&
        1 <= n@pre && n@pre <= 50 &&
        1 <= c@pre && c@pre <= n@pre &&
        0 <= start && start < n@pre &&
        2 <= len && len <= n@pre &&
        1 <= total && total <= 5000 &&
        ((first_left == 0 && start - len + 1 <= 0) ||
         (first_left == start - len + 1 && 0 <= start - len + 1)) &&
        ((last_left == n@pre - len && n@pre < start + len) ||
         (last_left == start && start + len <= n@pre)) &&
        0 <= first_left && first_left <= last_left &&
        first_left <= left && left <= last_left + 1 &&
        Zlength(pos_l) == n@pre && Zlength(power_l) == n@pre &&
        (forall (k : Z),
          (0 <= k && k < n@pre) =>
            (0 <= pos_l[k] && pos_l[k] <= 8000)) &&
        (forall (k : Z),
          (0 <= k && k + 1 < n@pre) => pos_l[k] < pos_l[k + 1]) &&
        (forall (k : Z),
          (0 <= k && k < n@pre) =>
            (1 <= power_l[k] && power_l[k] <= 100)) &&
        (forall (k : Z),
          (0 <= k && k <= n@pre) =>
            (0 <= prefix_l[k] && prefix_l[k] <= 5000)) &&
        (forall (pending_right : Z),
          (start + len - 1 <= pending_right && pending_right < n@pre) =>
            left_table[start][pending_right] == inf) &&
        (forall (pending_left : Z),
          (0 <= pending_left && pending_left <= start - len + 1) =>
            right_table[pending_left][start] == inf) &&
        StreetlightPrefixProgress(power_l, prefix_l, n@pre) &&
        StreetlightLeftProgress(pos_l, power_l, left_table, right_table,
          n@pre, start, len, left) &&
        IntArray::full(pos, n@pre, pos_l) *
        IntArray::full(power, n@pre, power_l) *
        IntArray::full(pre, n@pre + 1, prefix_l) *
        IntArray2::full(dp_l, n@pre, n@pre, left_table) *
        IntArray2::full(dp_r, n@pre, n@pre, right_table)
     */
    for (int left = first_left; left <= last_left; ++left) {
      int right = left + len - 1;
      /*@ 0 <= left && left <= start && start <= right &&
          right < n@pre && right == left + len - 1 by local */

      if (left < start) {
        int remain = total - (pre[right + 1] - pre[left + 1]);
        /*@ 1 <= remain && remain <= 5000 */
        int best = inf;
        int prev = *(dp_l + (left + 1) * width + right);

        if (prev < inf) {
          /*@ 0 <= prev && prev <= (len - 2) * 40000000 */
          best = prev + (pos[left + 1] - pos[left]) * remain;
          /*@ 0 <= best && best <= (len - 1) * 40000000 */
        }

        prev = *(dp_r + (left + 1) * width + right);
        if (prev < inf) {
          /*@ 0 <= prev && prev <= (len - 2) * 40000000 */
          int cand = prev + (pos[right] - pos[left]) * remain;
          /*@ 0 <= cand && cand <= (len - 1) * 40000000 */
          if (cand < best) {
            best = cand;
          }
        }

        /*@ Assert
            exists prefix_l left_table right_table,
            pos == pos@pre && power == power@pre && n == n@pre &&
            c == c@pre && pre == pre@pre && dp_l == dp_l@pre &&
            dp_r == dp_r@pre && width == n@pre &&
            inf == 2147483647 && start == c@pre - 1 &&
            total == prefix_l[n@pre] &&
            1 <= n@pre && n@pre <= 50 &&
            1 <= c@pre && c@pre <= n@pre &&
            0 <= start && start < n@pre &&
            2 <= len && len <= n@pre &&
            0 <= left && left < start &&
            right == left + len - 1 && start <= right && right < n@pre &&
            1 <= total && total <= 5000 &&
            1 <= remain && remain <= 5000 &&
            remain == total -
              (prefix_l[right + 1] - prefix_l[left + 1]) &&
            prev == right_table[left + 1][right] &&
            ((inf <= left_table[left + 1][right] &&
              inf <= right_table[left + 1][right] && best == inf) ||
             (left_table[left + 1][right] < inf &&
              (inf <= right_table[left + 1][right] ||
               left_table[left + 1][right] +
                 (pos_l[left + 1] - pos_l[left]) * remain <=
               right_table[left + 1][right] +
                 (pos_l[right] - pos_l[left]) * remain) &&
              0 <= best && best <= (len - 1) * 40000000 &&
              best == left_table[left + 1][right] +
                (pos_l[left + 1] - pos_l[left]) * remain) ||
             (right_table[left + 1][right] < inf &&
              (inf <= left_table[left + 1][right] ||
               right_table[left + 1][right] +
                 (pos_l[right] - pos_l[left]) * remain <
               left_table[left + 1][right] +
                 (pos_l[left + 1] - pos_l[left]) * remain) &&
              0 <= best && best <= (len - 1) * 40000000 &&
              best == right_table[left + 1][right] +
                (pos_l[right] - pos_l[left]) * remain)) &&
            (left_table[left + 1][right] < inf =>
              best <= left_table[left + 1][right] +
                (pos_l[left + 1] - pos_l[left]) * remain) &&
            (right_table[left + 1][right] < inf =>
              best <= right_table[left + 1][right] +
                (pos_l[right] - pos_l[left]) * remain) &&
            ((first_left == 0 && start - len + 1 <= 0) ||
             (first_left == start - len + 1 && 0 <= start - len + 1)) &&
            ((last_left == n@pre - len && n@pre < start + len) ||
             (last_left == start && start + len <= n@pre)) &&
            first_left <= left && left <= last_left &&
            Zlength(pos_l) == n@pre && Zlength(power_l) == n@pre &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
                (0 <= pos_l[k] && pos_l[k] <= 8000)) &&
            (forall (k : Z),
              (0 <= k && k + 1 < n@pre) => pos_l[k] < pos_l[k + 1]) &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
                (1 <= power_l[k] && power_l[k] <= 100)) &&
            (forall (k : Z),
              (0 <= k && k <= n@pre) =>
                (0 <= prefix_l[k] && prefix_l[k] <= 5000)) &&
            (forall (pending_right : Z),
              (start + len - 1 <= pending_right &&
               pending_right < n@pre) =>
                left_table[start][pending_right] == inf) &&
            (forall (pending_left : Z),
              (0 <= pending_left &&
               pending_left <= start - len + 1) =>
                right_table[pending_left][start] == inf) &&
            StreetlightPrefixProgress(power_l, prefix_l, n@pre) &&
            StreetlightLeftProgress(pos_l, power_l, left_table, right_table,
              n@pre, start, len, left) &&
            IntArray::full(pos, n@pre, pos_l) *
            IntArray::full(power, n@pre, power_l) *
            IntArray::full(pre, n@pre + 1, prefix_l) *
            IntArray2::full(dp_l, n@pre, n@pre, left_table) *
            IntArray2::full(dp_r, n@pre, n@pre, right_table)
         */
        *(dp_l + left * width + right) = best;
      }

      /*@ Assert
          exists prefix_l left_table right_table,
          pos == pos@pre && power == power@pre && n == n@pre &&
          c == c@pre && pre == pre@pre && dp_l == dp_l@pre &&
          dp_r == dp_r@pre && width == n@pre &&
          inf == 2147483647 && start == c@pre - 1 &&
          total == prefix_l[n@pre] &&
          1 <= n@pre && n@pre <= 50 &&
          1 <= c@pre && c@pre <= n@pre &&
          0 <= start && start < n@pre &&
          2 <= len && len <= n@pre &&
          0 <= left && left <= start &&
          right == left + len - 1 && start <= right && right < n@pre &&
          1 <= total && total <= 5000 &&
          ((first_left == 0 && start - len + 1 <= 0) ||
           (first_left == start - len + 1 && 0 <= start - len + 1)) &&
          ((last_left == n@pre - len && n@pre < start + len) ||
           (last_left == start && start + len <= n@pre)) &&
          first_left <= left && left <= last_left &&
          Zlength(pos_l) == n@pre && Zlength(power_l) == n@pre &&
          (forall (k : Z),
            (0 <= k && k < n@pre) =>
              (0 <= pos_l[k] && pos_l[k] <= 8000)) &&
          (forall (k : Z),
            (0 <= k && k + 1 < n@pre) => pos_l[k] < pos_l[k + 1]) &&
          (forall (k : Z),
            (0 <= k && k < n@pre) =>
              (1 <= power_l[k] && power_l[k] <= 100)) &&
          (forall (k : Z),
            (0 <= k && k <= n@pre) =>
              (0 <= prefix_l[k] && prefix_l[k] <= 5000)) &&
          (forall (pending_right : Z),
            (start + len - 1 <= pending_right &&
             pending_right < n@pre) =>
              left_table[start][pending_right] == inf) &&
          (forall (pending_left : Z),
            (0 <= pending_left &&
             pending_left <= start - len + 1) =>
              right_table[pending_left][start] == inf) &&
          (left == start => left_table[left][right] == inf) &&
          (right == start => right_table[left][right] == inf) &&
          StreetlightPrefixProgress(power_l, prefix_l, n@pre) &&
          StreetlightLeftEndpointReady(pos_l, power_l,
            left_table, right_table, n@pre, start, len, left) &&
          IntArray::full(pos, n@pre, pos_l) *
          IntArray::full(power, n@pre, power_l) *
          IntArray::full(pre, n@pre + 1, prefix_l) *
          IntArray2::full(dp_l, n@pre, n@pre, left_table) *
          IntArray2::full(dp_r, n@pre, n@pre, right_table)
       */
      if (right > start) {
        int remain = total - (pre[right] - pre[left]);
        /*@ 1 <= remain && remain <= 5000 */
        int best = inf;
        int prev = *(dp_l + left * width + (right - 1));

        if (prev < inf) {
          /*@ 0 <= prev && prev <= (len - 2) * 40000000 */
          best = prev + (pos[right] - pos[left]) * remain;
          /*@ 0 <= best && best <= (len - 1) * 40000000 */
        }

        prev = *(dp_r + left * width + (right - 1));
        if (prev < inf) {
          /*@ 0 <= prev && prev <= (len - 2) * 40000000 */
          int cand = prev + (pos[right] - pos[right - 1]) * remain;
          /*@ 0 <= cand && cand <= (len - 1) * 40000000 */
          if (cand < best) {
            best = cand;
          }
        }

        /*@ Assert
            exists prefix_l left_table right_table,
            pos == pos@pre && power == power@pre && n == n@pre &&
            c == c@pre && pre == pre@pre && dp_l == dp_l@pre &&
            dp_r == dp_r@pre && width == n@pre &&
            inf == 2147483647 && start == c@pre - 1 &&
            total == prefix_l[n@pre] &&
            1 <= n@pre && n@pre <= 50 &&
            1 <= c@pre && c@pre <= n@pre &&
            0 <= start && start < n@pre &&
            2 <= len && len <= n@pre &&
            0 <= left && left <= start &&
            right == left + len - 1 && start < right && right < n@pre &&
            1 <= total && total <= 5000 &&
            1 <= remain && remain <= 5000 &&
            remain == total -
              (prefix_l[right] - prefix_l[left]) &&
            prev == right_table[left][right - 1] &&
            ((left_table[left][right - 1] == inf &&
              right_table[left][right - 1] == inf && best == inf) ||
             (left_table[left][right - 1] < inf &&
              0 <= best && best <= (len - 1) * 40000000 &&
              best == left_table[left][right - 1] +
                (pos_l[right] - pos_l[left]) * remain) ||
             (right_table[left][right - 1] < inf &&
              0 <= best && best <= (len - 1) * 40000000 &&
              best == right_table[left][right - 1] +
                (pos_l[right] - pos_l[right - 1]) * remain)) &&
            (left_table[left][right - 1] < inf =>
              best <= left_table[left][right - 1] +
                (pos_l[right] - pos_l[left]) * remain) &&
            (right_table[left][right - 1] < inf =>
              best <= right_table[left][right - 1] +
                (pos_l[right] - pos_l[right - 1]) * remain) &&
            ((first_left == 0 && start - len + 1 <= 0) ||
             (first_left == start - len + 1 && 0 <= start - len + 1)) &&
            ((last_left == n@pre - len && n@pre < start + len) ||
             (last_left == start && start + len <= n@pre)) &&
            first_left <= left && left <= last_left &&
            Zlength(pos_l) == n@pre && Zlength(power_l) == n@pre &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
                (0 <= pos_l[k] && pos_l[k] <= 8000)) &&
            (forall (k : Z),
              (0 <= k && k + 1 < n@pre) => pos_l[k] < pos_l[k + 1]) &&
            (forall (k : Z),
              (0 <= k && k < n@pre) =>
                (1 <= power_l[k] && power_l[k] <= 100)) &&
            (forall (k : Z),
              (0 <= k && k <= n@pre) =>
                (0 <= prefix_l[k] && prefix_l[k] <= 5000)) &&
            (forall (pending_right : Z),
              (start + len - 1 <= pending_right &&
               pending_right < n@pre) =>
                left_table[start][pending_right] == inf) &&
            (forall (pending_left : Z),
              (0 <= pending_left &&
               pending_left <= start - len + 1) =>
                right_table[pending_left][start] == inf) &&
            StreetlightPrefixProgress(power_l, prefix_l, n@pre) &&
            StreetlightLeftEndpointReady(pos_l, power_l,
              left_table, right_table, n@pre, start, len, left) &&
            IntArray::full(pos, n@pre, pos_l) *
            IntArray::full(power, n@pre, power_l) *
            IntArray::full(pre, n@pre + 1, prefix_l) *
            IntArray2::full(dp_l, n@pre, n@pre, left_table) *
            IntArray2::full(dp_r, n@pre, n@pre, right_table)
         */
        *(dp_r + left * width + right) = best;
      }
    }
  }

  int ans_l = *(dp_l + 0 * width + (n - 1));
  int ans_r = *(dp_r + 0 * width + (n - 1));
  /*@ Assert
      exists prefix_l left_table right_table,
      pos == pos@pre && power == power@pre && n == n@pre &&
      c == c@pre && pre == pre@pre && dp_l == dp_l@pre &&
      dp_r == dp_r@pre && width == n@pre &&
      inf == 2147483647 && start == c@pre - 1 &&
      total == prefix_l[n@pre] && 1 <= total && total <= 5000 &&
      1 <= n@pre && n@pre <= 50 &&
      1 <= c@pre && c@pre <= n@pre &&
      0 <= start && start < n@pre &&
      ans_l == left_table[0][n@pre - 1] &&
      ans_r == right_table[0][n@pre - 1] &&
      (ans_l == inf || (0 <= ans_l && ans_l <= 1960000000)) &&
      (ans_r == inf || (0 <= ans_r && ans_r <= 1960000000)) &&
      (ans_l < inf || ans_r < inf) &&
      StreetlightFinalCandidates(pos_l, power_l, left_table, right_table,
        start, ans_l, ans_r) &&
      IntArray::full(pos, n@pre, pos_l) *
      IntArray::full(power, n@pre, power_l) *
      IntArray::full(pre, n@pre + 1, prefix_l) *
      IntArray2::full(dp_l, n@pre, n@pre, left_table) *
      IntArray2::full(dp_r, n@pre, n@pre, right_table)
   */
  if (ans_l < ans_r) {
    return ans_l;
  }
  return ans_r;
}
