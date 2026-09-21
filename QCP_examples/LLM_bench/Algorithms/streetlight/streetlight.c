#include "verification_stdlib.h"
#include "verification_list.h"
#include "array2_def.h"

/*@ Extern Coq
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (map : {A B} -> (A -> B) -> list A -> list B)
      (eq : {A} -> A -> A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (Z::max : Z -> Z -> Z)
      (Z::min : Z -> Z -> Z)
      (StreetlightRowLength : list Z -> Z)
      (StreetlightTourMinimumEnergy : list Z -> list Z -> Z -> Z -> Prop)
      (StreetlightPrefixProgress : list Z -> list Z -> Z -> Prop)
      (StreetlightInfRows : list (list Z) -> Z -> Z -> Prop)
      (StreetlightInfProgress : list (list Z) -> Z -> Z -> Z -> Prop)
      (StreetlightLengthsDone : list Z -> list Z -> list (list Z) -> list (list Z) -> Z -> Z -> Z -> Prop)
      (StreetlightLeftProgress : list Z -> list Z -> list (list Z) -> list (list Z) -> Z -> Z -> Z -> Z -> Prop)
      (StreetlightLeftEndpointReady : list Z -> list Z -> list (list Z) -> list (list Z) -> Z -> Z -> Z -> Z -> Prop)
      (StreetlightFinalCandidates : list Z -> list Z -> list (list Z) -> list (list Z) -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.streetlight.streetlight_lib */

int solve(int *pos, int *power, int n, int c)
/*@ With (pos_l power_l : list Z)
         
    Require
      1 <= n && n <= 50 &&
      1 <= c && c <= n &&
      Zlength(pos_l) == n &&
      Zlength(power_l) == n &&
      Forall(Z::le(1), pos_l) && Forall(Z::ge(100), pos_l) &&
      (forall (i : Z),
        (0 <= i && i + 1 < n) => pos_l[i] < pos_l[i + 1]) &&
      Forall(Z::le(1), power_l) && Forall(Z::ge(100), power_l) &&
      IntArray::full(pos, n, pos_l) *
      IntArray::full(power, n, power_l)
    Ensure
      StreetlightTourMinimumEnergy(pos_l, power_l, c - 1, __return) &&
      IntArray::full(pos, n, pos_l) *
      IntArray::full(power, n, power_l)
 */
{
  int pre[51];
  int dp_l[2500];
  int dp_r[2500];
  /*@ Inv Assert
      exists dp_l_flat dp_r_flat,
      pos == pos@pre && power == power@pre && n == n@pre && c == c@pre &&
      0 <= k && k <= n@pre * n@pre &&
      1 <= n@pre && n@pre <= 50 &&
      1 <= c@pre && c@pre <= n@pre &&
      Zlength(pos_l) == n@pre &&
      Zlength(power_l) == n@pre &&
      Forall(Z::le(1), pos_l) && Forall(Z::ge(100), pos_l) &&
      (forall (i : Z),
        (0 <= i && i + 1 < n@pre) => pos_l[i] < pos_l[i + 1]) &&
      Forall(Z::le(1), power_l) && Forall(Z::ge(100), power_l) &&
      IntArray::full(pos@pre, n@pre, pos_l) *
      IntArray::full(power@pre, n@pre, power_l) *
      IntArray::undef_full(pre, 51) *
      IntArray::seg(dp_l, 0, k, dp_l_flat) *
      IntArray::undef_seg(dp_l, k, 2500) *
      IntArray::seg(dp_r, 0, k, dp_r_flat) *
      IntArray::undef_seg(dp_r, k, 2500)
   */
  for (int k = 0; k < n * n; ++k) {
    dp_l[k] = 0;
    dp_r[k] = 0;
  }



  int width = n;
  int inf = 2147483647;
  int start = c - 1;

  pre[0] = 0;
  /*@ Inv Assert
      exists prefix_l dp_l_init dp_r_init,
      pos == pos@pre && power == power@pre && n == n@pre &&
      c == c@pre &&  
       width == n@pre &&
      inf == 2147483647 && start == c@pre - 1 &&
      1 <= n@pre && n@pre <= 50 &&
      1 <= c@pre && c@pre <= n@pre &&
      0 <= i && i <= n@pre &&
      Zlength(pos_l) == n@pre && Zlength(power_l) == n@pre &&
      Forall(Z::le(0), pos_l) && Forall(Z::ge(8000), pos_l) &&
      (forall (k : Z),
        (0 <= k && k + 1 < n@pre) => pos_l[k] < pos_l[k + 1]) &&
      Forall(Z::le(1), power_l) && Forall(Z::ge(100), power_l) &&
      Forall(Z::le(0), prefix_l) && Forall(Z::ge(5000), prefix_l) &&
      StreetlightPrefixProgress(power_l, prefix_l, i) &&
      Zlength(prefix_l) == i + 1 &&
      IntArray::full(pos, n@pre, pos_l) *
      IntArray::full(power, n@pre, power_l) *
      IntArray::seg(pre, 0, i + 1, prefix_l) *
      IntArray::undef_seg(pre, i + 1, n@pre + 1) *
      IntArray2::full(dp_l, n@pre, n@pre, dp_l_init) *
      IntArray2::full(dp_r, n@pre, n@pre, dp_r_init) *
      IntArray::undef_seg(pre, n@pre + 1, 51) *
      IntArray::undef_seg(dp_l, n@pre * n@pre, 2500) *
      IntArray::undef_seg(dp_r, n@pre * n@pre, 2500)
   */
  for (int i = 0; i < n; ++i) {
    pre[i + 1] = pre[i] + power[i];
  }
  int total = pre[n];

  /*@ Inv Assert
      exists prefix_l left_table right_table,
      pos == pos@pre && power == power@pre && n == n@pre &&
      c == c@pre &&  
       width == n@pre &&
      inf == 2147483647 && start == c@pre - 1 &&
      total == prefix_l[n@pre] &&
      1 <= n@pre && n@pre <= 50 &&
      1 <= c@pre && c@pre <= n@pre &&
      0 <= row && row <= n@pre &&
      1 <= total && total <= 5000 &&
      Zlength(pos_l) == n@pre && Zlength(power_l) == n@pre &&
      Forall(Z::le(0), pos_l) && Forall(Z::ge(8000), pos_l) &&
      (forall (k : Z),
        (0 <= k && k + 1 < n@pre) => pos_l[k] < pos_l[k + 1]) &&
      Forall(Z::le(1), power_l) && Forall(Z::ge(100), power_l) &&
      Forall(Z::le(0), prefix_l) && Forall(Z::ge(5000), prefix_l) &&
      StreetlightPrefixProgress(power_l, prefix_l, n@pre) &&
      Zlength(prefix_l) == n@pre + 1 &&
      StreetlightInfRows(left_table, n@pre, row) &&
      Zlength(left_table) == n@pre &&
      Forall(eq(n@pre), map(StreetlightRowLength, left_table)) &&
      StreetlightInfRows(right_table, n@pre, row) &&
      Zlength(right_table) == n@pre &&
      Forall(eq(n@pre), map(StreetlightRowLength, right_table)) &&
      IntArray::full(pos, n@pre, pos_l) *
      IntArray::full(power, n@pre, power_l) *
      IntArray::full(pre, n@pre + 1, prefix_l) *
      IntArray2::full(dp_l, n@pre, n@pre, left_table) *
      IntArray2::full(dp_r, n@pre, n@pre, right_table) *
      IntArray::undef_seg(pre, n@pre + 1, 51) *
      IntArray::undef_seg(dp_l, n@pre * n@pre, 2500) *
      IntArray::undef_seg(dp_r, n@pre * n@pre, 2500)
   */
  for (int row = 0; row < n; ++row) {
    /*@ Inv Assert
        exists prefix_l left_table right_table,
        pos == pos@pre && power == power@pre && n == n@pre &&
        c == c@pre &&  
         width == n@pre &&
        inf == 2147483647 && start == c@pre - 1 &&
        total == prefix_l[n@pre] &&
        1 <= n@pre && n@pre <= 50 &&
        1 <= c@pre && c@pre <= n@pre &&
        0 <= row && row < n@pre &&
        0 <= col && col <= n@pre &&
        1 <= total && total <= 5000 &&
        Zlength(pos_l) == n@pre && Zlength(power_l) == n@pre &&
        Forall(Z::le(0), pos_l) && Forall(Z::ge(8000), pos_l) &&
        (forall (k : Z),
          (0 <= k && k + 1 < n@pre) => pos_l[k] < pos_l[k + 1]) &&
        Forall(Z::le(1), power_l) && Forall(Z::ge(100), power_l) &&
        Forall(Z::le(0), prefix_l) && Forall(Z::ge(5000), prefix_l) &&
        StreetlightPrefixProgress(power_l, prefix_l, n@pre) &&
      Zlength(prefix_l) == n@pre + 1 &&
        StreetlightInfProgress(left_table, n@pre, row, col) &&
      Zlength(left_table) == n@pre &&
      Forall(eq(n@pre), map(StreetlightRowLength, left_table)) &&
        StreetlightInfProgress(right_table, n@pre, row, col) &&
      Zlength(right_table) == n@pre &&
      Forall(eq(n@pre), map(StreetlightRowLength, right_table)) &&
        IntArray::full(pos, n@pre, pos_l) *
        IntArray::full(power, n@pre, power_l) *
        IntArray::full(pre, n@pre + 1, prefix_l) *
        IntArray2::full(dp_l, n@pre, n@pre, left_table) *
        IntArray2::full(dp_r, n@pre, n@pre, right_table) *
      IntArray::undef_seg(pre, n@pre + 1, 51) *
      IntArray::undef_seg(dp_l, n@pre * n@pre, 2500) *
      IntArray::undef_seg(dp_r, n@pre * n@pre, 2500)
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
      c == c@pre &&  
       width == n@pre &&
      inf == 2147483647 && start == c@pre - 1 &&
      total == prefix_l[n@pre] &&
      1 <= n@pre && n@pre <= 50 &&
      1 <= c@pre && c@pre <= n@pre &&
      0 <= start && start < n@pre &&
      2 <= len && len <= n@pre + 1 &&
      1 <= total && total <= 5000 &&
      Zlength(pos_l) == n@pre && Zlength(power_l) == n@pre &&
      Forall(Z::le(0), pos_l) && Forall(Z::ge(8000), pos_l) &&
      (forall (k : Z),
        (0 <= k && k + 1 < n@pre) => pos_l[k] < pos_l[k + 1]) &&
      Forall(Z::le(1), power_l) && Forall(Z::ge(100), power_l) &&
      Forall(Z::le(0), prefix_l) && Forall(Z::ge(5000), prefix_l) &&
      (forall (pending_right : Z),
        (start + len - 1 <= pending_right && pending_right < n@pre) =>
          left_table[start][pending_right] == inf) &&
      (forall (pending_left : Z),
        (0 <= pending_left && pending_left <= start - len + 1) =>
          right_table[pending_left][start] == inf) &&
      StreetlightPrefixProgress(power_l, prefix_l, n@pre) &&
      Zlength(prefix_l) == n@pre + 1 &&
      StreetlightLengthsDone(pos_l, power_l, left_table, right_table,
        n@pre, start, len) &&
      Zlength(left_table) == n@pre &&
      Forall(eq(n@pre), map(StreetlightRowLength, left_table)) &&
      Zlength(right_table) == n@pre &&
      Forall(eq(n@pre), map(StreetlightRowLength, right_table)) &&
      IntArray::full(pos, n@pre, pos_l) *
      IntArray::full(power, n@pre, power_l) *
      IntArray::full(pre, n@pre + 1, prefix_l) *
      IntArray2::full(dp_l, n@pre, n@pre, left_table) *
      IntArray2::full(dp_r, n@pre, n@pre, right_table) *
      IntArray::undef_seg(pre, n@pre + 1, 51) *
      IntArray::undef_seg(dp_l, n@pre * n@pre, 2500) *
      IntArray::undef_seg(dp_r, n@pre * n@pre, 2500)
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
        c == c@pre &&  
         width == n@pre &&
        inf == 2147483647 && start == c@pre - 1 &&
        total == prefix_l[n@pre] &&
        1 <= n@pre && n@pre <= 50 &&
        1 <= c@pre && c@pre <= n@pre &&
        0 <= start && start < n@pre &&
        2 <= len && len <= n@pre &&
        1 <= total && total <= 5000 &&
        first_left == Z::max(0, start - len + 1) &&
        last_left == Z::min(n@pre - len, start) &&
        0 <= first_left && first_left <= last_left &&
        first_left <= left && left <= last_left + 1 &&
        Zlength(pos_l) == n@pre && Zlength(power_l) == n@pre &&
        Forall(Z::le(0), pos_l) && Forall(Z::ge(8000), pos_l) &&
        (forall (k : Z),
          (0 <= k && k + 1 < n@pre) => pos_l[k] < pos_l[k + 1]) &&
        Forall(Z::le(1), power_l) && Forall(Z::ge(100), power_l) &&
        Forall(Z::le(0), prefix_l) && Forall(Z::ge(5000), prefix_l) &&
        (forall (pending_right : Z),
          (start + len - 1 <= pending_right && pending_right < n@pre) =>
            left_table[start][pending_right] == inf) &&
        (forall (pending_left : Z),
          (0 <= pending_left && pending_left <= start - len + 1) =>
            right_table[pending_left][start] == inf) &&
        StreetlightPrefixProgress(power_l, prefix_l, n@pre) &&
      Zlength(prefix_l) == n@pre + 1 &&
        StreetlightLeftProgress(pos_l, power_l, left_table, right_table,
          n@pre, start, len, left) &&
      Zlength(left_table) == n@pre &&
      Forall(eq(n@pre), map(StreetlightRowLength, left_table)) &&
      Zlength(right_table) == n@pre &&
      Forall(eq(n@pre), map(StreetlightRowLength, right_table)) &&
        IntArray::full(pos, n@pre, pos_l) *
        IntArray::full(power, n@pre, power_l) *
        IntArray::full(pre, n@pre + 1, prefix_l) *
        IntArray2::full(dp_l, n@pre, n@pre, left_table) *
        IntArray2::full(dp_r, n@pre, n@pre, right_table) *
      IntArray::undef_seg(pre, n@pre + 1, 51) *
      IntArray::undef_seg(dp_l, n@pre * n@pre, 2500) *
      IntArray::undef_seg(dp_r, n@pre * n@pre, 2500)
   */
    for (int left = first_left; left <= last_left; ++left) {
      int right = left + len - 1;
      /*@ 0 <= left && left <= start && start <= right &&
          right < n@pre && right == left + len - 1 by local */

      if (left < start) {
        int remain = total - (pre[right + 1] - pre[left + 1]);

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
            c == c@pre &&  
             width == n@pre &&
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
            first_left == Z::max(0, start - len + 1) &&
            last_left == Z::min(n@pre - len, start) &&
            first_left <= left && left <= last_left &&
            Zlength(pos_l) == n@pre && Zlength(power_l) == n@pre &&
            Forall(Z::le(0), pos_l) && Forall(Z::ge(8000), pos_l) &&
            (forall (k : Z),
              (0 <= k && k + 1 < n@pre) => pos_l[k] < pos_l[k + 1]) &&
            Forall(Z::le(1), power_l) && Forall(Z::ge(100), power_l) &&
            Forall(Z::le(0), prefix_l) && Forall(Z::ge(5000), prefix_l) &&
            (forall (pending_right : Z),
              (start + len - 1 <= pending_right &&
               pending_right < n@pre) =>
                left_table[start][pending_right] == inf) &&
            (forall (pending_left : Z),
              (0 <= pending_left &&
               pending_left <= start - len + 1) =>
                right_table[pending_left][start] == inf) &&
            StreetlightPrefixProgress(power_l, prefix_l, n@pre) &&
      Zlength(prefix_l) == n@pre + 1 &&
            StreetlightLeftProgress(pos_l, power_l, left_table, right_table,
              n@pre, start, len, left) &&
      Zlength(left_table) == n@pre &&
      Forall(eq(n@pre), map(StreetlightRowLength, left_table)) &&
      Zlength(right_table) == n@pre &&
      Forall(eq(n@pre), map(StreetlightRowLength, right_table)) &&
            IntArray::full(pos, n@pre, pos_l) *
            IntArray::full(power, n@pre, power_l) *
            IntArray::full(pre, n@pre + 1, prefix_l) *
            IntArray2::full(dp_l, n@pre, n@pre, left_table) *
            IntArray2::full(dp_r, n@pre, n@pre, right_table) *
      IntArray::undef_seg(pre, n@pre + 1, 51) *
      IntArray::undef_seg(dp_l, n@pre * n@pre, 2500) *
      IntArray::undef_seg(dp_r, n@pre * n@pre, 2500)
   */
        *(dp_l + left * width + right) = best;
      }

      /*@ Assert
          exists prefix_l left_table right_table,
          pos == pos@pre && power == power@pre && n == n@pre &&
          c == c@pre &&  
           width == n@pre &&
          inf == 2147483647 && start == c@pre - 1 &&
          total == prefix_l[n@pre] &&
          1 <= n@pre && n@pre <= 50 &&
          1 <= c@pre && c@pre <= n@pre &&
          0 <= start && start < n@pre &&
          2 <= len && len <= n@pre &&
          0 <= left && left <= start &&
          right == left + len - 1 && start <= right && right < n@pre &&
          1 <= total && total <= 5000 &&
          first_left == Z::max(0, start - len + 1) &&
          last_left == Z::min(n@pre - len, start) &&
          first_left <= left && left <= last_left &&
          Zlength(pos_l) == n@pre && Zlength(power_l) == n@pre &&
          Forall(Z::le(0), pos_l) && Forall(Z::ge(8000), pos_l) &&
          (forall (k : Z),
            (0 <= k && k + 1 < n@pre) => pos_l[k] < pos_l[k + 1]) &&
          Forall(Z::le(1), power_l) && Forall(Z::ge(100), power_l) &&
          Forall(Z::le(0), prefix_l) && Forall(Z::ge(5000), prefix_l) &&
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
      Zlength(prefix_l) == n@pre + 1 &&
          StreetlightLeftEndpointReady(pos_l, power_l,
            left_table, right_table, n@pre, start, len, left) &&
      Zlength(left_table) == n@pre &&
      Forall(eq(n@pre), map(StreetlightRowLength, left_table)) &&
      Zlength(right_table) == n@pre &&
      Forall(eq(n@pre), map(StreetlightRowLength, right_table)) &&
          IntArray::full(pos, n@pre, pos_l) *
          IntArray::full(power, n@pre, power_l) *
          IntArray::full(pre, n@pre + 1, prefix_l) *
          IntArray2::full(dp_l, n@pre, n@pre, left_table) *
          IntArray2::full(dp_r, n@pre, n@pre, right_table) *
      IntArray::undef_seg(pre, n@pre + 1, 51) *
      IntArray::undef_seg(dp_l, n@pre * n@pre, 2500) *
      IntArray::undef_seg(dp_r, n@pre * n@pre, 2500)
   */
      if (right > start) {
        int remain = total - (pre[right] - pre[left]);

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
            c == c@pre &&  
             width == n@pre &&
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
            first_left == Z::max(0, start - len + 1) &&
            last_left == Z::min(n@pre - len, start) &&
            first_left <= left && left <= last_left &&
            Zlength(pos_l) == n@pre && Zlength(power_l) == n@pre &&
            Forall(Z::le(0), pos_l) && Forall(Z::ge(8000), pos_l) &&
            (forall (k : Z),
              (0 <= k && k + 1 < n@pre) => pos_l[k] < pos_l[k + 1]) &&
            Forall(Z::le(1), power_l) && Forall(Z::ge(100), power_l) &&
            Forall(Z::le(0), prefix_l) && Forall(Z::ge(5000), prefix_l) &&
            (forall (pending_right : Z),
              (start + len - 1 <= pending_right &&
               pending_right < n@pre) =>
                left_table[start][pending_right] == inf) &&
            (forall (pending_left : Z),
              (0 <= pending_left &&
               pending_left <= start - len + 1) =>
                right_table[pending_left][start] == inf) &&
            StreetlightPrefixProgress(power_l, prefix_l, n@pre) &&
      Zlength(prefix_l) == n@pre + 1 &&
            StreetlightLeftEndpointReady(pos_l, power_l,
              left_table, right_table, n@pre, start, len, left) &&
      Zlength(left_table) == n@pre &&
      Forall(eq(n@pre), map(StreetlightRowLength, left_table)) &&
      Zlength(right_table) == n@pre &&
      Forall(eq(n@pre), map(StreetlightRowLength, right_table)) &&
            IntArray::full(pos, n@pre, pos_l) *
            IntArray::full(power, n@pre, power_l) *
            IntArray::full(pre, n@pre + 1, prefix_l) *
            IntArray2::full(dp_l, n@pre, n@pre, left_table) *
            IntArray2::full(dp_r, n@pre, n@pre, right_table) *
      IntArray::undef_seg(pre, n@pre + 1, 51) *
      IntArray::undef_seg(dp_l, n@pre * n@pre, 2500) *
      IntArray::undef_seg(dp_r, n@pre * n@pre, 2500)
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
      c == c@pre &&  
       width == n@pre &&
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
      Zlength(pos_l) == n@pre &&
      Zlength(power_l) == n@pre &&
      (forall (k : Z),
        (0 <= k && k + 1 < n@pre) => pos_l[k] < pos_l[k + 1]) &&
      Forall(Z::le(1), power_l) && Forall(Z::ge(100), power_l) &&
      IntArray::full(pos, n@pre, pos_l) *
      IntArray::full(power, n@pre, power_l) *
      IntArray::full(pre, n@pre + 1, prefix_l) *
      IntArray2::full(dp_l, n@pre, n@pre, left_table) *
      IntArray2::full(dp_r, n@pre, n@pre, right_table) *
      IntArray::undef_seg(pre, n@pre + 1, 51) *
      IntArray::undef_seg(dp_l, n@pre * n@pre, 2500) *
      IntArray::undef_seg(dp_r, n@pre * n@pre, 2500)
   */
  if (ans_l < ans_r) {
    /*@ Assert
      pos == pos@pre && power == power@pre && n == n@pre && c == c@pre &&
      StreetlightTourMinimumEnergy(pos_l, power_l, c@pre - 1, ans_l) &&
      width == n@pre && inf == 2147483647 && start == c@pre - 1 &&
      1 <= total && total <= 5000 && 0 <= ans_r && ans_r <= 2147483647 &&
      IntArray::full(pos, n@pre, pos_l) *
      IntArray::full(power, n@pre, power_l) *
      IntArray::undef_full(pre, 51) *
      IntArray::undef_full(dp_l, 2500) *
      IntArray::undef_full(dp_r, 2500)
   */
    return ans_l;
  }
  /*@ Assert
      pos == pos@pre && power == power@pre && n == n@pre && c == c@pre &&
      StreetlightTourMinimumEnergy(pos_l, power_l, c@pre - 1, ans_r) &&
      width == n@pre && inf == 2147483647 && start == c@pre - 1 &&
      1 <= total && total <= 5000 && 0 <= ans_l && ans_l <= 2147483647 &&
      IntArray::full(pos, n@pre, pos_l) *
      IntArray::full(power, n@pre, power_l) *
      IntArray::undef_full(pre, 51) *
      IntArray::undef_full(dp_l, 2500) *
      IntArray::undef_full(dp_r, 2500)
   */
    return ans_r;
}
