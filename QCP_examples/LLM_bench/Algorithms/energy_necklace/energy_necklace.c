



/*@ Extern Coq
      (EnergyValsDuplicated : list Z -> list Z -> Z -> Prop)
      (EnergyLabelsBounded : list Z -> Z -> Prop)
      (EnergyComputationBounded : list Z -> Z -> Z -> Prop)
      (EnergyIntervalBest : list Z -> Z -> Z -> Z -> Prop)
      (EnergyNecklaceAnswer : list Z -> Z -> Z -> Prop)
      (EnergyZeroTable : list Z -> Z -> Z -> Prop)
      (EnergyLenDone : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (EnergyLeftProgress : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (EnergySplitProgress : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (EnergyUpdatedCell : list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (EnergyAnswerProgress : list Z -> list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_lib */

int energyNecklace(int *beads, int n, int *vals, int *dp)
/*@ With (beads_l : list Z)
    Require
      4 <= n && n <= 100 &&
      Zlength(beads_l) == n &&
      EnergyLabelsBounded(beads_l, n) &&
      EnergyComputationBounded(beads_l, n, 2100000000) &&
      IntArray::full(beads, n, beads_l) *
      IntArray::undef_full(vals, 2 * n) *
      IntArray::undef_full(dp, (2 * n) * (2 * n))
    Ensure
      exists vals_l dp_l,
      EnergyValsDuplicated(beads_l, vals_l, n) &&
      EnergyLenDone(vals_l, dp_l, 2 * n, 2 * n, n + 1) &&
      EnergyNecklaceAnswer(beads_l, n, __return) &&
      0 <= __return && __return <= 2100000000 &&
      IntArray::full(beads, n, beads_l) *
      IntArray::full(vals, 2 * n, vals_l) *
      IntArray::full(dp, (2 * n) * (2 * n), dp_l)
 */
{
  int total = 2 * n;
  int width = total;

  /*@ Assert
      beads == beads@pre && vals == vals@pre && dp == dp@pre &&
      n == n@pre &&
      total == 2 * n@pre &&
      width == total &&
      4 <= n@pre && n@pre <= 100 &&
      8 <= total && total <= 200 &&
      Zlength(beads_l) == n@pre &&
      EnergyLabelsBounded(beads_l, n@pre) &&
      EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
      IntArray::full(beads, n@pre, beads_l) *
      IntArray::undef_full(vals, total) *
      IntArray::undef_full(dp, total * width)
   */
  /*@ Inv Assert
      exists vals_l,
      beads == beads@pre && vals == vals@pre && dp == dp@pre &&
      n == n@pre &&
      total == 2 * n@pre &&
      width == total &&
      4 <= n@pre && n@pre <= 100 &&
      8 <= total && total <= 200 &&
      Zlength(beads_l) == n@pre &&
      Zlength(vals_l) == i &&
      0 <= i && i <= n@pre &&
      (forall (k : Z), (0 <= k && k < i) => (vals_l[k] == beads_l[k])) &&
      EnergyLabelsBounded(beads_l, n@pre) &&
      EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
      IntArray::full(beads, n@pre, beads_l) *
      IntArray::seg(vals, 0, i, vals_l) *
      IntArray::undef_seg(vals, i, total) *
      IntArray::undef_full(dp, total * width)
   */
  for (int i = 0; i < n; ++i) {
    vals[i] = beads[i];
  }

  /*@ Assert
      exists vals_l,
      beads == beads@pre && vals == vals@pre && dp == dp@pre &&
      n == n@pre &&
      total == 2 * n@pre &&
      width == total &&
      4 <= n@pre && n@pre <= 100 &&
      8 <= total && total <= 200 &&
      Zlength(beads_l) == n@pre &&
      Zlength(vals_l) == n@pre &&
      (forall (k : Z), (0 <= k && k < n@pre) => (vals_l[k] == beads_l[k])) &&
      EnergyLabelsBounded(beads_l, n@pre) &&
      EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
      IntArray::full(beads, n@pre, beads_l) *
      IntArray::seg(vals, 0, n@pre, vals_l) *
      IntArray::undef_seg(vals, n@pre, total) *
      IntArray::undef_full(dp, total * width)
   */
  /*@ Inv Assert
      exists vals_l,
      beads == beads@pre && vals == vals@pre && dp == dp@pre &&
      n == n@pre &&
      total == 2 * n@pre &&
      width == total &&
      4 <= n@pre && n@pre <= 100 &&
      8 <= total && total <= 200 &&
      Zlength(beads_l) == n@pre &&
      Zlength(vals_l) == n@pre + i &&
      0 <= i && i <= n@pre &&
      (forall (k : Z), (0 <= k && k < n@pre) => (vals_l[k] == beads_l[k])) &&
      (forall (k : Z), (0 <= k && k < i) => (vals_l[n@pre + k] == beads_l[k])) &&
      EnergyLabelsBounded(beads_l, n@pre) &&
      EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
      IntArray::full(beads, n@pre, beads_l) *
      IntArray::seg(vals, 0, n@pre + i, vals_l) *
      IntArray::undef_seg(vals, n@pre + i, total) *
      IntArray::undef_full(dp, total * width)
   */
  for (int i = 0; i < n; ++i) {
    vals[n + i] = beads[i];
  }

  /*@ Assert
      exists vals_l,
      beads == beads@pre && vals == vals@pre && dp == dp@pre &&
      n == n@pre &&
      total == 2 * n@pre &&
      width == total &&
      4 <= n@pre && n@pre <= 100 &&
      8 <= total && total <= 200 &&
      Zlength(beads_l) == n@pre &&
      EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
      EnergyLabelsBounded(beads_l, n@pre) &&
      EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
      IntArray::full(beads, n@pre, beads_l) *
      IntArray::full(vals, total, vals_l) *
      IntArray::undef_full(dp, total * width)
   */
  /*@ Inv Assert
      exists vals_l dp_l,
      beads == beads@pre && vals == vals@pre && dp == dp@pre &&
      n == n@pre &&
      total == 2 * n@pre &&
      width == total &&
      4 <= n@pre && n@pre <= 100 &&
      8 <= total && total <= 200 &&
      Zlength(beads_l) == n@pre &&
      Zlength(dp_l) == i &&
      0 <= i && i <= total * width &&
      (forall (k : Z), (0 <= k && k < i) => (dp_l[k] == 0)) &&
      EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
      EnergyLabelsBounded(beads_l, n@pre) &&
      EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
      IntArray::full(beads, n@pre, beads_l) *
      IntArray::full(vals, total, vals_l) *
      IntArray::seg(dp, 0, i, dp_l) *
      IntArray::undef_seg(dp, i, total * width)
   */
  for (int i = 0; i < total * width; ++i) {
    dp[i] = 0;
  }

  /*@ Assert
      exists vals_l dp_l,
      beads == beads@pre && vals == vals@pre && dp == dp@pre &&
      n == n@pre &&
      total == 2 * n@pre &&
      width == total &&
      4 <= n@pre && n@pre <= 100 &&
      8 <= total && total <= 200 &&
      Zlength(beads_l) == n@pre &&
      Zlength(dp_l) == total * width &&
      EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
      EnergyZeroTable(dp_l, total, width) &&
      EnergyLenDone(vals_l, dp_l, total, width, 2) &&
      EnergyLabelsBounded(beads_l, n@pre) &&
      EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
      IntArray::full(beads, n@pre, beads_l) *
      IntArray::full(vals, total, vals_l) *
      IntArray::full(dp, total * width, dp_l)
   */
  /*@ Inv Assert
      exists vals_l dp_l,
      beads == beads@pre && vals == vals@pre && dp == dp@pre &&
      n == n@pre &&
      total == 2 * n@pre &&
      width == total &&
      4 <= n@pre && n@pre <= 100 &&
      8 <= total && total <= 200 &&
      2 <= len && len <= n@pre + 1 &&
      Zlength(beads_l) == n@pre &&
      Zlength(dp_l) == total * width &&
      EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
      EnergyLenDone(vals_l, dp_l, total, width, len) &&
      EnergyLabelsBounded(beads_l, n@pre) &&
      EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
      IntArray::full(beads, n@pre, beads_l) *
      IntArray::full(vals, total, vals_l) *
      IntArray::full(dp, total * width, dp_l)
   */
  for (int len = 2; len <= n; ++len) {
    /*@ Inv Assert
        exists vals_l dp_l,
        beads == beads@pre && vals == vals@pre && dp == dp@pre &&
        n == n@pre &&
        total == 2 * n@pre &&
        width == total &&
        4 <= n@pre && n@pre <= 100 &&
        8 <= total && total <= 200 &&
        2 <= len && len <= n@pre &&
        0 <= left && left <= total - len &&
        Zlength(beads_l) == n@pre &&
        Zlength(dp_l) == total * width &&
        EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
        EnergyLeftProgress(vals_l, dp_l, total, width, len, left) &&
        EnergyLabelsBounded(beads_l, n@pre) &&
        EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
        IntArray::full(beads, n@pre, beads_l) *
        IntArray::full(vals, total, vals_l) *
        IntArray::full(dp, total * width, dp_l)
     */
    for (int left = 0; left < total - len; ++left) {
      int right = left + len - 1;
      int best = 0;

      /*@ Assert
          exists vals_l dp_l,
          beads == beads@pre && vals == vals@pre && dp == dp@pre &&
          n == n@pre &&
          total == 2 * n@pre &&
          width == total &&
          4 <= n@pre && n@pre <= 100 &&
          8 <= total && total <= 200 &&
          2 <= len && len <= n@pre &&
          0 <= left && left < total - len &&
          right == left + len - 1 &&
          left < right &&
          0 <= right && right < total &&
          right + 1 < total &&
          Zlength(beads_l) == n@pre &&
          Zlength(dp_l) == total * width &&
          EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
          EnergySplitProgress(vals_l, dp_l, total, width, len, left, left, best) &&
          EnergyLabelsBounded(beads_l, n@pre) &&
          EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
          IntArray::full(beads, n@pre, beads_l) *
          IntArray::full(vals, total, vals_l) *
          IntArray::full(dp, total * width, dp_l)
       */
      /*@ Inv Assert
          exists vals_l dp_l,
          beads == beads@pre && vals == vals@pre && dp == dp@pre &&
          n == n@pre &&
          total == 2 * n@pre &&
          width == total &&
          4 <= n@pre && n@pre <= 100 &&
          8 <= total && total <= 200 &&
          2 <= len && len <= n@pre &&
          0 <= left && left < total - len &&
          right == left + len - 1 &&
          left < right &&
          0 <= right && right < total &&
          right + 1 < total &&
          left <= split && split <= right &&
          0 <= best && best <= 2100000000 &&
          Zlength(beads_l) == n@pre &&
          Zlength(dp_l) == total * width &&
          EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
          EnergySplitProgress(vals_l, dp_l, total, width, len, left, split, best) &&
          EnergyLabelsBounded(beads_l, n@pre) &&
          EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
          IntArray::full(beads, n@pre, beads_l) *
          IntArray::full(vals, total, vals_l) *
          IntArray::full(dp, total * width, dp_l)
       */
      for (int split = left; split < right; ++split) {
        /*@ Assert
            exists vals_l dp_l,
            beads == beads@pre && vals == vals@pre && dp == dp@pre &&
            n == n@pre &&
            total == 2 * n@pre &&
            width == total &&
            4 <= n@pre && n@pre <= 100 &&
            8 <= total && total <= 200 &&
            2 <= len && len <= n@pre &&
            0 <= left && left < total - len &&
            right == left + len - 1 &&
            left <= split && split < right &&
            0 <= right && right < total &&
            right + 1 < total &&
            0 <= left * width + split &&
            left * width + split < total * width &&
            0 <= (split + 1) * width + right &&
            (split + 1) * width + right < total * width &&
            0 <= left && left < total &&
            0 <= split + 1 && split + 1 < total &&
            0 <= right + 1 && right + 1 < total &&
            Zlength(beads_l) == n@pre &&
            Zlength(dp_l) == total * width &&
            EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
            EnergySplitProgress(vals_l, dp_l, total, width, len, left, split, best) &&
            EnergyLabelsBounded(beads_l, n@pre) &&
            EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
            IntArray::full(beads, n@pre, beads_l) *
            IntArray::full(vals, total, vals_l) *
            IntArray::full(dp, total * width, dp_l)
         */
        int left_value = dp[left * width + split];
        int right_value = dp[(split + 1) * width + right];
        int gain = vals[left] * vals[split + 1] * vals[right + 1];
        int candidate = left_value + right_value + gain;

        /*@ Assert
            exists vals_l dp_l,
            beads == beads@pre && vals == vals@pre && dp == dp@pre &&
            n == n@pre &&
            total == 2 * n@pre &&
            width == total &&
            4 <= n@pre && n@pre <= 100 &&
            8 <= total && total <= 200 &&
            2 <= len && len <= n@pre &&
            0 <= left && left < total - len &&
            right == left + len - 1 &&
            left <= split && split < right &&
            0 <= right && right < total &&
            right + 1 < total &&
            left_value == dp_l[left * width + split] &&
            right_value == dp_l[(split + 1) * width + right] &&
            gain == vals_l[left] * vals_l[split + 1] * vals_l[right + 1] &&
            candidate == left_value + right_value + gain &&
            0 <= candidate && candidate <= 2100000000 &&
            Zlength(beads_l) == n@pre &&
            Zlength(dp_l) == total * width &&
            EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
            EnergySplitProgress(vals_l, dp_l, total, width, len, left, split, best) &&
            EnergyLabelsBounded(beads_l, n@pre) &&
            EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
            IntArray::full(beads, n@pre, beads_l) *
            IntArray::full(vals, total, vals_l) *
            IntArray::full(dp, total * width, dp_l)
         */
        if (candidate > best) {
          best = candidate;
        }
        /*@ Assert
            exists vals_l dp_l,
            beads == beads@pre && vals == vals@pre && dp == dp@pre &&
            n == n@pre &&
            total == 2 * n@pre &&
            width == total &&
            4 <= n@pre && n@pre <= 100 &&
            8 <= total && total <= 200 &&
            2 <= len && len <= n@pre &&
            0 <= left && left < total - len &&
            right == left + len - 1 &&
            left <= split && split < right &&
            right + 1 < total &&
            left_value == dp_l[left * width + split] &&
            right_value == dp_l[(split + 1) * width + right] &&
            gain == vals_l[left] * vals_l[split + 1] * vals_l[right + 1] &&
            candidate == left_value + right_value + gain &&
            0 <= candidate && candidate <= 2100000000 &&
            0 <= best && best <= 2100000000 &&
            Zlength(beads_l) == n@pre &&
            Zlength(dp_l) == total * width &&
            EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
            EnergySplitProgress(vals_l, dp_l, total, width, len, left, split + 1, best) &&
            EnergyLabelsBounded(beads_l, n@pre) &&
            EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
            IntArray::full(beads, n@pre, beads_l) *
            IntArray::full(vals, total, vals_l) *
            IntArray::full(dp, total * width, dp_l)
         */
      }

      /*@ Assert
          exists vals_l dp_l,
          beads == beads@pre && vals == vals@pre && dp == dp@pre &&
          n == n@pre &&
          total == 2 * n@pre &&
          width == total &&
          4 <= n@pre && n@pre <= 100 &&
          8 <= total && total <= 200 &&
          2 <= len && len <= n@pre &&
          0 <= left && left < total - len &&
          right == left + len - 1 &&
          right + 1 < total &&
          0 <= left * width + right &&
          left * width + right < total * width &&
          0 <= best && best <= 2100000000 &&
          Zlength(beads_l) == n@pre &&
          Zlength(dp_l) == total * width &&
          EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
          EnergySplitProgress(vals_l, dp_l, total, width, len, left, right, best) &&
          EnergyIntervalBest(vals_l, left, right, best) &&
          EnergyLabelsBounded(beads_l, n@pre) &&
          EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
          IntArray::full(beads, n@pre, beads_l) *
          IntArray::full(vals, total, vals_l) *
          IntArray::full(dp, total * width, dp_l)
       */
      dp[left * width + right] = best;
      /*@ Assert
          exists vals_l dp_old dp_new,
          beads == beads@pre && vals == vals@pre && dp == dp@pre &&
          n == n@pre &&
          total == 2 * n@pre &&
          width == total &&
          4 <= n@pre && n@pre <= 100 &&
          8 <= total && total <= 200 &&
          2 <= len && len <= n@pre &&
          0 <= left && left < total - len &&
          right == left + len - 1 &&
          0 <= best && best <= 2100000000 &&
          Zlength(beads_l) == n@pre &&
          Zlength(dp_old) == total * width &&
          Zlength(dp_new) == total * width &&
          EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
          EnergyUpdatedCell(vals_l, dp_old, dp_new, width, left, right, best) &&
          EnergyLeftProgress(vals_l, dp_new, total, width, len, left + 1) &&
          EnergyLabelsBounded(beads_l, n@pre) &&
          EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
          IntArray::full(beads, n@pre, beads_l) *
          IntArray::full(vals, total, vals_l) *
          IntArray::full(dp, total * width, dp_new)
       */
    }
    /*@ Assert
        exists vals_l dp_l,
        beads == beads@pre && vals == vals@pre && dp == dp@pre &&
        n == n@pre &&
        total == 2 * n@pre &&
        width == total &&
        4 <= n@pre && n@pre <= 100 &&
        8 <= total && total <= 200 &&
        2 <= len && len <= n@pre &&
        Zlength(beads_l) == n@pre &&
        Zlength(dp_l) == total * width &&
        EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
        EnergyLenDone(vals_l, dp_l, total, width, len + 1) &&
        EnergyLabelsBounded(beads_l, n@pre) &&
        EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
        IntArray::full(beads, n@pre, beads_l) *
        IntArray::full(vals, total, vals_l) *
        IntArray::full(dp, total * width, dp_l)
     */
  }

  int answer = 0;
  /*@ Assert
      exists vals_l dp_l,
      beads == beads@pre && vals == vals@pre && dp == dp@pre &&
      n == n@pre &&
      total == 2 * n@pre &&
      width == total &&
      4 <= n@pre && n@pre <= 100 &&
      8 <= total && total <= 200 &&
      Zlength(beads_l) == n@pre &&
      Zlength(dp_l) == total * width &&
      EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
      EnergyLenDone(vals_l, dp_l, total, width, n@pre + 1) &&
      EnergyAnswerProgress(beads_l, vals_l, dp_l, n@pre, total, width, 0, answer) &&
      EnergyLabelsBounded(beads_l, n@pre) &&
      EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
      IntArray::full(beads, n@pre, beads_l) *
      IntArray::full(vals, total, vals_l) *
      IntArray::full(dp, total * width, dp_l)
   */
  /*@ Inv Assert
      exists vals_l dp_l,
      beads == beads@pre && vals == vals@pre && dp == dp@pre &&
      n == n@pre &&
      total == 2 * n@pre &&
      width == total &&
      4 <= n@pre && n@pre <= 100 &&
      8 <= total && total <= 200 &&
      0 <= start && start <= n@pre &&
      0 <= answer && answer <= 2100000000 &&
      Zlength(beads_l) == n@pre &&
      Zlength(dp_l) == total * width &&
      EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
      EnergyLenDone(vals_l, dp_l, total, width, n@pre + 1) &&
      EnergyAnswerProgress(beads_l, vals_l, dp_l, n@pre, total, width, start, answer) &&
      EnergyLabelsBounded(beads_l, n@pre) &&
      EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
      IntArray::full(beads, n@pre, beads_l) *
      IntArray::full(vals, total, vals_l) *
      IntArray::full(dp, total * width, dp_l)
   */
  for (int start = 0; start < n; ++start) {
    /*@ Assert
        exists vals_l dp_l,
        beads == beads@pre && vals == vals@pre && dp == dp@pre &&
        n == n@pre &&
        total == 2 * n@pre &&
        width == total &&
        4 <= n@pre && n@pre <= 100 &&
        8 <= total && total <= 200 &&
        0 <= start && start < n@pre &&
        0 <= start * width + start + n@pre - 1 &&
        start * width + start + n@pre - 1 < total * width &&
        Zlength(beads_l) == n@pre &&
        Zlength(dp_l) == total * width &&
        EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
        EnergyLenDone(vals_l, dp_l, total, width, n@pre + 1) &&
        EnergyAnswerProgress(beads_l, vals_l, dp_l, n@pre, total, width, start, answer) &&
        EnergyIntervalBest(vals_l, start, start + n@pre - 1,
          dp_l[start * width + start + n@pre - 1]) &&
        EnergyLabelsBounded(beads_l, n@pre) &&
        EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
        IntArray::full(beads, n@pre, beads_l) *
        IntArray::full(vals, total, vals_l) *
        IntArray::full(dp, total * width, dp_l)
     */
    int value = dp[start * width + start + n - 1];
    /*@ Assert
        exists vals_l dp_l,
        beads == beads@pre && vals == vals@pre && dp == dp@pre &&
        n == n@pre &&
        total == 2 * n@pre &&
        width == total &&
        4 <= n@pre && n@pre <= 100 &&
        8 <= total && total <= 200 &&
        0 <= start && start < n@pre &&
        value == dp_l[start * width + start + n@pre - 1] &&
        0 <= value && value <= 2100000000 &&
        Zlength(beads_l) == n@pre &&
        Zlength(dp_l) == total * width &&
        EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
        EnergyLenDone(vals_l, dp_l, total, width, n@pre + 1) &&
        EnergyAnswerProgress(beads_l, vals_l, dp_l, n@pre, total, width, start, answer) &&
        EnergyIntervalBest(vals_l, start, start + n@pre - 1, value) &&
        EnergyLabelsBounded(beads_l, n@pre) &&
        EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
        IntArray::full(beads, n@pre, beads_l) *
        IntArray::full(vals, total, vals_l) *
        IntArray::full(dp, total * width, dp_l)
     */
    if (value > answer) {
      answer = value;
    }
    /*@ Assert
        exists vals_l dp_l,
        beads == beads@pre && vals == vals@pre && dp == dp@pre &&
        n == n@pre &&
        total == 2 * n@pre &&
        width == total &&
        4 <= n@pre && n@pre <= 100 &&
        8 <= total && total <= 200 &&
        0 <= start && start < n@pre &&
        value == dp_l[start * width + start + n@pre - 1] &&
        0 <= value && value <= 2100000000 &&
        0 <= answer && answer <= 2100000000 &&
        Zlength(beads_l) == n@pre &&
        Zlength(dp_l) == total * width &&
        EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
        EnergyLenDone(vals_l, dp_l, total, width, n@pre + 1) &&
        EnergyIntervalBest(vals_l, start, start + n@pre - 1, value) &&
        EnergyAnswerProgress(beads_l, vals_l, dp_l, n@pre, total, width, start + 1, answer) &&
        EnergyLabelsBounded(beads_l, n@pre) &&
        EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
        IntArray::full(beads, n@pre, beads_l) *
        IntArray::full(vals, total, vals_l) *
        IntArray::full(dp, total * width, dp_l)
     */
  }

  /*@ Assert
      exists vals_l dp_l,
      beads == beads@pre && vals == vals@pre && dp == dp@pre &&
      n == n@pre &&
      total == 2 * n@pre &&
      width == total &&
      4 <= n@pre && n@pre <= 100 &&
      8 <= total && total <= 200 &&
      0 <= answer && answer <= 2100000000 &&
      Zlength(beads_l) == n@pre &&
      Zlength(dp_l) == total * width &&
      EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
      EnergyLenDone(vals_l, dp_l, total, width, n@pre + 1) &&
      EnergyNecklaceAnswer(beads_l, n@pre, answer) &&
      EnergyLabelsBounded(beads_l, n@pre) &&
      EnergyComputationBounded(beads_l, n@pre, 2100000000) &&
      IntArray::full(beads, n@pre, beads_l) *
      IntArray::full(vals, total, vals_l) *
      IntArray::full(dp, total * width, dp_l)
   */
  return answer;
}
