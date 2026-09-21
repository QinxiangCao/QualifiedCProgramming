



/*@ Extern Coq
      (Forall2 : {A B} -> (A -> B -> Prop) -> list A -> list B -> Prop)
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::le : Z -> Z -> Prop)
      (Z::ge : Z -> Z -> Prop)
      (eq : {A} -> A -> A -> Prop)
      (EnergyLengthsComplete : list Z -> list Z -> Z -> Z -> Prop)
      (EnergyLeftComplete : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (EnergySplitBest : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
      (EnergyAnswerBest : list Z -> Z -> Z -> Z -> Prop)
      (EnergyValsDuplicated : list Z -> list Z -> Z -> Prop)
      (EnergyIntervalPlan : list Z -> Z -> Z -> Z -> Prop)
      (EnergyIntervalBest : list Z -> Z -> Z -> Z -> Prop)
      (EnergyNecklaceAnswer : list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.energy_necklace.energy_necklace_lib */

int energyNecklace(int *beads, int n)
/*@ With (beads_l : list Z)
    Require
      4 <= n && n <= 100 &&
      Zlength(beads_l) == n &&
      Zlength(beads_l) == n && Forall(Z::le(1), beads_l) && Forall(Z::ge(1000), beads_l) &&
      (forall (ev : list Z) (start : Z) (energy : Z),
        (EnergyValsDuplicated(beads_l, ev, n) &&
         0 <= start && start < n &&
         EnergyIntervalPlan(ev, start, start + n - 1, energy)) =>
        energy <= 2100000000) &&
      IntArray::full(beads, n, beads_l)
    Ensure
      EnergyNecklaceAnswer(beads_l, n, __return) &&
      IntArray::full(beads, n, beads_l)
 */
{
  int vals[200];
  int dp[40000];

  int total = 2 * n;
  int width = total;

  /*@ Inv Assert
      exists vals_l,
      beads == beads@pre &&  
      n == n@pre &&
      total == 2 * n@pre &&
      width == total &&
      4 <= n@pre && n@pre <= 100 &&
      8 <= total && total <= 200 &&
      Zlength(beads_l) == n@pre &&
      Zlength(vals_l) == i &&
      0 <= i && i <= n@pre &&
      Forall2(eq, sublist(0, i, vals_l), sublist(0, i, beads_l)) &&
      Zlength(beads_l) == n@pre && Forall(Z::le(1), beads_l) && Forall(Z::ge(1000), beads_l) &&
      (forall (ev : list Z) (start : Z) (energy : Z),
        (EnergyValsDuplicated(beads_l, ev, n@pre) &&
         0 <= start && start < n@pre &&
         EnergyIntervalPlan(ev, start, start + n@pre - 1, energy)) =>
        energy <= 2100000000) &&
      IntArray::full(beads, n@pre, beads_l) *
      IntArray::seg(vals, 0, i, vals_l) *
      IntArray::undef_seg(vals, i, total) *
      IntArray::undef_full(dp, total * width) *
      IntArray::undef_seg(vals, 2 * n@pre, 200) *
      IntArray::undef_seg(dp, (2 * n@pre) * (2 * n@pre), 40000)
   */
  for (int i = 0; i < n; ++i) {
    vals[i] = beads[i];
  }

  /*@ Inv Assert
      exists vals_l,
      beads == beads@pre &&  
      n == n@pre &&
      total == 2 * n@pre &&
      width == total &&
      4 <= n@pre && n@pre <= 100 &&
      8 <= total && total <= 200 &&
      Zlength(beads_l) == n@pre &&
      Zlength(vals_l) == n@pre + i &&
      0 <= i && i <= n@pre &&
      Forall2(eq, sublist(0, n@pre, vals_l), sublist(0, n@pre, beads_l)) &&
      Forall2(eq, sublist(n@pre, n@pre + i, vals_l), sublist(0, i, beads_l)) &&
      Zlength(beads_l) == n@pre && Forall(Z::le(1), beads_l) && Forall(Z::ge(1000), beads_l) &&
      (forall (ev : list Z) (start : Z) (energy : Z),
        (EnergyValsDuplicated(beads_l, ev, n@pre) &&
         0 <= start && start < n@pre &&
         EnergyIntervalPlan(ev, start, start + n@pre - 1, energy)) =>
        energy <= 2100000000) &&
      IntArray::full(beads, n@pre, beads_l) *
      IntArray::seg(vals, 0, n@pre + i, vals_l) *
      IntArray::undef_seg(vals, n@pre + i, total) *
      IntArray::undef_full(dp, total * width) *
      IntArray::undef_seg(vals, 2 * n@pre, 200) *
      IntArray::undef_seg(dp, (2 * n@pre) * (2 * n@pre), 40000)
   */
  for (int i = 0; i < n; ++i) {
    vals[n + i] = beads[i];
  }

  /*@ Inv Assert
      exists vals_l dp_l,
      beads == beads@pre &&  
      n == n@pre &&
      total == 2 * n@pre &&
      width == total &&
      4 <= n@pre && n@pre <= 100 &&
      8 <= total && total <= 200 &&
      Zlength(beads_l) == n@pre &&
      Zlength(dp_l) == i &&
      0 <= i && i <= total * width &&
      Forall(eq(0), dp_l) &&
      EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
      Zlength(beads_l) == n@pre && Forall(Z::le(1), beads_l) && Forall(Z::ge(1000), beads_l) &&
      (forall (ev : list Z) (start : Z) (energy : Z),
        (EnergyValsDuplicated(beads_l, ev, n@pre) &&
         0 <= start && start < n@pre &&
         EnergyIntervalPlan(ev, start, start + n@pre - 1, energy)) =>
        energy <= 2100000000) &&
      IntArray::full(beads, n@pre, beads_l) *
      IntArray::full(vals, total, vals_l) *
      IntArray::seg(dp, 0, i, dp_l) *
      IntArray::undef_seg(dp, i, total * width) *
      IntArray::undef_seg(vals, 2 * n@pre, 200) *
      IntArray::undef_seg(dp, (2 * n@pre) * (2 * n@pre), 40000)
   */
  for (int i = 0; i < total * width; ++i) {
    dp[i] = 0;
  }

  /*@ Inv Assert
      exists vals_l dp_l,
      beads == beads@pre &&  
      n == n@pre &&
      total == 2 * n@pre &&
      width == total &&
      4 <= n@pre && n@pre <= 100 &&
      8 <= total && total <= 200 &&
      2 <= len && len <= n@pre + 1 &&
      Zlength(beads_l) == n@pre &&
      Zlength(dp_l) == total * width &&
      EnergyValsDuplicated(beads_l, vals_l, n@pre) &&
      0 <= total && width == total && Zlength(vals_l) == total && Zlength(dp_l) == total * width && 1 <= len && EnergyLengthsComplete(vals_l, dp_l, width, len) &&
      Zlength(beads_l) == n@pre && Forall(Z::le(1), beads_l) && Forall(Z::ge(1000), beads_l) &&
      (forall (ev : list Z) (start : Z) (energy : Z),
        (EnergyValsDuplicated(beads_l, ev, n@pre) &&
         0 <= start && start < n@pre &&
         EnergyIntervalPlan(ev, start, start + n@pre - 1, energy)) =>
        energy <= 2100000000) &&
      IntArray::full(beads, n@pre, beads_l) *
      IntArray::full(vals, total, vals_l) *
      IntArray::full(dp, total * width, dp_l) *
      IntArray::undef_seg(vals, 2 * n@pre, 200) *
      IntArray::undef_seg(dp, (2 * n@pre) * (2 * n@pre), 40000)
   */
  for (int len = 2; len <= n; ++len) {
    /*@ Inv Assert
        exists vals_l dp_l,
        beads == beads@pre &&  
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
        0 <= total && width == total && Zlength(vals_l) == total && Zlength(dp_l) == total * width && 1 <= len && EnergyLengthsComplete(vals_l, dp_l, width, len) && 2 <= len && 0 <= left && EnergyLeftComplete(vals_l, dp_l, width, len, left) &&
        Zlength(beads_l) == n@pre && Forall(Z::le(1), beads_l) && Forall(Z::ge(1000), beads_l) &&
        (forall (ev : list Z) (start : Z) (energy : Z),
          (EnergyValsDuplicated(beads_l, ev, n@pre) &&
           0 <= start && start < n@pre &&
           EnergyIntervalPlan(ev, start, start + n@pre - 1, energy)) =>
          energy <= 2100000000) &&
        IntArray::full(beads, n@pre, beads_l) *
        IntArray::full(vals, total, vals_l) *
        IntArray::full(dp, total * width, dp_l) *
      IntArray::undef_seg(vals, 2 * n@pre, 200) *
      IntArray::undef_seg(dp, (2 * n@pre) * (2 * n@pre), 40000)
   */
    for (int left = 0; left < total - len; ++left) {
      int right = left + len - 1;
      int best = 0;

      /*@ Inv Assert
          exists vals_l dp_l,
          beads == beads@pre &&  
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
          0 <= total && width == total && Zlength(vals_l) == total && Zlength(dp_l) == total * width && 1 <= len && EnergyLengthsComplete(vals_l, dp_l, width, len) && 2 <= len && 0 <= left && EnergyLeftComplete(vals_l, dp_l, width, len, left) && left + len <= total && left <= split && split <= left + len - 1 && 0 <= best && best <= 2100000000 && EnergySplitBest(vals_l, dp_l, width, len, left, split, best) &&
          Zlength(beads_l) == n@pre && Forall(Z::le(1), beads_l) && Forall(Z::ge(1000), beads_l) &&
          (forall (ev : list Z) (start : Z) (energy : Z),
            (EnergyValsDuplicated(beads_l, ev, n@pre) &&
             0 <= start && start < n@pre &&
             EnergyIntervalPlan(ev, start, start + n@pre - 1, energy)) =>
            energy <= 2100000000) &&
          IntArray::full(beads, n@pre, beads_l) *
          IntArray::full(vals, total, vals_l) *
          IntArray::full(dp, total * width, dp_l) *
      IntArray::undef_seg(vals, 2 * n@pre, 200) *
      IntArray::undef_seg(dp, (2 * n@pre) * (2 * n@pre), 40000)
   */
      for (int split = left; split < right; ++split) {
        /*@ Assert
            exists vals_l dp_l,
            beads == beads@pre &&  
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
            0 <= total && width == total && Zlength(vals_l) == total && Zlength(dp_l) == total * width && 1 <= len && EnergyLengthsComplete(vals_l, dp_l, width, len) && 2 <= len && 0 <= left && EnergyLeftComplete(vals_l, dp_l, width, len, left) && left + len <= total && left <= split && split <= left + len - 1 && 0 <= best && best <= 2100000000 && EnergySplitBest(vals_l, dp_l, width, len, left, split, best) &&
            Zlength(beads_l) == n@pre && Forall(Z::le(1), beads_l) && Forall(Z::ge(1000), beads_l) &&
            (forall (ev : list Z) (start : Z) (energy : Z),
              (EnergyValsDuplicated(beads_l, ev, n@pre) &&
               0 <= start && start < n@pre &&
               EnergyIntervalPlan(ev, start, start + n@pre - 1, energy)) =>
              energy <= 2100000000) &&
            IntArray::full(beads, n@pre, beads_l) *
            IntArray::full(vals, total, vals_l) *
            IntArray::full(dp, total * width, dp_l) *
      IntArray::undef_seg(vals, 2 * n@pre, 200) *
      IntArray::undef_seg(dp, (2 * n@pre) * (2 * n@pre), 40000)
   */
        int left_value = dp[left * width + split];
        int right_value = dp[(split + 1) * width + right];
        int gain = vals[left] * vals[split + 1] * vals[right + 1];
        int candidate = left_value + right_value + gain;

        /*@ Assert
            exists vals_l dp_l,
            beads == beads@pre &&  
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
            0 <= total && width == total && Zlength(vals_l) == total && Zlength(dp_l) == total * width && 1 <= len && EnergyLengthsComplete(vals_l, dp_l, width, len) && 2 <= len && 0 <= left && EnergyLeftComplete(vals_l, dp_l, width, len, left) && left + len <= total && left <= split && split <= left + len - 1 && 0 <= best && best <= 2100000000 && EnergySplitBest(vals_l, dp_l, width, len, left, split, best) &&
            Zlength(beads_l) == n@pre && Forall(Z::le(1), beads_l) && Forall(Z::ge(1000), beads_l) &&
            (forall (ev : list Z) (start : Z) (energy : Z),
              (EnergyValsDuplicated(beads_l, ev, n@pre) &&
               0 <= start && start < n@pre &&
               EnergyIntervalPlan(ev, start, start + n@pre - 1, energy)) =>
              energy <= 2100000000) &&
            IntArray::full(beads, n@pre, beads_l) *
            IntArray::full(vals, total, vals_l) *
            IntArray::full(dp, total * width, dp_l) *
      IntArray::undef_seg(vals, 2 * n@pre, 200) *
      IntArray::undef_seg(dp, (2 * n@pre) * (2 * n@pre), 40000)
   */
        if (candidate > best) {
          best = candidate;
        }
        /*@ Assert
            exists vals_l dp_l,
            beads == beads@pre &&  
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
            0 <= total && width == total && Zlength(vals_l) == total && Zlength(dp_l) == total * width && 1 <= len && EnergyLengthsComplete(vals_l, dp_l, width, len) && 2 <= len && 0 <= left && EnergyLeftComplete(vals_l, dp_l, width, len, left) && left + len <= total && left <= split + 1 && split + 1 <= left + len - 1 && 0 <= best && best <= 2100000000 && EnergySplitBest(vals_l, dp_l, width, len, left, split + 1, best) &&
            Zlength(beads_l) == n@pre && Forall(Z::le(1), beads_l) && Forall(Z::ge(1000), beads_l) &&
            (forall (ev : list Z) (start : Z) (energy : Z),
              (EnergyValsDuplicated(beads_l, ev, n@pre) &&
               0 <= start && start < n@pre &&
               EnergyIntervalPlan(ev, start, start + n@pre - 1, energy)) =>
              energy <= 2100000000) &&
            IntArray::full(beads, n@pre, beads_l) *
            IntArray::full(vals, total, vals_l) *
            IntArray::full(dp, total * width, dp_l) *
      IntArray::undef_seg(vals, 2 * n@pre, 200) *
      IntArray::undef_seg(dp, (2 * n@pre) * (2 * n@pre), 40000)
   */
      }

      /*@ Assert
          exists vals_l dp_l,
          beads == beads@pre &&  
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
          0 <= total && width == total && Zlength(vals_l) == total && Zlength(dp_l) == total * width && 1 <= len && EnergyLengthsComplete(vals_l, dp_l, width, len) && 2 <= len && 0 <= left && EnergyLeftComplete(vals_l, dp_l, width, len, left) && left + len <= total && left <= right && right <= left + len - 1 && 0 <= best && best <= 2100000000 && EnergySplitBest(vals_l, dp_l, width, len, left, right, best) &&
          EnergyIntervalBest(vals_l, left, right, best) &&
          Zlength(beads_l) == n@pre && Forall(Z::le(1), beads_l) && Forall(Z::ge(1000), beads_l) &&
          (forall (ev : list Z) (start : Z) (energy : Z),
            (EnergyValsDuplicated(beads_l, ev, n@pre) &&
             0 <= start && start < n@pre &&
             EnergyIntervalPlan(ev, start, start + n@pre - 1, energy)) =>
            energy <= 2100000000) &&
          IntArray::full(beads, n@pre, beads_l) *
          IntArray::full(vals, total, vals_l) *
          IntArray::full(dp, total * width, dp_l) *
      IntArray::undef_seg(vals, 2 * n@pre, 200) *
      IntArray::undef_seg(dp, (2 * n@pre) * (2 * n@pre), 40000)
   */
      dp[left * width + right] = best;

    }

  }

  int answer = 0;
  /*@ Inv Assert
      exists vals_l dp_l,
      beads == beads@pre &&  
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
      0 <= total && width == total && Zlength(vals_l) == total && Zlength(dp_l) == total * width && 1 <= n@pre + 1 && EnergyLengthsComplete(vals_l, dp_l, width, n@pre + 1) &&
      EnergyValsDuplicated(beads_l, vals_l, n@pre) && Zlength(dp_l) == total * width && width == total && 0 <= start && start <= n@pre && 0 <= answer && answer <= 2100000000 && EnergyAnswerBest(vals_l, n@pre, start, answer) &&
      Zlength(beads_l) == n@pre && Forall(Z::le(1), beads_l) && Forall(Z::ge(1000), beads_l) &&
      (forall (ev : list Z) (start : Z) (energy : Z),
        (EnergyValsDuplicated(beads_l, ev, n@pre) &&
         0 <= start && start < n@pre &&
         EnergyIntervalPlan(ev, start, start + n@pre - 1, energy)) =>
        energy <= 2100000000) &&
      IntArray::full(beads, n@pre, beads_l) *
      IntArray::full(vals, total, vals_l) *
      IntArray::full(dp, total * width, dp_l) *
      IntArray::undef_seg(vals, 2 * n@pre, 200) *
      IntArray::undef_seg(dp, (2 * n@pre) * (2 * n@pre), 40000)
   */
  for (int start = 0; start < n; ++start) {
    /*@ Assert
        exists vals_l dp_l,
        beads == beads@pre &&  
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
        0 <= total && width == total && Zlength(vals_l) == total && Zlength(dp_l) == total * width && 1 <= n@pre + 1 && EnergyLengthsComplete(vals_l, dp_l, width, n@pre + 1) &&
        EnergyValsDuplicated(beads_l, vals_l, n@pre) && Zlength(dp_l) == total * width && width == total && 0 <= start && start <= n@pre && 0 <= answer && answer <= 2100000000 && EnergyAnswerBest(vals_l, n@pre, start, answer) &&
        EnergyIntervalBest(vals_l, start, start + n@pre - 1,
          dp_l[start * width + start + n@pre - 1]) &&
        Zlength(beads_l) == n@pre && Forall(Z::le(1), beads_l) && Forall(Z::ge(1000), beads_l) &&
        (forall (ev : list Z) (start : Z) (energy : Z),
          (EnergyValsDuplicated(beads_l, ev, n@pre) &&
           0 <= start && start < n@pre &&
           EnergyIntervalPlan(ev, start, start + n@pre - 1, energy)) =>
          energy <= 2100000000) &&
        IntArray::full(beads, n@pre, beads_l) *
        IntArray::full(vals, total, vals_l) *
        IntArray::full(dp, total * width, dp_l) *
      IntArray::undef_seg(vals, 2 * n@pre, 200) *
      IntArray::undef_seg(dp, (2 * n@pre) * (2 * n@pre), 40000)
   */
    int value = dp[start * width + start + n - 1];
    /*@ Assert
        exists vals_l dp_l,
        beads == beads@pre &&  
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
        0 <= total && width == total && Zlength(vals_l) == total && Zlength(dp_l) == total * width && 1 <= n@pre + 1 && EnergyLengthsComplete(vals_l, dp_l, width, n@pre + 1) &&
        EnergyValsDuplicated(beads_l, vals_l, n@pre) && Zlength(dp_l) == total * width && width == total && 0 <= start && start <= n@pre && 0 <= answer && answer <= 2100000000 && EnergyAnswerBest(vals_l, n@pre, start, answer) &&
        EnergyIntervalBest(vals_l, start, start + n@pre - 1, value) &&
        Zlength(beads_l) == n@pre && Forall(Z::le(1), beads_l) && Forall(Z::ge(1000), beads_l) &&
        (forall (ev : list Z) (start : Z) (energy : Z),
          (EnergyValsDuplicated(beads_l, ev, n@pre) &&
           0 <= start && start < n@pre &&
           EnergyIntervalPlan(ev, start, start + n@pre - 1, energy)) =>
          energy <= 2100000000) &&
        IntArray::full(beads, n@pre, beads_l) *
        IntArray::full(vals, total, vals_l) *
        IntArray::full(dp, total * width, dp_l) *
      IntArray::undef_seg(vals, 2 * n@pre, 200) *
      IntArray::undef_seg(dp, (2 * n@pre) * (2 * n@pre), 40000)
   */
    if (value > answer) {
      answer = value;
    }
    /*@ Assert
        exists vals_l dp_l,
        beads == beads@pre &&  
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
        0 <= total && width == total && Zlength(vals_l) == total && Zlength(dp_l) == total * width && 1 <= n@pre + 1 && EnergyLengthsComplete(vals_l, dp_l, width, n@pre + 1) &&
        EnergyIntervalBest(vals_l, start, start + n@pre - 1, value) &&
        EnergyValsDuplicated(beads_l, vals_l, n@pre) && Zlength(dp_l) == total * width && width == total && 0 <= start + 1 && start + 1 <= n@pre && 0 <= answer && answer <= 2100000000 && EnergyAnswerBest(vals_l, n@pre, start + 1, answer) &&
        Zlength(beads_l) == n@pre && Forall(Z::le(1), beads_l) && Forall(Z::ge(1000), beads_l) &&
        (forall (ev : list Z) (start : Z) (energy : Z),
          (EnergyValsDuplicated(beads_l, ev, n@pre) &&
           0 <= start && start < n@pre &&
           EnergyIntervalPlan(ev, start, start + n@pre - 1, energy)) =>
          energy <= 2100000000) &&
        IntArray::full(beads, n@pre, beads_l) *
        IntArray::full(vals, total, vals_l) *
        IntArray::full(dp, total * width, dp_l) *
      IntArray::undef_seg(vals, 2 * n@pre, 200) *
      IntArray::undef_seg(dp, (2 * n@pre) * (2 * n@pre), 40000)
   */
  }


  int result = answer;
  /*@ Assert
      beads == beads@pre && n == n@pre &&
      EnergyNecklaceAnswer(beads_l, n@pre, result) &&
      IntArray::full(beads@pre, n@pre, beads_l) *
      IntArray::undef_full(vals, 200) *
      IntArray::undef_full(dp, 40000) *
      has_int_permission(&total) *
      has_int_permission(&width) *
      has_int_permission(&answer)
   */
  return result;
}
