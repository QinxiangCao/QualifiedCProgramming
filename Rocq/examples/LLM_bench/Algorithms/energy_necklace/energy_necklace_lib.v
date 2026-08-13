Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition EnergyValsDuplicated (beads vals : list Z) (n : Z) : Prop :=
  0 <= n /\
  Zlength beads = n /\
  Zlength vals = 2 * n /\
  (forall i, 0 <= i < n -> Znth i vals 0 = Znth i beads 0) /\
  (forall i, 0 <= i < n -> Znth (n + i) vals 0 = Znth i beads 0).

Definition EnergyLabelsBounded (beads : list Z) (n : Z) : Prop :=
  Zlength beads = n /\
  forall i, 0 <= i < n -> 1 <= Znth i beads 0 <= 1000.

Inductive EnergyIntervalPlan (vals : list Z) : Z -> Z -> Z -> Prop :=
  | EnergyIntervalPlan_single :
      forall left,
        0 <= left ->
        left + 1 < Zlength vals ->
        EnergyIntervalPlan vals left left 0
  | EnergyIntervalPlan_merge :
      forall left split right e_left e_right,
        0 <= left ->
        left <= split < right ->
        right + 1 < Zlength vals ->
        EnergyIntervalPlan vals left split e_left ->
        EnergyIntervalPlan vals (split + 1) right e_right ->
        EnergyIntervalPlan vals left right
          (e_left + e_right +
             Znth left vals 0 * Znth (split + 1) vals 0 *
             Znth (right + 1) vals 0).

Definition EnergyIntervalBest
    (vals : list Z) (left right answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun energy => EnergyIntervalPlan vals left right energy)
    (fun energy => energy)
    answer.

Definition EnergyRotationBest
    (beads : list Z) (n start answer : Z) : Prop :=
  exists vals,
    EnergyValsDuplicated beads vals n /\
    0 <= start < n /\
    EnergyIntervalBest vals start (start + n - 1) answer.

Definition EnergyNecklaceAnswer
    (beads : list Z) (n answer : Z) : Prop :=
  max_value_of_subset Z.le
    (fun energy =>
       exists start, 0 <= start < n /\ EnergyRotationBest beads n start energy)
    (fun energy => energy)
    answer.

Definition EnergyCellIndex (width left right : Z) : Z :=
  left * width + right.

Definition EnergyZeroTable (dp : list Z) (total width : Z) : Prop :=
  0 <= total /\
  width = total /\
  Zlength dp = total * width /\
  forall idx, 0 <= idx < total * width -> Znth idx dp 0 = 0.

Definition EnergyLenDone
    (vals dp : list Z) (total width len : Z) : Prop :=
  0 <= total /\
  width = total /\
  Zlength vals = total /\
  Zlength dp = total * width /\
  1 <= len /\
  (forall l left right idx,
     1 <= l < len ->
     right = left + l - 1 ->
     idx = EnergyCellIndex width left right ->
     0 <= left ->
     left + l < Zlength vals ->
     EnergyIntervalBest vals left right (Znth idx dp 0)).

Definition EnergyLeftProgress
    (vals dp : list Z) (total width len left : Z) : Prop :=
  EnergyLenDone vals dp total width len /\
  2 <= len /\
  0 <= left /\
  (forall done_left right idx,
     0 <= done_left < left ->
     right = done_left + len - 1 ->
     idx = EnergyCellIndex width done_left right ->
     done_left + len < Zlength vals ->
     EnergyIntervalBest vals done_left right (Znth idx dp 0)).

Definition EnergySplitCandidate
    (vals dp : list Z) (width left right split candidate : Z) : Prop :=
  left <= split < right /\
  right + 1 < Zlength vals /\
  candidate =
    Znth (EnergyCellIndex width left split) dp 0 +
    Znth (EnergyCellIndex width (split + 1) right) dp 0 +
    Znth left vals 0 * Znth (split + 1) vals 0 * Znth (right + 1) vals 0.

Definition EnergySplitProgress
    (vals dp : list Z) (total width len left split best : Z) : Prop :=
  EnergyLeftProgress vals dp total width len left /\
  let right := left + len - 1 in
  2 <= len /\
  0 <= left /\
  left + len <= total /\
  right = left + len - 1 /\
  left <= split <= right /\
  0 <= best <= 2100000000 /\
  ((split = left /\ best = 0) \/
   (left < split /\
    max_value_of_subset Z.le
      (fun candidate =>
         exists k,
           left <= k < split /\
           EnergySplitCandidate vals dp width left right k candidate)
      (fun candidate => candidate)
      best)).

Definition EnergyUpdatedCell
    (vals old_dp new_dp : list Z) (width left right value : Z) : Prop :=
  0 <= EnergyCellIndex width left right < Zlength old_dp /\
  new_dp = replace_Znth (EnergyCellIndex width left right) value old_dp /\
  EnergyIntervalBest vals left right value.

Definition EnergyAnswerProgress
    (beads vals dp : list Z) (n total width start answer : Z) : Prop :=
  EnergyValsDuplicated beads vals n /\
  Zlength dp = total * width /\
  width = total /\
  0 <= start <= n /\
  0 <= answer <= 2100000000 /\
  ((start = 0 /\ answer = 0) \/
   (0 < start /\
    max_value_of_subset Z.le
      (fun value =>
         exists s,
           0 <= s < start /\
           EnergyIntervalBest vals s (s + n - 1) value)
      (fun value => value)
      answer)).

Definition EnergySplitArithmeticBounded
    (vals dp : list Z) (width left right split bound : Z) : Prop :=
  let left_value := Znth (EnergyCellIndex width left split) dp 0 in
  let right_value := Znth (EnergyCellIndex width (split + 1) right) dp 0 in
  let gain :=
    Znth left vals 0 * Znth (split + 1) vals 0 * Znth (right + 1) vals 0 in
  0 <= left_value <= bound /\
  0 <= right_value <= bound /\
  0 <= gain <= bound /\
  0 <= left_value + right_value <= bound /\
  0 <= left_value + right_value + gain <= bound.

Definition EnergyComputationBounded
    (beads : list Z) (n bound : Z) : Prop :=
  0 <= bound /\
  (forall vals dp total width len left right split,
     EnergyValsDuplicated beads vals n ->
     total = 2 * n ->
     width = total ->
     2 <= len <= n ->
     0 <= left < total - len ->
     right = left + len - 1 ->
     left <= split < right ->
     Zlength dp = total * width ->
     EnergyLenDone vals dp total width len ->
     EnergySplitArithmeticBounded vals dp width left right split bound) /\
  (forall vals left right answer,
     EnergyValsDuplicated beads vals n ->
     0 <= left ->
     left <= right ->
     right + 1 < Zlength vals ->
     EnergyIntervalBest vals left right answer ->
     0 <= answer <= bound) /\
  (forall vals dp total width start,
     EnergyValsDuplicated beads vals n ->
     total = 2 * n ->
     width = total ->
     0 <= start < n ->
     Zlength dp = total * width ->
     EnergyLenDone vals dp total width (n + 1) ->
     0 <= Znth (EnergyCellIndex width start (start + n - 1)) dp 0 <= bound).

Require Import Coq.micromega.Psatz.
Lemma EnergyValsDuplicated_label_bound__arithmetic_safety_bounds :
  forall beads vals n i,
    EnergyValsDuplicated beads vals n ->
    EnergyLabelsBounded beads n ->
    0 <= i < 2 * n ->
    1 <= Znth i vals 0 <= 1000.
Proof.
  intros beads vals n i Hdup Hlabels Hi.
  unfold EnergyValsDuplicated in Hdup.
  unfold EnergyLabelsBounded in Hlabels.
  destruct Hdup as [Hn [_ [_ [Hfirst Hsecond]]]].
  destruct Hlabels as [_ Hbounded].
  destruct (Z_lt_ge_dec i n) as [Hi_lt | Hi_ge].
  - rewrite Hfirst by lia.
    apply Hbounded; lia.
  - replace i with (n + (i - n)) by lia.
    rewrite Hsecond by lia.
    apply Hbounded; lia.
Qed.
Lemma EnergySplitArithmeticBounded_from_progress__arithmetic_safety_bounds :
  forall beads vals dp n total width len left right split best bound,
    EnergyComputationBounded beads n bound ->
    EnergyValsDuplicated beads vals n ->
    total = 2 * n ->
    width = total ->
    2 <= len <= n ->
    0 <= left < total - len ->
    right = left + len - 1 ->
    left <= split < right ->
    Zlength dp = total * width ->
    EnergySplitProgress vals dp total width len left split best ->
    EnergySplitArithmeticBounded vals dp width left right split bound.
Proof.
  intros beads vals dp n total width len left right split best bound
    Hbounded Hdup Htotal Hwidth Hlen Hleft Hright Hsplit Hdp Hprogress.
  unfold EnergyComputationBounded in Hbounded.
  destruct Hbounded as [_ [Hsplit_bound _]].
  unfold EnergySplitProgress in Hprogress.
  destruct Hprogress as [Hleft_progress _].
  unfold EnergyLeftProgress in Hleft_progress.
  destruct Hleft_progress as [Hlen_done _].
  eapply Hsplit_bound; eauto.
Qed.
Lemma EnergyIntervalBest_single_zero__prefix_table_bootstrap :
  forall vals left,
    0 <= left ->
    left + 1 < Zlength vals ->
    EnergyIntervalBest vals left left 0.
Proof.
  intros vals left Hleft Hrange.
  unfold EnergyIntervalBest, max_value_of_subset, max_object_of_subset.
  exists 0.
  split; [split | reflexivity].
  - constructor; lia.
  - intros energy Hplan.
    inversion Hplan; subst; lia.
Qed.
Lemma EnergyZeroTable_len_done_2__prefix_table_bootstrap :
  forall vals dp total width,
    Zlength vals = total ->
    EnergyZeroTable dp total width ->
    EnergyLenDone vals dp total width 2.
Proof.
  intros vals dp total width Hvals Hzero.
  unfold EnergyZeroTable in Hzero.
  destruct Hzero as [Htotal [Hwidth [Hdp Hpoint]]].
  unfold EnergyLenDone.
  repeat split; try lia; auto.
  intros l left right idx Hl Hright Hidx Hleft Hrange.
  assert (Hl1 : l = 1) by lia.
  subst l right idx.
  replace (left + 1 - 1) with left by lia.
  rewrite Hpoint.
  - apply EnergyIntervalBest_single_zero__prefix_table_bootstrap; lia.
  - unfold EnergyCellIndex.
    nia.
Qed.
Lemma EnergyZeroTable_from_prefix__prefix_table_bootstrap :
  forall dp total width i,
    0 <= total ->
    width = total ->
    i >= total * width ->
    i <= total * width ->
    Zlength dp = i ->
    (forall k, 0 <= k < i -> Znth k dp 0 = 0) ->
    EnergyZeroTable dp total width.
Proof.
  intros dp total width i Htotal Hwidth Hge Hle Hlen Hpoint.
  unfold EnergyZeroTable.
  repeat split.
  - exact Htotal.
  - exact Hwidth.
  - rewrite Hlen.
    lia.
  - intros idx Hidx.
    apply Hpoint.
    lia.
Qed.
Lemma EnergySplitCandidate_ext_eq__dp_interval_progress :
  forall vals dp width left right split candidate1 candidate2,
    EnergySplitCandidate vals dp width left right split candidate1 ->
    EnergySplitCandidate vals dp width left right split candidate2 ->
    candidate1 = candidate2.
Proof.
  intros.
  unfold EnergySplitCandidate, EnergyCellIndex in *.
  lia.
Qed.
Lemma EnergySplitProgress_step_keep__dp_interval_progress :
  forall vals dp total width len left right split best candidate,
    right = left + len - 1 ->
    left <= split < right ->
    EnergySplitProgress vals dp total width len left split best ->
    EnergySplitCandidate vals dp width left right split candidate ->
    0 <= candidate ->
    candidate <= best ->
    EnergySplitProgress vals dp total width len left (split + 1) best.
Proof.
  intros vals dp total width len left right split best candidate
         Hright Hsplit_range Hprog Hcand Hcand_nonneg Hcand_le.
  subst right.
  unfold EnergySplitProgress in *.
  destruct Hprog as
    (Hleft_prog & Hlen2 & Hleft0 & Hleft_total & Hright_old &
     Hsplit_old & Hbest_bounds & Hcase).
  repeat match goal with
         | |- _ /\ _ => split; [try tauto; try lia|]
         end.
  right.
  split; [lia|].
  destruct Hcase as [[Hsplit_eq Hbest_eq] | [Hleft_split Hmax]].
  - subst split best.
    assert (candidate = 0) by lia.
    subst candidate.
    unfold max_value_of_subset, max_object_of_subset.
    exists 0.
    split; [split|reflexivity].
    + exists left.
      split; [lia|exact Hcand].
    + intros b Hb.
      destruct Hb as [k [[Hk_left Hk_right] Hcand_b]].
      assert (k = left) by lia.
      subst k.
      pose proof (EnergySplitCandidate_ext_eq__dp_interval_progress
                    vals dp width left (left + len - 1) left 0 b Hcand Hcand_b).
      lia.
  - unfold max_value_of_subset, max_object_of_subset in *.
    destruct Hmax as [a [[Ha_in Ha_max] Ha_eq]].
    subst best.
    exists a.
    split; [split|reflexivity].
    + destruct Ha_in as [k [Hk_range Hcand_k]].
      exists k.
      split; [lia|exact Hcand_k].
    + intros b Hb.
      destruct Hb as [k [[Hk_left Hk_right] Hcand_k]].
      destruct (Z_lt_ge_dec k split) as [Hk_lt|Hk_ge].
      * apply Ha_max.
        exists k.
        split; [lia|exact Hcand_k].
      * assert (k = split) by lia.
        subst k.
        pose proof (EnergySplitCandidate_ext_eq__dp_interval_progress
                      vals dp width left (left + len - 1) split candidate b Hcand Hcand_k).
        lia.
Qed.
Lemma EnergySplitProgress_step_take__dp_interval_progress :
  forall vals dp total width len left right split best candidate,
    right = left + len - 1 ->
    left <= split < right ->
    EnergySplitProgress vals dp total width len left split best ->
    EnergySplitCandidate vals dp width left right split candidate ->
    0 <= candidate <= 2100000000 ->
    best < candidate ->
    EnergySplitProgress vals dp total width len left (split + 1) candidate.
Proof.
  intros vals dp total width len left right split best candidate
         Hright Hsplit_range Hprog Hcand Hcand_bound Hbest_lt.
  subst right.
  unfold EnergySplitProgress in *.
  destruct Hprog as
    (Hleft_prog & Hlen2 & Hleft0 & Hleft_total & Hright_old &
     Hsplit_old & Hbest_bounds & Hcase).
  repeat match goal with
         | |- _ /\ _ => split; [try tauto; try lia|]
         end.
  right.
  split; [lia|].
  destruct Hcase as [[Hsplit_eq Hbest_eq] | [Hleft_split Hmax]].
  - subst split best.
    unfold max_value_of_subset, max_object_of_subset.
    exists candidate.
    split; [split|reflexivity].
    + exists left.
      split; [lia|exact Hcand].
    + intros b Hb.
      destruct Hb as [k [[Hk_left Hk_right] Hcand_b]].
      assert (k = left) by lia.
      subst k.
      pose proof (EnergySplitCandidate_ext_eq__dp_interval_progress
                    vals dp width left (left + len - 1) left candidate b Hcand Hcand_b).
      lia.
  - unfold max_value_of_subset, max_object_of_subset in *.
    destruct Hmax as [a [[Ha_in Ha_max] Ha_eq]].
    subst best.
    exists candidate.
    split; [split|reflexivity].
    + exists split.
      split; [lia|exact Hcand].
    + intros b Hb.
      destruct Hb as [k [[Hk_left Hk_right] Hcand_k]].
      destruct (Z_lt_ge_dec k split) as [Hk_lt|Hk_ge].
      * specialize (Ha_max b ltac:(exists k; split; [lia|exact Hcand_k])).
        lia.
      * assert (k = split) by lia.
        subst k.
        pose proof (EnergySplitCandidate_ext_eq__dp_interval_progress
                      vals dp width left (left + len - 1) split candidate b Hcand Hcand_k).
        lia.
Qed.
Lemma EnergySplitCandidate_plan__dp_interval_progress :
  forall vals dp total width len left right split candidate,
    EnergyLenDone vals dp total width len ->
    right = left + len - 1 ->
    0 <= left ->
    left <= split < right ->
    right + 1 < Zlength vals ->
    EnergySplitCandidate vals dp width left right split candidate ->
    EnergyIntervalPlan vals left right candidate.
Proof.
  intros vals dp total width len left right split candidate
         Hdone Hright Hleft_nonneg Hsplit Hright_bound Hcand.
  unfold EnergyLenDone in Hdone.
  destruct Hdone as
    (Htotal_nonneg & Hwidth & Hvals_len & Hdp_len & Hlen_pos & Hdone).
  unfold EnergySplitCandidate, EnergyCellIndex in Hcand.
  destruct Hcand as (_ & _ & Hcandidate_eq).
  assert (Hleft_best :
            EnergyIntervalBest vals left split
              (Znth (left * width + split) dp 0)).
  {
    eapply Hdone with (l := split - left + 1)
                       (left := left)
                       (right := split)
                       (idx := left * width + split).
    - lia.
    - lia.
    - unfold EnergyCellIndex; lia.
    - lia.
    - lia.
  }
  assert (Hright_best :
            EnergyIntervalBest vals (split + 1) right
              (Znth ((split + 1) * width + right) dp 0)).
  {
    eapply Hdone with (l := right - split)
                       (left := split + 1)
                       (right := right)
                       (idx := (split + 1) * width + right).
    - lia.
    - lia.
    - unfold EnergyCellIndex; lia.
    - lia.
    - lia.
  }
  unfold EnergyIntervalBest, max_value_of_subset,
    max_object_of_subset in *.
  destruct Hleft_best as [left_energy [[Hleft_plan _] Hleft_eq]].
  destruct Hright_best as [right_energy [[Hright_plan _] Hright_eq]].
  simpl in *.
  subst left_energy right_energy candidate.
  apply EnergyIntervalPlan_merge with (split := split); try lia; assumption.
Qed.
Lemma EnergySplitProgress_finish_interval_best__dp_interval_progress :
  forall vals dp total width len left right split best,
    right = left + len - 1 ->
    split >= right ->
    right + 1 < Zlength vals ->
    EnergySplitProgress vals dp total width len left split best ->
    EnergyIntervalBest vals left right best.
Proof.
  intros vals dp total width len left right split best
         Hright Hsplit_ge Hright_bound Hprog.
  subst right.
  unfold EnergySplitProgress in Hprog.
  destruct Hprog as
    (Hleft_prog & Hlen2 & Hleft0 & Hleft_total & Hright_eq &
     Hsplit_bounds & Hbest_bounds & Hcase).
  assert (Hsplit_eq : split = left + len - 1) by lia.
  subst split.
  destruct Hcase as [[Hleft_right Hbest_zero] | [_ Hmax]].
  { lia. }
  assert (Hdone_full : EnergyLenDone vals dp total width len)
    by (unfold EnergyLeftProgress in Hleft_prog; tauto).
  unfold EnergyLeftProgress, EnergyLenDone in Hleft_prog.
  destruct Hleft_prog as
    ((Htotal_nonneg & Hwidth & Hvals_len & Hdp_len & Hlen_pos & Hdone) &
     _ & _ & _).
  unfold EnergyIntervalBest, max_value_of_subset, max_object_of_subset.
  unfold max_value_of_subset, max_object_of_subset in Hmax.
  destruct Hmax as [candidate [[Hcand_in Hcand_max] Hcandidate_eq]].
  simpl in Hcandidate_eq.
  subst candidate.
  exists best.
  split; [split|reflexivity].
  - destruct Hcand_in as [k [Hk_range Hcand]].
    apply (EnergySplitCandidate_plan__dp_interval_progress
             vals dp total width len left (left + len - 1) k best);
      [ exact Hdone_full
      | reflexivity
      | exact Hleft0
      | exact Hk_range
      | lia
      | exact Hcand ].
  - intros b Hplan.
    inversion Hplan as
      [single_left Hsingle_nonneg Hsingle_bound
      | merge_left merge_split merge_right e_left e_right
        Hmerge_left_nonneg Hmerge_split_range Hmerge_right_bound
        Hplan_left Hplan_right]; subst.
    + lia.
    + pose proof
        (Hdone (merge_split - left + 1) left merge_split
           (EnergyCellIndex (Zlength vals) left merge_split)
           ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
           ltac:(lia)) as Hbest_left.
      pose proof
        (Hdone (left + len - 1 - merge_split) (merge_split + 1)
           (left + len - 1)
           (EnergyCellIndex (Zlength vals) (merge_split + 1) (left + len - 1))
           ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
           ltac:(lia)) as Hbest_right.
      unfold EnergyIntervalBest, max_value_of_subset,
        max_object_of_subset in Hbest_left, Hbest_right.
      destruct Hbest_left as [best_left [[_ Hmax_left] Hbest_left_eq]].
      destruct Hbest_right as [best_right [[_ Hmax_right] Hbest_right_eq]].
      simpl in *.
      subst best_left best_right.
      specialize (Hmax_left e_left Hplan_left).
      specialize (Hmax_right e_right Hplan_right).
      set (cand :=
             Znth (EnergyCellIndex (Zlength vals) left merge_split) dp 0 +
             Znth (EnergyCellIndex (Zlength vals) (merge_split + 1) (left + len - 1)) dp 0 +
             Znth left vals 0 * Znth (merge_split + 1) vals 0 *
             Znth (left + len - 1 + 1) vals 0).
      assert (Hcand_cur :
                EnergySplitCandidate vals dp (Zlength vals) left (left + len - 1)
                  merge_split cand).
      {
        unfold cand, EnergySplitCandidate.
        repeat split; try lia.
      }
      specialize (Hcand_max cand ltac:(exists merge_split; split; [lia|exact Hcand_cur])).
      unfold cand in Hcand_max.
      lia.
Qed.
Lemma EnergyCellIndex_inj__dp_interval_progress :
  forall width left1 right1 left2 right2,
    0 < width ->
    0 <= right1 < width ->
    0 <= right2 < width ->
    EnergyCellIndex width left1 right1 =
      EnergyCellIndex width left2 right2 ->
    left1 = left2 /\ right1 = right2.
Proof.
  intros width left1 right1 left2 right2 Hwidth Hright1 Hright2 Heq.
  unfold EnergyCellIndex in Heq.
  destruct (Z_lt_ge_dec left1 left2) as [Hlt|Hge].
  - assert ((left2 - left1) * width = right1 - right2) by nia.
    nia.
  - destruct (Z_lt_ge_dec left2 left1) as [Hgt|Hle].
    + assert ((left1 - left2) * width = right2 - right1) by nia.
      nia.
    + assert (left1 = left2) by lia.
      subst left2.
      split; [reflexivity|lia].
Qed.
Lemma EnergyLenDone_replace_current__dp_interval_progress :
  forall vals dp total width len left right best,
    right = left + len - 1 ->
    0 <= left ->
    left < total - len ->
    EnergyLenDone vals dp total width len ->
    EnergyLenDone vals
      (replace_Znth (EnergyCellIndex width left right) best dp)
      total width len.
Proof.
  intros vals dp total width len left right best
         Hright Hleft Hleft_bound Hdone.
  unfold EnergyLenDone in *.
  destruct Hdone as
    (Htotal_nonneg & Hwidth & Hvals_len & Hdp_len & Hlen_pos & Hdone).
  repeat split; try assumption; try lia.
  - rewrite Zlength_replace_Znth; exact Hdp_len.
  - intros l left0 right0 idx Hl Hright0 Hidx Hleft0 Hbound0.
    specialize (Hdone l left0 right0 idx Hl Hright0 Hidx Hleft0 Hbound0).
    rewrite Znth_replace_Znth_Diff.
    + exact Hdone.
    + unfold EnergyCellIndex; nia.
    + rewrite Hdp_len.
      unfold EnergyCellIndex in Hidx; nia.
    + intro Heq.
      rewrite Hidx in Heq.
      pose proof
        (EnergyCellIndex_inj__dp_interval_progress
           width left right left0 right0 ltac:(lia) ltac:(lia) ltac:(lia) Heq)
        as [Hleft_eq Hright_eq].
      lia.
Qed.
Lemma EnergyLeftProgress_step_update__dp_interval_progress :
  forall vals dp total width len left right best,
    right = left + len - 1 ->
    0 <= left ->
    left < total - len ->
    EnergySplitProgress vals dp total width len left right best ->
    EnergyIntervalBest vals left right best ->
    EnergyLeftProgress vals
      (replace_Znth (EnergyCellIndex width left right) best dp)
      total width len (left + 1).
Proof.
  intros vals dp total width len left right best
         Hright Hleft Hleft_bound Hprog Hbest.
  unfold EnergySplitProgress in Hprog.
  destruct Hprog as
    (Hleft_prog & Hlen2 & Hleft0 & Hleft_total & Hright_eq &
     Hsplit_bounds & Hbest_bounds & Hcase).
  unfold EnergyLeftProgress in Hleft_prog.
  destruct Hleft_prog as (Hdone & Hlen2_old & Hleft0_old & Hprev).
  unfold EnergyLeftProgress.
  split.
  - eapply (EnergyLenDone_replace_current__dp_interval_progress
              vals dp total width len left right best);
      [ exact Hright | exact Hleft | exact Hleft_bound | exact Hdone ].
  - split.
    + lia.
    + split.
      * lia.
      * intros done_left right0 idx Hdone_left Hright0 Hidx Hbound.
        destruct (Z.eq_dec done_left left) as [Hdone_eq|Hdone_neq].
        { subst done_left.
          assert (right0 = right) by lia.
          subst right0.
          subst idx.
          unfold EnergyCellIndex.
          rewrite H.
          rewrite Znth_replace_Znth_Same;
            [ exact Hbest
            | unfold EnergyLenDone in Hdone;
              destruct Hdone as
                (_ & Hwidth & Hvals_len & Hdp_len & _ & _);
              rewrite Hdp_len;
              nia ]. }
        { assert (done_left < left) by lia.
          specialize (Hprev done_left right0 idx ltac:(lia) Hright0 Hidx Hbound).
          rewrite Znth_replace_Znth_Diff;
            [ exact Hprev
            | unfold EnergyLenDone in Hdone;
              destruct Hdone as
                (_ & Hwidth & Hvals_len & Hdp_len & _ & _);
              rewrite Hdp_len;
              unfold EnergyCellIndex; nia
            | unfold EnergyLenDone in Hdone;
              destruct Hdone as
                (_ & Hwidth & Hvals_len & Hdp_len & _ & _);
              rewrite Hdp_len;
              unfold EnergyCellIndex in Hidx; nia
            | intro Heq;
              rewrite Hidx in Heq;
              unfold EnergyLenDone in Hdone;
              destruct Hdone as
                (_ & Hwidth & Hvals_len & Hdp_len & _ & _);
              pose proof
                (EnergyCellIndex_inj__dp_interval_progress
                   width left right done_left right0
                   ltac:(lia) ltac:(lia) ltac:(lia) Heq)
                as [Hleft_eq Hright_eq_index];
              lia ]. }
Qed.
Lemma EnergyLeftProgress_finish_len__dp_interval_progress :
  forall vals dp total width len left,
    left >= total - len ->
    left <= total - len ->
    EnergyLeftProgress vals dp total width len left ->
    EnergyLenDone vals dp total width (len + 1).
Proof.
  intros vals dp total width len left Hleft_ge Hleft_le Hprog.
  assert (Hleft_eq : left = total - len) by lia.
  unfold EnergyLeftProgress in Hprog.
  destruct Hprog as (Hdone_len & Hlen2 & Hleft0 & Hprev).
  unfold EnergyLenDone in Hdone_len.
  destruct Hdone_len as
    (Htotal_nonneg & Hwidth & Hvals_len & Hdp_len & Hlen_pos & Hdone).
  unfold EnergyLenDone.
  repeat split; try assumption; try lia.
  intros l left0 right idx Hl Hright Hidx Hleft0' Hbound.
  destruct (Z_lt_ge_dec l len) as [Hl_old|Hl_new].
  - apply (Hdone l left0 right idx); try assumption; try lia.
  - assert (l = len) by lia.
    subst l.
    apply (Hprev left0 right idx); try assumption; try lia.
Qed.
Lemma EnergyAnswerProgress_answer_bounds__answer_loop :
  forall beads vals dp n total width start answer,
    EnergyAnswerProgress beads vals dp n total width start answer ->
    0 <= answer <= 2100000000.
Proof.
  intros.
  unfold EnergyAnswerProgress in H.
  tauto.
Qed.
Lemma EnergyLenDone_to_answer_len__answer_loop :
  forall vals dp total width len n,
    len > n ->
    len <= n + 1 ->
    EnergyLenDone vals dp total width len ->
    EnergyLenDone vals dp total width (n + 1).
Proof.
  intros.
  replace (n + 1) with len by lia.
  exact H1.
Qed.
Lemma EnergyLenDone_rotation_cell_best__answer_loop :
  forall vals dp total width n start,
    4 <= n ->
    total = 2 * n ->
    width = total ->
    0 <= start < n ->
    EnergyLenDone vals dp total width (n + 1) ->
    EnergyIntervalBest vals start (start + n - 1)
      (Znth (EnergyCellIndex width start (start + n - 1)) dp 0).
Proof.
  intros vals dp total width n start Hn Htotal Hwidth Hstart Hdone.
  unfold EnergyLenDone in Hdone.
  destruct Hdone as [_ [_ [Hvals_len [_ [_ Hdone]]]]].
  eapply Hdone with
    (l := n) (left := start) (right := start + n - 1)
    (idx := EnergyCellIndex width start (start + n - 1));
    try reflexivity; try lia.
Qed.
Lemma EnergyAnswerCellBounded__answer_loop :
  forall beads vals dp n total width start,
    EnergyComputationBounded beads n 2100000000 ->
    EnergyValsDuplicated beads vals n ->
    total = 2 * n ->
    width = total ->
    0 <= start < n ->
    Zlength dp = total * width ->
    EnergyLenDone vals dp total width (n + 1) ->
    0 <= Znth (EnergyCellIndex width start (start + n - 1)) dp 0 <= 2100000000.
Proof.
  intros beads vals dp n total width start Hbounded Hvals Htotal Hwidth Hstart Hdp Hdone.
  unfold EnergyComputationBounded in Hbounded.
  destruct Hbounded as [_ [_ [_ Hcell]]].
  eapply Hcell; eauto.
Qed.
Lemma EnergyIntervalBest_unique__answer_loop :
  forall vals left right a b,
    EnergyIntervalBest vals left right a ->
    EnergyIntervalBest vals left right b ->
    a = b.
Proof.
  intros vals left right a b Ha Hb.
  unfold EnergyIntervalBest in *.
  eapply (@max_unique Z Z.le Zle_TotalOrder Z
    (fun energy => energy)
    (fun energy => EnergyIntervalPlan vals left right energy)); eauto.
Qed.
Lemma EnergyValsDuplicated_unique__answer_loop :
  forall beads vals1 vals2 n,
    EnergyValsDuplicated beads vals1 n ->
    EnergyValsDuplicated beads vals2 n ->
    vals1 = vals2.
Proof.
  intros beads vals1 vals2 n Hvals1 Hvals2.
  unfold EnergyValsDuplicated in *.
  destruct Hvals1 as [Hn [Hbeads1 [Hlen1 [Hfirst1 Hsecond1]]]].
  destruct Hvals2 as [_ [Hbeads2 [Hlen2 [Hfirst2 Hsecond2]]]].
  apply (proj2 (list_eq_ext vals1 vals2 0)).
  split; [lia|].
  intros i Hi.
  destruct (Z_lt_ge_dec i n) as [Hi_lt | Hi_ge].
  - rewrite Hfirst1, Hfirst2; lia.
  - assert (0 <= i - n < n) by lia.
    replace i with (n + (i - n)) by lia.
    rewrite Hsecond1, Hsecond2; lia.
Qed.
Lemma EnergyAnswerProgress_step_keep__answer_loop :
  forall beads vals dp n total width start answer value,
    EnergyAnswerProgress beads vals dp n total width start answer ->
    0 <= start < n ->
    EnergyIntervalBest vals start (start + n - 1) value ->
    0 <= value ->
    value <= answer ->
    EnergyAnswerProgress beads vals dp n total width (start + 1) answer.
Proof.
  intros beads vals dp n total width start answer value
    Hprogress Hstart Hbest Hvalue_nonneg Hvalue_le.
  unfold EnergyAnswerProgress in *.
  destruct Hprogress as [Hvals [Hdp [Hwidth [Hstart_progress [Hanswer Hcase]]]]].
  split; [exact Hvals|].
  split; [exact Hdp|].
  split; [exact Hwidth|].
  split; [lia|].
  split; [exact Hanswer|].
  right.
  split; [lia|].
  destruct Hcase as [[Hstart0 Hanswer0] | [Hstartpos Holdmax]].
  - subst start answer.
    assert (value = 0) by lia.
    subst value.
    unfold max_value_of_subset, max_object_of_subset.
    exists 0.
    split.
    + split.
      * exists 0.
        split; [lia|exact Hbest].
      * intros b [s [Hs Hb]].
        assert (s = 0) by lia.
        subst s.
        pose proof (EnergyIntervalBest_unique__answer_loop vals 0 (0 + n - 1) b 0 Hb Hbest).
        lia.
    + reflexivity.
  - unfold max_value_of_subset, max_object_of_subset in *.
    destruct Holdmax as [a [[Ha_in Ha_max] Ha_eq]].
    exists a.
    split.
    + split.
      * destruct Ha_in as [s [Hs Hbest_s]].
        exists s.
        split; [lia|exact Hbest_s].
      * intros b [s [Hs Hb]].
        destruct (Z_lt_ge_dec s start) as [Hs_lt | Hs_ge].
        -- apply Ha_max.
           exists s.
           split; [lia|exact Hb].
        -- assert (s = start) by lia.
           subst s.
           pose proof
             (EnergyIntervalBest_unique__answer_loop vals start (start + n - 1) b value Hb Hbest).
           subst b.
           rewrite Ha_eq.
           exact Hvalue_le.
    + exact Ha_eq.
Qed.
Lemma EnergyAnswerProgress_step_update__answer_loop :
  forall beads vals dp n total width start answer value,
    EnergyAnswerProgress beads vals dp n total width start answer ->
    0 <= start < n ->
    EnergyIntervalBest vals start (start + n - 1) value ->
    0 <= value <= 2100000000 ->
    answer < value ->
    EnergyAnswerProgress beads vals dp n total width (start + 1) value.
Proof.
  intros beads vals dp n total width start answer value
    Hprogress Hstart Hbest Hvalue_bounds Hanswer_lt.
  unfold EnergyAnswerProgress in *.
  destruct Hprogress as [Hvals [Hdp [Hwidth [Hstart_progress [Hanswer Hcase]]]]].
  split; [exact Hvals|].
  split; [exact Hdp|].
  split; [exact Hwidth|].
  split; [lia|].
  split; [exact Hvalue_bounds|].
  right.
  split; [lia|].
  unfold max_value_of_subset, max_object_of_subset.
  exists value.
  split.
  - split.
    + exists start.
      split; [lia|exact Hbest].
    + intros b [s [Hs Hb]].
      destruct (Z_lt_ge_dec s start) as [Hs_lt | Hs_ge].
      * destruct Hcase as [[Hstart0 _] | [_ Holdmax]].
        -- lia.
        -- unfold max_value_of_subset, max_object_of_subset in Holdmax.
           destruct Holdmax as [a [[Ha_in Ha_max] Ha_eq]].
           pose proof Ha_max b ltac:(exists s; split; [lia|exact Hb]) as Hb_le_a.
           rewrite Ha_eq in Hb_le_a.
           lia.
      * assert (s = start) by lia.
        subst s.
        pose proof
          (EnergyIntervalBest_unique__answer_loop vals start (start + n - 1) b value Hb Hbest).
        lia.
  - reflexivity.
Qed.
Lemma EnergyAnswerProgress_finish__answer_loop :
  forall beads vals dp n total width start answer,
    4 <= n ->
    EnergyAnswerProgress beads vals dp n total width start answer ->
    start >= n ->
    start <= n ->
    EnergyNecklaceAnswer beads n answer.
Proof.
  intros beads vals dp n total width start answer Hn Hprogress Hge Hle.
  unfold EnergyAnswerProgress in Hprogress.
  destruct Hprogress as [Hvals [_ [_ [Hstart [Hanswer Hcase]]]]].
  assert (start = n) by lia.
  subst start.
  destruct Hcase as [[Hzero _] | [_ Hmax]]; [lia|].
  unfold EnergyNecklaceAnswer.
  unfold max_value_of_subset, max_object_of_subset in *.
  destruct Hmax as [a [[Ha_in Ha_max] Ha_eq]].
  exists a.
  split.
  - split.
    + destruct Ha_in as [s [Hs Hbest]].
      exists s.
      split; [exact Hs|].
      unfold EnergyRotationBest.
      exists vals.
      split; [exact Hvals|].
      split; [exact Hs|exact Hbest].
    + intros b [s [Hs Hrot]].
      unfold EnergyRotationBest in Hrot.
      destruct Hrot as [vals' [Hvals' [_ Hbest']]].
      pose proof (EnergyValsDuplicated_unique__answer_loop beads vals' vals n Hvals' Hvals) as Heq.
      subst vals'.
      apply Ha_max.
      exists s.
      split; [exact Hs|exact Hbest'].
  - exact Ha_eq.
Qed.
