Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.max_sum_increasing_sequence Require Import max_sum_increasing_sequence_goal.
From SimpleC.EE.LLM_bench.Algorithms.max_sum_increasing_sequence Require Import max_sum_increasing_sequence_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.max_sum_increasing_sequence.max_sum_increasing_sequence_lib.
Local Open Scope sac.

Lemma proof_of_maxSumIncreasingSequence_safety_wit_6_split_goal_1 : maxSumIncreasingSequence_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof
    (msis_inner_progress_entry_bound__inner_transitions
       l d i j j PreH13 ltac:(lia)) as Hj.
  pose proof (PreH14 i ltac:(lia)) as Hi_value.
  replace (j - 0) with j by lia.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_maxSumIncreasingSequence_safety_wit_6_split_goal_2 : maxSumIncreasingSequence_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof
    (msis_inner_progress_entry_bound__inner_transitions
       l d i j j PreH13 ltac:(lia)) as Hj.
  pose proof (PreH14 i ltac:(lia)) as Hi_value.
  replace (j - 0) with j by lia.
  change INT_MIN with (-2147483648).
  lia.
Qed.

Lemma proof_of_maxSumIncreasingSequence_safety_wit_6 : maxSumIncreasingSequence_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSumIncreasingSequence_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_maxSumIncreasingSequence_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_1 : maxSumIncreasingSequence_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hvalue0 : 1 <= Znth 0 l 0 <= 10000).
  { apply PreH4. lia. }
  pose proof
    (msis_initial_semantics__initialization l ltac:(rewrite PreH3; lia))
    as [Hending0 Hprefix1].
  Exists (Znth 0 l 0 :: nil).
  split_pure_spatial.
  - sep_apply (IntArray.seg_single dp_pre 0 (Znth 0 l 0)).
    replace (0 + 1) with 1 by lia.
    cancel (IntArray.full nums_pre numsSize_pre l).
    cancel (IntArray.seg dp_pre 0 1 (Znth 0 l 0 :: nil)).
    cancel (IntArray.undef_seg dp_pre 1 numsSize_pre).
  - split_pures.
    all: try (dump_pre_spatial; try assumption; try lia).
    + unfold MSISDPTablePrefix.
      split; [rewrite PreH3; lia |].
      split.
      * rewrite Zlength_cons, Zlength_nil. lia.
      * intros k Hk.
        assert (k = 0) by lia.
        subst k.
        simpl.
        split; assumption.
    + unfold MSISBestSoFar.
      split; [rewrite PreH3; lia | exact Hprefix1].
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_2_split_goal_1 : maxSumIncreasingSequence_entail_wit_2_split_goal_1.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_2_split_goal_1.
  intros.
  apply PreH11.
  assumption.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_2_split_goal_2 : maxSumIncreasingSequence_entail_wit_2_split_goal_2.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_2_split_goal_2.
  intros.
  apply msis_inner_progress_zero__initialization.
  - exact PreH9.
  - rewrite PreH4. lia.
  - apply PreH11. lia.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_2 : maxSumIncreasingSequence_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_3_1 : maxSumIncreasingSequence_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists
    (replace_Znth i
       (Znth (j - 0) d_2 0 + Znth i l 0) d_2).
  split_pure_spatial.
  - sep_apply_l_atomic
      (IntArray.full_to_seg dp_pre (i + 1)
        (replace_Znth i
          (Znth (j - 0) d_2 0 + Znth i l 0) d_2)).
    repeat cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    pose proof (PreH15 i ltac:(lia)) as Hi_value.
    replace (j - 0) with j by lia.
    replace (j - 0) with j in PreH1 by lia.
    replace (i - 0) with i in PreH1 by lia.
    eapply
      (replace_Znth_inner_progress_step__inner_transitions
        l d_2 i j).
    + exact PreH14.
    + lia.
    + exact PreH2.
    + lia.
    + exact Hi_value.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_3_2_split_goal_1 : maxSumIncreasingSequence_entail_wit_3_2_split_goal_1.
Proof.
  intros numsSize_pre l d_2 ans j i
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
    PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15.
  replace (j - 0) with j in PreH1 by lia.
  replace (i - 0) with i in PreH1 by lia.
  eapply
    (msis_inner_progress_skip_dominated__inner_transitions
      l d_2 i j).
  - exact PreH14.
  - lia.
  - exact PreH2.
  - exact PreH1.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_3_2 : maxSumIncreasingSequence_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  Goal_apply
    proof_of_maxSumIncreasingSequence_entail_wit_3_2_split_goal_1.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_3_3_split_goal_1 : maxSumIncreasingSequence_entail_wit_3_3_split_goal_1.
Proof.
  intros numsSize_pre l d_2 ans j i
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
    PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14.
  eapply
    (msis_inner_progress_skip_nonincreasing__inner_transitions
      l d_2 i j).
  - exact PreH13.
  - lia.
  - lia.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_3_3 : maxSumIncreasingSequence_entail_wit_3_3.
Proof.
  aggressive_pre_process.
  Goal_apply
    proof_of_maxSumIncreasingSequence_entail_wit_3_3_split_goal_1.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_4_split_goal_1 : maxSumIncreasingSequence_entail_wit_4_split_goal_1.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_4_split_goal_1.
  intros numsSize_pre l d_2 ans j i
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
    PreH8 PreH9 PreH10 PreH11 PreH12 PreH13.
  exact PreH13.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_4_split_goal_2 : maxSumIncreasingSequence_entail_wit_4_split_goal_2.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_4_split_goal_2.
  intros numsSize_pre l d_2 ans j i
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
    PreH8 PreH9 PreH10 PreH11 PreH12 PreH13.
  assert (j = i) by lia.
  subst j.
  apply msis_inner_complete_dp_prefix__outer_transitions.
  exact PreH12.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_4 : maxSumIncreasingSequence_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_5_1_split_goal_1 : maxSumIncreasingSequence_entail_wit_5_1_split_goal_1.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_5_1_split_goal_1.
  intros numsSize_pre l d_2 i ans
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    PreH7 PreH8 PreH9 PreH10 PreH11.
  exact PreH11.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_5_1_split_goal_2 : maxSumIncreasingSequence_entail_wit_5_1_split_goal_2.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_5_1_split_goal_2.
  intros numsSize_pre l d_2 i ans
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    PreH7 PreH8 PreH9 PreH10 PreH11.
  assert (Hending : MSISEndingAt l i (Znth i d_2 0)).
  {
    unfold MSISDPTablePrefix in PreH10.
    destruct PreH10 as [_ [_ Hentries]].
    exact (proj1 (Hentries i ltac:(lia))).
  }
  pose proof
    (msis_prefix_extend_by_ending__outer_transitions
      l i ans (Znth i d_2 0) PreH9 Hending) as Hstep.
  replace (i - 0) with i in PreH1 by lia.
  replace (i - 0) with i by lia.
  rewrite Z.max_r in Hstep by lia.
  exact Hstep.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_5_1_split_goal_3 : maxSumIncreasingSequence_entail_wit_5_1_split_goal_3.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_5_1_split_goal_3.
  intros numsSize_pre l d_2 i ans
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    PreH7 PreH8 PreH9 PreH10 PreH11.
  replace (i - 0) with i by lia.
  unfold MSISDPTablePrefix in PreH10.
  destruct PreH10 as [_ [_ Hentries]].
  exact (proj2 (proj2 (Hentries i ltac:(lia)))).
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_5_1 : maxSumIncreasingSequence_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_5_1_split_goal_1.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_5_1_split_goal_2.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_5_1_split_goal_3.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_5_2_split_goal_1 : maxSumIncreasingSequence_entail_wit_5_2_split_goal_1.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_5_2_split_goal_1.
  intros numsSize_pre l d_2 i ans
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    PreH7 PreH8 PreH9 PreH10 PreH11.
  exact PreH11.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_5_2_split_goal_2 : maxSumIncreasingSequence_entail_wit_5_2_split_goal_2.
Proof.
  unfold maxSumIncreasingSequence_entail_wit_5_2_split_goal_2.
  intros numsSize_pre l d_2 i ans
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    PreH7 PreH8 PreH9 PreH10 PreH11.
  assert (Hending : MSISEndingAt l i (Znth i d_2 0)).
  {
    unfold MSISDPTablePrefix in PreH10.
    destruct PreH10 as [_ [_ Hentries]].
    exact (proj1 (Hentries i ltac:(lia))).
  }
  pose proof
    (msis_prefix_extend_by_ending__outer_transitions
      l i ans (Znth i d_2 0) PreH9 Hending) as Hstep.
  replace (i - 0) with i in PreH1 by lia.
  rewrite Z.max_l in Hstep by lia.
  exact Hstep.
Qed.

Lemma proof_of_maxSumIncreasingSequence_entail_wit_5_2 : maxSumIncreasingSequence_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_5_2_split_goal_1.
  - Goal_apply proof_of_maxSumIncreasingSequence_entail_wit_5_2_split_goal_2.
Qed.

Lemma proof_of_maxSumIncreasingSequence_return_wit_1 : maxSumIncreasingSequence_return_wit_1.
Proof.
  aggressive_pre_process.
  - replace i with numsSize_pre in * by lia.
    Exists d_2.
    split_pure_spatial.
    + sep_apply (IntArray.seg_to_full dp_pre 0 numsSize_pre d_2).
      replace (dp_pre + 0 * sizeof(INT)) with dp_pre by lia.
      replace (numsSize_pre - 0) with numsSize_pre by lia.
      cancel.
    + split_pures; dump_pre_spatial; try lia; try assumption.
      unfold MSISMaximum.
      rewrite PreH4.
      exact (proj2 PreH10).
Qed.
