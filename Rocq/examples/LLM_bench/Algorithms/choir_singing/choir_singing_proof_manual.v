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
From SimpleC.EE.LLM_bench.Algorithms.choir_singing Require Import choir_singing_goal.
From SimpleC.EE.LLM_bench.Algorithms.choir_singing Require Import choir_singing_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.choir_singing.choir_singing_lib.
Local Open Scope sac.

Lemma proof_of_choir_singing_safety_wit_9_split_goal_1 : choir_singing_safety_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold ChoirLeftInnerProgress in PreH10.
  destruct PreH10 as [_ [_ [_ [Hprocessed _]]]].
  pose proof (Hprocessed j ltac:(lia)) as Hj_bounds.
  destruct Hj_bounds as [_ Hj_bounds].
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_9_split_goal_2 : choir_singing_safety_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold ChoirLeftInnerProgress in PreH10.
  destruct PreH10 as [_ [_ [_ [Hprocessed _]]]].
  pose proof (Hprocessed j ltac:(lia)) as Hj_bounds.
  destruct Hj_bounds as [_ Hj_bounds].
  change INT_MIN with (-2147483648).
  lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_9 : choir_singing_safety_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_choir_singing_safety_wit_9_split_goal_1.
  - Goal_apply proof_of_choir_singing_safety_wit_9_split_goal_2.
Qed.

Lemma proof_of_choir_singing_safety_wit_11_split_goal_1 : choir_singing_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold ChoirLeftInnerProgress in PreH11.
  destruct PreH11 as [_ [_ [_ [Hprocessed _]]]].
  pose proof (Hprocessed j ltac:(lia)) as Hj_bounds.
  destruct Hj_bounds as [_ Hj_bounds].
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_11_split_goal_2 : choir_singing_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold ChoirLeftInnerProgress in PreH11.
  destruct PreH11 as [_ [_ [_ [Hprocessed _]]]].
  pose proof (Hprocessed j ltac:(lia)) as Hj_bounds.
  destruct Hj_bounds as [_ Hj_bounds].
  change INT_MIN with (-2147483648).
  lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_11 : choir_singing_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_choir_singing_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_choir_singing_safety_wit_11_split_goal_2.
Qed.

Lemma proof_of_choir_singing_safety_wit_22_split_goal_1 : choir_singing_safety_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold ChoirRightInnerProgress in PreH11.
  destruct PreH11 as [_ [_ [_ [Hprocessed _]]]].
  pose proof (Hprocessed j ltac:(lia)) as Hj_bounds.
  destruct Hj_bounds as [_ Hj_bounds].
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_22_split_goal_2 : choir_singing_safety_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold ChoirRightInnerProgress in PreH11.
  destruct PreH11 as [_ [_ [_ [Hprocessed _]]]].
  pose proof (Hprocessed j ltac:(lia)) as Hj_bounds.
  destruct Hj_bounds as [_ Hj_bounds].
  change INT_MIN with (-2147483648).
  lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_22 : choir_singing_safety_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_choir_singing_safety_wit_22_split_goal_1.
  - Goal_apply proof_of_choir_singing_safety_wit_22_split_goal_2.
Qed.

Lemma proof_of_choir_singing_safety_wit_24_split_goal_1 : choir_singing_safety_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold ChoirRightInnerProgress in PreH12.
  destruct PreH12 as [_ [_ [_ [Hprocessed _]]]].
  pose proof (Hprocessed j ltac:(lia)) as Hj_bounds.
  destruct Hj_bounds as [_ Hj_bounds].
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_24_split_goal_2 : choir_singing_safety_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold ChoirRightInnerProgress in PreH12.
  destruct PreH12 as [_ [_ [_ [Hprocessed _]]]].
  pose proof (Hprocessed j ltac:(lia)) as Hj_bounds.
  destruct Hj_bounds as [_ Hj_bounds].
  change INT_MIN with (-2147483648).
  lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_24 : choir_singing_safety_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_choir_singing_safety_wit_24_split_goal_1.
  - Goal_apply proof_of_choir_singing_safety_wit_24_split_goal_2.
Qed.

Lemma proof_of_choir_singing_safety_wit_32_split_goal_1 : choir_singing_safety_wit_32_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold ChoirDPLeftPrefix in PreH9.
  unfold ChoirDPRightSuffix in PreH10.
  destruct PreH9 as (_ & _ & Hleft & _).
  destruct PreH10 as (_ & _ & Hright & _).
  specialize (Hleft k ltac:(lia)) as (_ & Hleft_bound).
  specialize (Hright k ltac:(lia)) as (_ & Hright_bound).
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_32_split_goal_2 : choir_singing_safety_wit_32_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold ChoirDPLeftPrefix in PreH9.
  unfold ChoirDPRightSuffix in PreH10.
  destruct PreH9 as (_ & _ & Hleft & _).
  destruct PreH10 as (_ & _ & Hright & _).
  specialize (Hleft k ltac:(lia)) as (_ & Hleft_bound).
  specialize (Hright k ltac:(lia)) as (_ & Hright_bound).
  change INT_MIN with (-2147483648).
  lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_32 : choir_singing_safety_wit_32.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_choir_singing_safety_wit_32_split_goal_1.
  - Goal_apply proof_of_choir_singing_safety_wit_32_split_goal_2.
Qed.

Lemma proof_of_choir_singing_safety_wit_33_split_goal_1 : choir_singing_safety_wit_33_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold ChoirDPLeftPrefix in PreH10.
  unfold ChoirDPRightSuffix in PreH11.
  destruct PreH10 as (_ & _ & Hleft & _).
  destruct PreH11 as (_ & _ & Hright & _).
  specialize (Hleft k ltac:(lia)) as (_ & Hleft_bound).
  specialize (Hright k ltac:(lia)) as (_ & Hright_bound).
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_33_split_goal_2 : choir_singing_safety_wit_33_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_choir_singing_safety_wit_33 : choir_singing_safety_wit_33.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_choir_singing_safety_wit_33_split_goal_1.
  - Goal_apply proof_of_choir_singing_safety_wit_33_split_goal_2.
Qed.

Lemma proof_of_choir_singing_safety_wit_34_split_goal_1 : choir_singing_safety_wit_34_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold ChoirDPLeftPrefix in PreH10.
  unfold ChoirDPRightSuffix in PreH11.
  destruct PreH10 as (_ & _ & Hleft & _).
  destruct PreH11 as (_ & _ & Hright & _).
  specialize (Hleft k ltac:(lia)) as (_ & Hleft_bound).
  specialize (Hright k ltac:(lia)) as (_ & Hright_bound).
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_34_split_goal_2 : choir_singing_safety_wit_34_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_choir_singing_safety_wit_34 : choir_singing_safety_wit_34.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_choir_singing_safety_wit_34_split_goal_1.
  - Goal_apply proof_of_choir_singing_safety_wit_34_split_goal_2.
Qed.

Lemma proof_of_choir_singing_entail_wit_1_split_goal_1 : choir_singing_entail_wit_1_split_goal_1.
Proof.
  unfold choir_singing_entail_wit_1_split_goal_1.
  intros.
  unfold ChoirOnesPrefix.
  split.
  - reflexivity.
  - intros k Hk.
    lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_1_split_goal_2 : choir_singing_entail_wit_1_split_goal_2.
Proof.
  unfold choir_singing_entail_wit_1_split_goal_2.
  intros.
  unfold ChoirOnesPrefix.
  split.
  - reflexivity.
  - intros k Hk.
    lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_1 : choir_singing_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_choir_singing_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_choir_singing_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_choir_singing_entail_wit_2_split_goal_1 : choir_singing_entail_wit_2_split_goal_1.
Proof.
  unfold choir_singing_entail_wit_2_split_goal_1.
  intros.
  apply choir_ones_prefix_snoc__ones_initialization.
  exact PreH8.
Qed.

Lemma proof_of_choir_singing_entail_wit_2_split_goal_2 : choir_singing_entail_wit_2_split_goal_2.
Proof.
  unfold choir_singing_entail_wit_2_split_goal_2.
  intros.
  apply choir_ones_prefix_snoc__ones_initialization.
  exact PreH7.
Qed.

Lemma proof_of_choir_singing_entail_wit_2 : choir_singing_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_choir_singing_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_choir_singing_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_choir_singing_entail_wit_3 : choir_singing_entail_wit_3.
Proof.
  aggressive_pre_process.
  replace i with numsSize_pre in * by lia.
  Exists right_written left_written.
  split_pure_spatial.
  - sep_apply (IntArray.seg_to_full dp_left_pre 0 numsSize_pre left_written).
    replace (dp_left_pre + 0 * sizeof(INT)) with dp_left_pre by lia.
    replace (numsSize_pre - 0) with numsSize_pre by lia.
    sep_apply (IntArray.seg_to_full dp_right_pre 0 numsSize_pre right_written).
    replace (dp_right_pre + 0 * sizeof(INT)) with dp_right_pre by lia.
    replace (numsSize_pre - 0) with numsSize_pre by lia.
    cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_choir_singing_entail_wit_4_split_goal_1 : choir_singing_entail_wit_4_split_goal_1.
Proof.
  unfold choir_singing_entail_wit_4_split_goal_1.
  intros.
  unfold ChoirDPLeftPrefix.
  unfold ChoirOnesFull in PreH4.
  destruct PreH4 as [Hleft_length Hleft_ones].
  split.
  - rewrite PreH3.
    lia.
  - split.
    + lia.
    + split.
      * intros k Hk.
        lia.
      * intros k Hk.
        apply Hleft_ones.
        lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_4 : choir_singing_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_choir_singing_entail_wit_5_split_goal_1 : choir_singing_entail_wit_5_split_goal_1.
Proof.
  unfold choir_singing_entail_wit_5_split_goal_1.
  intros.
  replace (i - 1 + 1) with i by lia.
  apply choir_left_inner_progress_base__ones_initialization.
  - exact PreH7.
  - rewrite PreH4.
    lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_5 : choir_singing_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_choir_singing_entail_wit_6_1_split_goal_1 : choir_singing_entail_wit_6_1_split_goal_1.
Proof.
  unfold choir_singing_entail_wit_6_1_split_goal_1.
  intros.
  replace ((j - 1) + 1) with j by lia.
  eapply choir_left_progress_step_update__left_dp_transitions; eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_6_1 : choir_singing_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_6_1_split_goal_1.
Qed.

Lemma proof_of_choir_singing_entail_wit_6_2_split_goal_1 : choir_singing_entail_wit_6_2_split_goal_1.
Proof.
  unfold choir_singing_entail_wit_6_2_split_goal_1.
  intros.
  replace ((j - 1) + 1) with j by lia.
  eapply choir_left_progress_step_ineligible__left_dp_transitions; eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_6_2 : choir_singing_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_6_2_split_goal_1.
Qed.

Lemma proof_of_choir_singing_entail_wit_6_3_split_goal_1 : choir_singing_entail_wit_6_3_split_goal_1.
Proof.
  unfold choir_singing_entail_wit_6_3_split_goal_1.
  intros.
  replace ((j - 1) + 1) with j by lia.
  eapply choir_left_progress_step_dominated__left_dp_transitions; eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_6_3 : choir_singing_entail_wit_6_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_6_3_split_goal_1.
Qed.

Lemma proof_of_choir_singing_entail_wit_7_split_goal_1 : choir_singing_entail_wit_7_split_goal_1.
Proof.
  unfold choir_singing_entail_wit_7_split_goal_1.
  intros.
  assert (j = -1) by lia.
  subst j.
  replace (-1 + 1) with 0 in PreH9 by lia.
  eapply choir_left_progress_complete__left_dp_transitions.
  exact PreH9.
Qed.

Lemma proof_of_choir_singing_entail_wit_7 : choir_singing_entail_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_7_split_goal_1.
Qed.

Lemma proof_of_choir_singing_entail_wit_9_split_goal_1 : choir_singing_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  replace i with numsSize_pre in PreH7 by lia.
  exact PreH7.
Qed.

Lemma proof_of_choir_singing_entail_wit_9 : choir_singing_entail_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_9_split_goal_1.
Qed.

Lemma proof_of_choir_singing_entail_wit_10_split_goal_1 : choir_singing_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  replace ((numsSize_pre - 1) + 1) with numsSize_pre by lia.
  eapply choir_right_suffix_from_ones__phase_bridges; eauto.
Qed.

Lemma proof_of_choir_singing_entail_wit_10 : choir_singing_entail_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_10_split_goal_1.
Qed.

Lemma proof_of_choir_singing_entail_wit_11_split_goal_1 : choir_singing_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  apply choir_right_inner_progress_base__phase_bridges.
  - lia.
  - exact PreH8.
Qed.

Lemma proof_of_choir_singing_entail_wit_11 : choir_singing_entail_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_11_split_goal_1.
Qed.

Lemma proof_of_choir_singing_entail_wit_12_1_split_goal_1 : choir_singing_entail_wit_12_1_split_goal_1.
Proof.
  intros numsSize_pre heights right_values_2 left_values_2 j i
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    PreH7 PreH8 PreH9 PreH10 PreH11 PreH12.
  eapply choir_right_progress_step_update__right_dp_transitions.
  - exact PreH12.
  - lia.
  - exact PreH2.
  - lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_12_1 : choir_singing_entail_wit_12_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_12_1_split_goal_1.
Qed.

Lemma proof_of_choir_singing_entail_wit_12_2_split_goal_1 : choir_singing_entail_wit_12_2_split_goal_1.
Proof.
  intros numsSize_pre heights right_values_2 left_values_2 j i
    PreH1 PreH2 PreH3 PreH4 PreH5
    PreH6 PreH7 PreH8 PreH9 PreH10 PreH11.
  eapply choir_right_progress_step_ineligible__right_dp_transitions.
  - exact PreH11.
  - lia.
  - lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_12_2 : choir_singing_entail_wit_12_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_12_2_split_goal_1.
Qed.

Lemma proof_of_choir_singing_entail_wit_12_3_split_goal_1 : choir_singing_entail_wit_12_3_split_goal_1.
Proof.
  intros numsSize_pre heights right_values_2 left_values_2 j i
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    PreH7 PreH8 PreH9 PreH10 PreH11 PreH12.
  eapply choir_right_progress_step_dominated__right_dp_transitions.
  - exact PreH12.
  - lia.
  - exact PreH2.
  - exact PreH1.
Qed.

Lemma proof_of_choir_singing_entail_wit_12_3 : choir_singing_entail_wit_12_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_12_3_split_goal_1.
Qed.

Lemma proof_of_choir_singing_entail_wit_13_split_goal_1 : choir_singing_entail_wit_13_split_goal_1.
Proof.
  intros numsSize_pre heights right_values_2 left_values_2 j i
    PreH1 PreH2 PreH3 PreH4 PreH5
    PreH6 PreH7 PreH8 PreH9 PreH10.
  assert (j = numsSize_pre) by lia.
  subst j.
  apply choir_right_progress_complete__right_dp_transitions.
  rewrite PreH4.
  exact PreH10.
Qed.

Lemma proof_of_choir_singing_entail_wit_13 : choir_singing_entail_wit_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_13_split_goal_1.
Qed.

Lemma proof_of_choir_singing_entail_wit_14_split_goal_1 : choir_singing_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  replace ((i - 1) + 1) with i by lia.
  exact PreH7.
Qed.

Lemma proof_of_choir_singing_entail_wit_14 : choir_singing_entail_wit_14.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_14_split_goal_1.
Qed.

Lemma proof_of_choir_singing_entail_wit_15_split_goal_1 : choir_singing_entail_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(auto).
  replace (i + 1) with 0 in PreH8 by lia.
  exact PreH8.
Qed.

Lemma proof_of_choir_singing_entail_wit_15 : choir_singing_entail_wit_15.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_15_split_goal_1.
Qed.

Lemma proof_of_choir_singing_entail_wit_16_split_goal_1 : choir_singing_entail_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  unfold ChoirBestPrefix.
  split; [lia |].
  left.
  lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_16 : choir_singing_entail_wit_16.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_16_split_goal_1.
Qed.

Lemma proof_of_choir_singing_entail_wit_17_1_split_goal_1 : choir_singing_entail_wit_17_1_split_goal_1.
Proof.
  unfold choir_singing_entail_wit_17_1_split_goal_1.
  intros.
  subst numsSize_pre.
  pose proof
    (choir_peak_length_from_dp__best_prefix_fold
       heights left_values_2 right_values_2 k
       PreH10 PreH11 ltac:(lia))
    as [Hpeak Hpeak_bounds].
  eapply choir_best_prefix_step_take__best_prefix_fold; eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_17_1_split_goal_2 : choir_singing_entail_wit_17_1_split_goal_2.
Proof.
  unfold choir_singing_entail_wit_17_1_split_goal_2.
  intros.
  subst numsSize_pre.
  pose proof
    (choir_peak_length_from_dp__best_prefix_fold
       heights left_values_2 right_values_2 k
       PreH10 PreH11 ltac:(lia))
    as [Hpeak Hpeak_bounds].
  lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_17_1 : choir_singing_entail_wit_17_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_17_1_split_goal_1.
  Goal_apply proof_of_choir_singing_entail_wit_17_1_split_goal_2.
Qed.

Lemma proof_of_choir_singing_entail_wit_17_2_split_goal_1 : choir_singing_entail_wit_17_2_split_goal_1.
Proof.
  unfold choir_singing_entail_wit_17_2_split_goal_1.
  intros.
  subst numsSize_pre.
  pose proof
    (choir_peak_length_from_dp__best_prefix_fold
       heights left_values_2 right_values_2 k
       PreH10 PreH11 ltac:(lia))
    as [Hpeak [Hpeak_positive Hpeak_bound]].
  eapply choir_best_prefix_step_keep__best_prefix_fold; eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_17_2 : choir_singing_entail_wit_17_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_17_2_split_goal_1.
Qed.

Lemma proof_of_choir_singing_entail_wit_18_split_goal_1 : choir_singing_entail_wit_18_split_goal_1.
Proof.
  unfold choir_singing_entail_wit_18_split_goal_1.
  intros.
  assert (k = numsSize_pre) by lia.
  subst k.
  exact PreH11.
Qed.

Lemma proof_of_choir_singing_entail_wit_18_split_goal_2 : choir_singing_entail_wit_18_split_goal_2.
Proof.
  unfold choir_singing_entail_wit_18_split_goal_2.
  intros.
  assert (k = numsSize_pre) by lia.
  subst k.
  subst numsSize_pre.
  eapply
    (choir_best_prefix_positive__best_prefix_fold
       heights left_values_2 right_values_2
       (Zlength heights) max_choir);
    eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_18 : choir_singing_entail_wit_18.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_entail_wit_18_split_goal_1.
  Goal_apply proof_of_choir_singing_entail_wit_18_split_goal_2.
Qed.

Lemma proof_of_choir_singing_return_wit_1_split_goal_1 : choir_singing_return_wit_1_split_goal_1.
Proof.
  intros numsSize_pre heights left_values_2 right_values_2 max_choir
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8.
  unfold ChoirMinimumRemovals.
  exists max_choir.
  split.
  - unfold ChoirLength.
    rewrite PreH3.
    exact PreH8.
  - rewrite PreH3.
    reflexivity.
Qed.

Lemma proof_of_choir_singing_return_wit_1 : choir_singing_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_choir_singing_return_wit_1_split_goal_1.
Qed.
