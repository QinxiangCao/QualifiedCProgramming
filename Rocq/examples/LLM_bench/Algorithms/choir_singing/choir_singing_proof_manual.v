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
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.choir_singing.choir_singing_lib.
Local Open Scope sac.
Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg.




Lemma proof_of_choir_singing_safety_wit_9 : choir_singing_safety_wit_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (choir_left_length_bounds _ _ _ (proj1 PreH10 j ltac:(lia))) as Hbounds.
  split_pures; dump_pre_spatial; try change INT_MAX with 2147483647; try change INT_MIN with (-2147483648); lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_11 : choir_singing_safety_wit_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (choir_left_length_bounds _ _ _ (proj1 PreH11 j ltac:(lia))) as Hbounds.
  split_pures; dump_pre_spatial; try change INT_MAX with 2147483647; try change INT_MIN with (-2147483648); lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_22 : choir_singing_safety_wit_22.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (choir_right_length_bounds _ _ _ (proj1 PreH11 j ltac:(lia))) as Hbounds.
  split_pures; dump_pre_spatial; try change INT_MAX with 2147483647; try change INT_MIN with (-2147483648); lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_24 : choir_singing_safety_wit_24.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (choir_right_length_bounds _ _ _ (proj1 PreH12 j ltac:(lia))) as Hbounds.
  split_pures; dump_pre_spatial; try change INT_MAX with 2147483647; try change INT_MIN with (-2147483648); lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_32 : choir_singing_safety_wit_32.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (choir_left_length_bounds _ _ _ (proj1 PreH9 k ltac:(lia))) as Hleft.
  pose proof (choir_right_length_bounds _ _ _ (proj1 PreH10 k ltac:(lia))) as Hright.
  split_pures; dump_pre_spatial; try change INT_MAX with 2147483647; try change INT_MIN with (-2147483648); lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_33 : choir_singing_safety_wit_33.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (choir_left_length_bounds _ _ _ (proj1 PreH10 k ltac:(lia))) as Hleft.
  pose proof (choir_right_length_bounds _ _ _ (proj1 PreH11 k ltac:(lia))) as Hright.
  split_pures; dump_pre_spatial; try change INT_MAX with 2147483647; try change INT_MIN with (-2147483648); lia.
Qed.

Lemma proof_of_choir_singing_safety_wit_34 : choir_singing_safety_wit_34.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (choir_left_length_bounds _ _ _ (proj1 PreH10 k ltac:(lia))) as Hleft.
  pose proof (choir_right_length_bounds _ _ _ (proj1 PreH11 k ltac:(lia))) as Hright.
  split_pures; dump_pre_spatial; try change INT_MAX with 2147483647; try change INT_MIN with (-2147483648); lia.
Qed.



Lemma proof_of_choir_singing_entail_wit_1 : choir_singing_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (@nil Z) (@nil Z).
  split_pure_spatial.
  - rewrite (IntArray.seg_empty (&( "dp_left" )) 0 0).
    rewrite (IntArray.seg_empty (&( "dp_right" )) 0 0).
    sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&( "dp_left" )) numsSize_pre 100 ltac:(lia)).
    sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&( "dp_right" )) numsSize_pre 100 ltac:(lia)).
    entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia; constructor.
Qed.

Lemma proof_of_choir_singing_entail_wit_2 : choir_singing_entail_wit_2.
Proof.
  aggressive_pre_process.
  all: apply Forall_app; split;
    [assumption | apply Forall_cons; [reflexivity | apply Forall_nil]].
Qed.

Lemma proof_of_choir_singing_entail_wit_3 : choir_singing_entail_wit_3.
Proof.
  aggressive_pre_process.
  replace i with numsSize_pre in * by lia.
  try rewrite (IntArray.undef_seg_empty (&( "dp_left" )) numsSize_pre).
  try rewrite (IntArray.undef_seg_empty (&( "dp_right" )) numsSize_pre).
  prop_apply (IntArray.seg_Zlength (&( "dp_left" )) 0 numsSize_pre left_written).
  Intros.
  Exists right_written left_written.
  split_pure_spatial.
  - sep_apply (IntArray.seg_to_full (&( "dp_left" )) 0 numsSize_pre left_written).
    replace ((&( "dp_left" )) + 0 * sizeof(INT)) with (&( "dp_left" )) by lia.
    replace (numsSize_pre - 0) with numsSize_pre by lia.
    sep_apply (IntArray.seg_to_full (&( "dp_right" )) 0 numsSize_pre right_written).
    replace ((&( "dp_right" )) + 0 * sizeof(INT)) with (&( "dp_right" )) by lia.
    replace (numsSize_pre - 0) with numsSize_pre by lia.
    entailer!.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    unfold ChoirDPLeftPrefix. split.
    + intros k Hk. lia.
    + rewrite sublist_self by lia. exact PreH7.
Qed.

Lemma proof_of_choir_singing_entail_wit_4 : choir_singing_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength (&( "dp_left" )) numsSize_pre left_values_2).
  Intros.
  Exists right_values_2 left_values_2.
  split_pure_spatial; [entailer! |].
  split_pures; dump_pre_spatial; try lia; try assumption.
  replace (i - 1 + 1) with i by lia.
  eapply choir_left_inner_progress_base__ones_initialization; eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_5_1 : choir_singing_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength (&( "dp_left" )) numsSize_pre (replace_Znth i (Znth j left_values_2 0 + 1) left_values_2)).
  Intros.
  try rewrite Zlength_replace_Znth in *.
  Exists right_values_2 (replace_Znth i (Znth j left_values_2 0 + 1) left_values_2).
  split_pure_spatial; [entailer! |].
  split_pures; dump_pre_spatial; try lia; try assumption.
  replace (j - 1 + 1) with j by lia.
  eapply choir_left_progress_step_update__left_dp_transitions; eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_5_2 : choir_singing_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength (&( "dp_left" )) numsSize_pre left_values_2).
  Intros.
  Exists right_values_2 left_values_2.
  split_pure_spatial; [entailer! |].
  split_pures; dump_pre_spatial; try lia; try assumption.
  replace (j - 1 + 1) with j by lia.
  eapply choir_left_progress_step_ineligible__left_dp_transitions; eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_5_3 : choir_singing_entail_wit_5_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength (&( "dp_left" )) numsSize_pre left_values_2).
  Intros.
  Exists right_values_2 left_values_2.
  split_pure_spatial; [entailer! |].
  split_pures; dump_pre_spatial; try lia; try assumption.
  replace (j - 1 + 1) with j by lia.
  eapply choir_left_progress_step_dominated__left_dp_transitions; eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_6 : choir_singing_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength (&( "dp_left" )) numsSize_pre left_values_2).
  Intros.
  Exists right_values_2 left_values_2.
  split_pure_spatial; [entailer! |].
  split_pures; dump_pre_spatial; try lia; try assumption.
  replace (j + 1) with 0 in PreH9 by lia.
  eapply choir_left_progress_complete__left_dp_transitions; eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_7 : choir_singing_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength (&( "dp_right" )) numsSize_pre right_values_2).
  Intros.
  Exists right_values_2 left_values_2.
  split_pure_spatial; [entailer! |].
  split_pures; dump_pre_spatial; try lia; try assumption.
  - replace numsSize_pre with i by lia. exact PreH7.
  - replace (numsSize_pre - 1 + 1) with (Zlength heights) by lia.
    eapply choir_right_suffix_from_ones__phase_bridges; eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_8 : choir_singing_entail_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength (&( "dp_right" )) numsSize_pre right_values_2).
  Intros.
  Exists right_values_2 left_values_2.
  split_pure_spatial; [entailer! |].
  split_pures; dump_pre_spatial; try lia; try assumption.
  eapply choir_right_inner_progress_base__phase_bridges; eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_9_1 : choir_singing_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength (&( "dp_right" )) numsSize_pre (replace_Znth i (Znth j right_values_2 0 + 1) right_values_2)).
  Intros.
  try rewrite Zlength_replace_Znth in *.
  Exists (replace_Znth i (Znth j right_values_2 0 + 1) right_values_2) left_values_2.
  split_pure_spatial; [entailer! |].
  split_pures; dump_pre_spatial; try lia; try assumption.
  eapply choir_right_progress_step_update__right_dp_transitions; eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_9_2 : choir_singing_entail_wit_9_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength (&( "dp_right" )) numsSize_pre right_values_2).
  Intros.
  Exists right_values_2 left_values_2.
  split_pure_spatial; [entailer! |].
  split_pures; dump_pre_spatial; try lia; try assumption.
  eapply choir_right_progress_step_ineligible__right_dp_transitions; eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_9_3 : choir_singing_entail_wit_9_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength (&( "dp_right" )) numsSize_pre right_values_2).
  Intros.
  Exists right_values_2 left_values_2.
  split_pure_spatial; [entailer! |].
  split_pures; dump_pre_spatial; try lia; try assumption.
  eapply choir_right_progress_step_dominated__right_dp_transitions; eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_10 : choir_singing_entail_wit_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength (&( "dp_right" )) numsSize_pre right_values_2).
  Intros.
  Exists right_values_2 left_values_2.
  split_pure_spatial; [entailer! |].
  split_pures; dump_pre_spatial; try lia; try assumption.
  replace (i - 1 + 1) with i by lia.
  replace j with (Zlength heights) in PreH10 by lia.
  eapply choir_right_progress_complete__right_dp_transitions; eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_11 : choir_singing_entail_wit_11.
Proof.
  aggressive_pre_process.
  - unfold ChoirBestPrefix. left. split; reflexivity.
  - replace (i + 1) with 0 in PreH8 by lia. exact PreH8.
Qed.

Lemma proof_of_choir_singing_entail_wit_12_1 : choir_singing_entail_wit_12_1.
Proof.
  aggressive_pre_process;
    subst numsSize_pre;
    pose proof (choir_peak_length_from_dp__best_prefix_fold
      heights left_values_2 right_values_2 k PreH10 PreH11 ltac:(lia))
      as [Hpeak Hbounds].
  - eapply choir_best_prefix_step_take__best_prefix_fold; eauto; lia.
  - lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_12_2 : choir_singing_entail_wit_12_2.
Proof.
  aggressive_pre_process;
    subst numsSize_pre;
    pose proof (choir_peak_length_from_dp__best_prefix_fold
      heights left_values_2 right_values_2 k PreH10 PreH11 ltac:(lia))
      as [Hpeak Hbounds].
  eapply choir_best_prefix_step_keep__best_prefix_fold; eauto; lia.
Qed.

Lemma proof_of_choir_singing_entail_wit_13 : choir_singing_entail_wit_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  split_pure_spatial.
  - prop_apply (IntArray.undef_seg_valid (&( "dp_left" )) (numsSize_pre) 100). Intros.
    sep_apply_l_atomic (IntArray.full_to_undef_full (&( "dp_left" )) (numsSize_pre) left_values).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&( "dp_left" )) (numsSize_pre)).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&( "dp_left" )) 0 (numsSize_pre) 100 ltac:(lia)).
    simpl. replace ((&( "dp_left" )) + 0) with (&( "dp_left" )) by lia.
    prop_apply (IntArray.undef_seg_valid (&( "dp_right" )) (numsSize_pre) 100). Intros.
    sep_apply_l_atomic (IntArray.full_to_undef_full (&( "dp_right" )) (numsSize_pre) right_values).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&( "dp_right" )) (numsSize_pre)).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&( "dp_right" )) 0 (numsSize_pre) 100 ltac:(lia)).
    simpl. replace ((&( "dp_right" )) + 0) with (&( "dp_right" )) by lia.
    entailer!.
  - split_pures; dump_pre_spatial; try lia.
    replace k with (Zlength heights) in PreH11 by lia.
    subst numsSize_pre.
    eapply choir_best_prefix_minimum_removals; eauto; lia.
Qed.