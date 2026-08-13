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
From SimpleC.EE.LLM_bench.Algorithms.longest_increasing_subsequence Require Import longest_increasing_subsequence_goal.
From SimpleC.EE.LLM_bench.Algorithms.longest_increasing_subsequence Require Import longest_increasing_subsequence_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.longest_increasing_subsequence.longest_increasing_subsequence_lib.
Local Open Scope sac.

Lemma proof_of_lengthOfLIS_safety_wit_5_split_goal_1 : lengthOfLIS_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pures.
  all: dump_pre_spatial; try lia; try assumption.
  pose proof
    (lis_inner_progress_entry_bound__inner_foundations
       l d i j j PreH13 ltac:(lia)) as Hj.
  replace (j - 0) with j by lia.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_lengthOfLIS_safety_wit_5_split_goal_2 : lengthOfLIS_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  pose proof
    (lis_inner_progress_entry_bound__inner_foundations
       l d i j j PreH13 ltac:(lia)) as Hj.
  change INT_MIN with (-2147483648).
  replace (j - 0) with j by lia.
  destruct Hj as [Hj_lower Hj_upper].
  apply Z.le_trans with (m := 1).
  - lia.
  - lia.
Qed.

Lemma proof_of_lengthOfLIS_safety_wit_5 : lengthOfLIS_safety_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lengthOfLIS_safety_wit_5_split_goal_1.
  Goal_apply proof_of_lengthOfLIS_safety_wit_5_split_goal_2.
Qed. 

Lemma proof_of_lengthOfLIS_entail_wit_1_split_goal_1 : lengthOfLIS_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  unfold LISBestSoFar.
  split; [lia |].
  left; lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_1_split_goal_2 : lengthOfLIS_entail_wit_1_split_goal_2.
Proof.
  unfold lengthOfLIS_entail_wit_1_split_goal_2.
  intros.
  unfold LISDPTablePrefix.
  split.
  - rewrite PreH3; lia.
  - split.
    + rewrite Zlength_nil; reflexivity.
    + intros k Hk; lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_1 : lengthOfLIS_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lengthOfLIS_entail_wit_1_split_goal_1.
  Goal_apply proof_of_lengthOfLIS_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_2_split_goal_1 : lengthOfLIS_entail_wit_2_split_goal_1.
Proof.
  unfold lengthOfLIS_entail_wit_2_split_goal_1.
  intros.
  apply lis_inner_progress_init__inner_foundations.
  - exact PreH9.
  - rewrite PreH4; lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_2 : lengthOfLIS_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lengthOfLIS_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_3_1 : lengthOfLIS_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (replace_Znth i (Znth (j - 0) d_2 0 + 1) d_2).
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.full_to_seg dp_pre (i + 1)
      (replace_Znth i (Znth (j - 0) d_2 0 + 1) d_2)).
    repeat cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    replace (j - 0) with j by lia.
    replace (j - 0) with j in PreH1 by lia.
    replace (i - 0) with i in PreH1 by lia.
    eapply (lis_inner_progress_take_candidate__inner_transitions l d_2 i j).
    + exact PreH14.
    + lia.
    + exact PreH2.
    + lia.
Qed. 

Lemma proof_of_lengthOfLIS_entail_wit_3_2_split_goal_1 : lengthOfLIS_entail_wit_3_2_split_goal_1.
Proof.
  intros numsSize_pre l d_2 ans j i
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
    PreH9 PreH10 PreH11 PreH12 PreH13 PreH14.
  replace (j - 0) with j in PreH1 by lia.
  replace (i - 0) with i in PreH1 by lia.
  eapply (lis_inner_progress_skip_dominated__inner_transitions l d_2 i j).
  - exact PreH14.
  - lia.
  - exact PreH2.
  - exact PreH1.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_3_2 : lengthOfLIS_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lengthOfLIS_entail_wit_3_2_split_goal_1.
Qed. 

Lemma proof_of_lengthOfLIS_entail_wit_3_3_split_goal_1 : lengthOfLIS_entail_wit_3_3_split_goal_1.
Proof.
  intros numsSize_pre l d_2 ans j i
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
    PreH9 PreH10 PreH11 PreH12 PreH13.
  eapply (lis_inner_progress_skip_nonincreasing__inner_transitions l d_2 i j).
  - exact PreH13.
  - lia.
  - lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_3_3 : lengthOfLIS_entail_wit_3_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lengthOfLIS_entail_wit_3_3_split_goal_1.
Qed. 

Lemma proof_of_lengthOfLIS_entail_wit_4_split_goal_1 : lengthOfLIS_entail_wit_4_split_goal_1.
Proof.
  intros numsSize_pre l d_2 ans j i
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
    PreH9 PreH10 PreH11 PreH12.
  assert (j = i) by lia. subst j.
  apply lis_inner_progress_complete__inner_transitions.
  exact PreH12.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_4 : lengthOfLIS_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lengthOfLIS_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_5_1_split_goal_1 : lengthOfLIS_entail_wit_5_1_split_goal_1.
Proof.
  unfold lengthOfLIS_entail_wit_5_1_split_goal_1.
  intros.
  replace (i - 0) with i in * by lia.
  pose proof (lis_dp_table_entry_bounds__outer_best_update
    l d (i + 1) i PreH10 ltac:(lia)) as [Hending Hbounds].
  unfold LISBestSoFar in PreH9.
  destruct PreH9 as [_ [[Hzero Hans] | [Hpositive Hprefix]]].
  - exfalso. lia.
  - replace (Znth i d 0) with (Z.max ans (Znth i d 0)) by lia.
    eapply lis_best_so_far_step__outer_best_update; eauto; lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_5_1_split_goal_2 : lengthOfLIS_entail_wit_5_1_split_goal_2.
Proof.
  unfold lengthOfLIS_entail_wit_5_1_split_goal_2.
  intros.
  replace (i - 0) with i in * by lia.
  pose proof (lis_dp_table_entry_bounds__outer_best_update
    l d (i + 1) i PreH10 ltac:(lia)) as [_ Hbounds].
  lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_5_2_split_goal_1 : lengthOfLIS_entail_wit_5_2_split_goal_1.
Proof.
  unfold lengthOfLIS_entail_wit_5_2_split_goal_1.
  intros.
  replace (i - 0) with i in * by lia.
  pose proof (lis_dp_table_entry_bounds__outer_best_update
    l d_2 (i + 1) i PreH10 ltac:(lia)) as [Hending Hbounds].
  unfold LISBestSoFar in PreH9.
  destruct PreH9 as [_ [[Hzero Hans] | [Hpositive Hprefix]]].
  - subst i ans.
    assert (Hcur : Znth 0 d_2 0 = 1) by lia.
    rewrite Hcur in Hending.
    change (LISBestSoFar l (0 + 1) 1) with
      (LISBestSoFar l (0 + 1) (Z.max 0 1)).
    eapply (lis_best_so_far_step__outer_best_update l 0 0 1).
    + lia.
    + apply lis_prefix_empty__outer_best_update.
    + exact Hending.
  - replace ans with (Z.max ans (Znth i d_2 0)) by lia.
    eapply lis_best_so_far_step__outer_best_update; eauto; lia.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_5_2 : lengthOfLIS_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lengthOfLIS_entail_wit_5_2_split_goal_1.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_5_1 : lengthOfLIS_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_lengthOfLIS_entail_wit_5_1_split_goal_1.
  Goal_apply proof_of_lengthOfLIS_entail_wit_5_1_split_goal_2.
Qed.

Lemma proof_of_lengthOfLIS_entail_wit_7 : lengthOfLIS_entail_wit_7.
Proof.
  aggressive_pre_process.
  replace i with numsSize_pre in * by lia.
  Exists d_2.
  split_pure_spatial.
  - sep_apply (IntArray.seg_to_full dp_pre 0 numsSize_pre d_2).
    replace (dp_pre + 0 * sizeof(INT)) with dp_pre by lia.
    replace (numsSize_pre - 0) with numsSize_pre by lia.
    cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    apply (lis_best_so_far_full_implies_length__final_result l numsSize_pre ans).
    + lia.
    + exact PreH4.
    + exact PreH10.
Qed.
