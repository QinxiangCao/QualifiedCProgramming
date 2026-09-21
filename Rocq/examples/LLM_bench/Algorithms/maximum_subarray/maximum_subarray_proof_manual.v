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
From SimpleC.EE.LLM_bench.Algorithms.maximum_subarray Require Import maximum_subarray_goal.
From SimpleC.EE.LLM_bench.Algorithms.maximum_subarray Require Import maximum_subarray_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_lib.
Local Open Scope sac.
Require Import AUXLib.MonotonicList.

Lemma input_Znth_bounds : forall l k,
  Forall (Z.le (-10000)) l -> Forall (Z.ge 10000) l ->
  0 <= k < Zlength l -> -10000 <= Znth k l 0 <= 10000.
Proof.
  intros l k Hlo Hhi Hk.
  pose proof (proj1 (Forall_Znth _ 0 _) Hlo k Hk).
  pose proof (proj1 (Forall_Znth _ 0 _) Hhi k Hk). lia.
Qed.

Lemma proof_of_max_return_wit_1_split_goal_1 : max_return_wit_1_split_goal_1.
Proof.
  unfold max_return_wit_1_split_goal_1; intros; unfold max_Z; rewrite Z.max_l by lia; reflexivity.
Qed.

Lemma proof_of_max_return_wit_1 : max_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_max_return_wit_1_split_goal_1.

Qed. 

Lemma proof_of_max_return_wit_2_split_goal_1 : max_return_wit_2_split_goal_1.
Proof.
  unfold max_return_wit_2_split_goal_1; intros; unfold max_Z; rewrite Z.max_r by lia; reflexivity.
Qed.

Lemma proof_of_max_return_wit_2 : max_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_max_return_wit_2_split_goal_1.

Qed. 

Lemma proof_of_max_sub_array_safety_wit_6_split_goal_1 : max_sub_array_safety_wit_6_split_goal_1.
Proof.
  unfold max_sub_array_safety_wit_6_split_goal_1; intros.
  pose proof (input_Znth_bounds l i PreH13 PreH14 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_max_sub_array_safety_wit_6_split_goal_2 : max_sub_array_safety_wit_6_split_goal_2.
Proof.
  unfold max_sub_array_safety_wit_6_split_goal_2; intros.
  pose proof (input_Znth_bounds l i PreH13 PreH14 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_max_sub_array_safety_wit_6 : max_sub_array_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_max_sub_array_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_max_sub_array_safety_wit_6_split_goal_2.

Qed. 

Lemma proof_of_max_sub_array_entail_wit_1_split_goal_1 : max_sub_array_entail_wit_1_split_goal_1.
Proof.
  unfold max_sub_array_entail_wit_1_split_goal_1; intros.
  apply MaxSubarraySumPrefix_single; lia.
Qed.

Lemma proof_of_max_sub_array_entail_wit_1_split_goal_2 : max_sub_array_entail_wit_1_split_goal_2.
Proof.
  unfold max_sub_array_entail_wit_1_split_goal_2; intros.
  apply MaxSuffixSumPrefix_single; lia.
Qed.

Lemma proof_of_max_sub_array_entail_wit_1_split_goal_3 : max_sub_array_entail_wit_1_split_goal_3.
Proof.
  unfold max_sub_array_entail_wit_1_split_goal_3; intros.
  pose proof (input_Znth_bounds l 0 PreH5 PreH6 ltac:(lia)); lia.
Qed.

Lemma proof_of_max_sub_array_entail_wit_1_split_goal_4 : max_sub_array_entail_wit_1_split_goal_4.
Proof.
  unfold max_sub_array_entail_wit_1_split_goal_4; intros.
  pose proof (input_Znth_bounds l 0 PreH5 PreH6 ltac:(lia)); lia.
Qed.

Lemma proof_of_max_sub_array_entail_wit_1_split_goal_5 : max_sub_array_entail_wit_1_split_goal_5.
Proof.
  unfold max_sub_array_entail_wit_1_split_goal_5; intros.
  pose proof (input_Znth_bounds l 0 PreH5 PreH6 ltac:(lia)); lia.
Qed.

Lemma proof_of_max_sub_array_entail_wit_1_split_goal_6 : max_sub_array_entail_wit_1_split_goal_6.
Proof.
  unfold max_sub_array_entail_wit_1_split_goal_6; intros.
  pose proof (input_Znth_bounds l 0 PreH5 PreH6 ltac:(lia)); lia.
Qed.

Lemma proof_of_max_sub_array_entail_wit_1 : max_sub_array_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_max_sub_array_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_max_sub_array_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_max_sub_array_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_max_sub_array_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_max_sub_array_entail_wit_1_split_goal_5.
  - Goal_apply proof_of_max_sub_array_entail_wit_1_split_goal_6.

Qed. 

Lemma proof_of_max_sub_array_entail_wit_2_split_goal_1 : max_sub_array_entail_wit_2_split_goal_1.
Proof.
  unfold max_sub_array_entail_wit_2_split_goal_1; intros.
  assert (Hsuffix : MaxSuffixSumPrefix l (i + 1) retval).
  { subst retval. apply MaxSuffixSumPrefix_step; try lia; assumption. }
  subst retval_2; apply MaxSubarraySumPrefix_step; assumption.
Qed.

Lemma proof_of_max_sub_array_entail_wit_2_split_goal_2 : max_sub_array_entail_wit_2_split_goal_2.
Proof.
  unfold max_sub_array_entail_wit_2_split_goal_2; intros.
  assert (Hsuffix : MaxSuffixSumPrefix l (i + 1) retval).
  { subst retval. apply MaxSuffixSumPrefix_step; try lia; assumption. }
  exact Hsuffix.
Qed.

Lemma proof_of_max_sub_array_entail_wit_2_split_goal_3 : max_sub_array_entail_wit_2_split_goal_3.
Proof.
  unfold max_sub_array_entail_wit_2_split_goal_3; intros.
  assert (Hsuffix : MaxSuffixSumPrefix l (i + 1) retval).
  { subst retval. apply MaxSuffixSumPrefix_step; try lia; assumption. }
  assert (Hbound : retval <= 1000000000).
  { eapply (MaxSuffixSumPrefix_upper_bound l (i + 1) retval n_pre); try lia; try exact Hsuffix.
    intros k Hk. pose proof (input_Znth_bounds l k PreH15 PreH16 ltac:(lia)); lia. }
  subst retval_2; unfold max_Z; apply Z.max_lub; lia.
Qed.

Lemma proof_of_max_sub_array_entail_wit_2_split_goal_4 : max_sub_array_entail_wit_2_split_goal_4.
Proof.
  unfold max_sub_array_entail_wit_2_split_goal_4; intros.
  assert (Hsuffix : MaxSuffixSumPrefix l (i + 1) retval).
  { subst retval. apply MaxSuffixSumPrefix_step; try lia; assumption. }
  subst retval_2; unfold max_Z; pose proof (Z.le_max_l res retval); lia.
Qed.

Lemma proof_of_max_sub_array_entail_wit_2_split_goal_5 : max_sub_array_entail_wit_2_split_goal_5.
Proof.
  unfold max_sub_array_entail_wit_2_split_goal_5; intros.
  assert (Hsuffix : MaxSuffixSumPrefix l (i + 1) retval).
  { subst retval. apply MaxSuffixSumPrefix_step; try lia; assumption. }
  assert (Hbound : retval <= 1000000000).
  { eapply (MaxSuffixSumPrefix_upper_bound l (i + 1) retval n_pre); try lia; try exact Hsuffix.
    intros k Hk. pose proof (input_Znth_bounds l k PreH15 PreH16 ltac:(lia)); lia. }
  exact Hbound.
Qed.

Lemma proof_of_max_sub_array_entail_wit_2_split_goal_6 : max_sub_array_entail_wit_2_split_goal_6.
Proof.
  unfold max_sub_array_entail_wit_2_split_goal_6; intros.
  assert (Hsuffix : MaxSuffixSumPrefix l (i + 1) retval).
  { subst retval. apply MaxSuffixSumPrefix_step; try lia; assumption. }
  pose proof (input_Znth_bounds l i PreH15 PreH16 ltac:(lia)).
  subst retval; unfold max_Z; pose proof (Z.le_max_l (Znth i l 0) (cur + Znth i l 0)); lia.
Qed.

Lemma proof_of_max_sub_array_entail_wit_2 : max_sub_array_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_max_sub_array_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_max_sub_array_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_max_sub_array_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_max_sub_array_entail_wit_2_split_goal_4.
  - Goal_apply proof_of_max_sub_array_entail_wit_2_split_goal_5.
  - Goal_apply proof_of_max_sub_array_entail_wit_2_split_goal_6.

Qed. 

Lemma proof_of_max_sub_array_return_wit_1_split_goal_1 : max_sub_array_return_wit_1_split_goal_1.
Proof.
  unfold max_sub_array_return_wit_1_split_goal_1; intros. assert (i = n_pre) by lia. subst i; assumption.
Qed.

Lemma proof_of_max_sub_array_return_wit_1 : max_sub_array_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_max_sub_array_return_wit_1_split_goal_1.

Qed. 

