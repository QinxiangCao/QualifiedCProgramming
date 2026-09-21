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
From SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum Require Import split_array_largest_sum_goal.
Require Import AUXLib.MonotonicList.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum.split_array_largest_sum_lib.
Local Open Scope sac.

Lemma proof_of_check_entail_wit_1_split_goal_1 : check_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  change (SplitProgress (@nil Z) cap_pre 1 0). apply split_progress_empty.
Qed.

Lemma proof_of_check_entail_wit_1 : check_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_check_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_check_entail_wit_2_1_split_goal_1 : check_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : Forall (Z.le 0) l |- _ =>
    pose proof (proj1 (Forall_Znth (Z.le 0) 0 l) H i ltac:(lia)) as Hnonnegative end.
  rewrite (sublist_snoc_Znth 0 l i) by lia.
  eapply split_progress_new_segment; try eassumption; try lia.
  apply split_prefix_nonnegative; assumption || lia.
Qed.

Lemma proof_of_check_entail_wit_2_1 : check_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_check_entail_wit_2_1_split_goal_1.
Qed.

Lemma proof_of_check_entail_wit_2_2_split_goal_1 : check_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : Forall (Z.le 0) l |- _ =>
    pose proof (proj1 (Forall_Znth (Z.le 0) 0 l) H i ltac:(lia)) as Hnonnegative end.
  rewrite (sublist_snoc_Znth 0 l i) by lia.
  eapply split_progress_extend; try eassumption; try lia.
  apply split_prefix_nonnegative; assumption || lia.
Qed.

Lemma proof_of_check_entail_wit_2_2_split_goal_2 : check_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (proj1 (Forall_Znth _ 0 l) PreH11 i ltac:(lia)). lia.
Qed.

Lemma proof_of_check_entail_wit_2_2 : check_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_check_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_check_entail_wit_2_2_split_goal_2.
Qed.

Lemma proof_of_check_return_wit_1_split_goal_1 : check_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : SplitProgress (sublist 0 i l) _ _ _ |- _ =>
    replace i with (Zlength l) in H by lia;
    rewrite sublist_self in H by reflexivity end.
  eapply split_progress_infeasible; eassumption || lia.
Qed.

Lemma proof_of_check_return_wit_1 : check_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_check_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_check_return_wit_2_split_goal_1 : check_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : SplitProgress (sublist 0 i l) _ _ _ |- _ =>
    replace i with (Zlength l) in H by lia;
    rewrite sublist_self in H by reflexivity end.
  eapply split_progress_feasible; eassumption || lia.
Qed.

Lemma proof_of_check_return_wit_2 : check_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_check_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_check_return_wit_3_split_goal_1 : check_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (proj2 (SplitInfeasible_legacy l m_pre cap_pre ltac:(lia) ltac:(lia) PreH10)).
  unfold CannotSplit. intros cnt' cur' Hstate.
  pose proof (PrefixSplitState_items_bound _ _ _ _ _ Hstate i ltac:(lia)). lia.
Qed.

Lemma proof_of_check_return_wit_3 : check_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_check_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_splitArrayLargestSum_safety_wit_3_split_goal_1 : splitArrayLargestSum_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply dump_spatial_left.
  assert (0 <= (right-left) ÷ 2) by (apply Z.quot_pos; lia).
  assert ((right-left) ÷ 2 < right-left) by (apply Z.quot_lt; lia).
  lia.
Qed.

Lemma proof_of_splitArrayLargestSum_safety_wit_3_split_goal_2 : splitArrayLargestSum_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply dump_spatial_left.
  assert (0 <= (right-left) ÷ 2) by (apply Z.quot_pos; lia).
  assert ((right-left) ÷ 2 < right-left) by (apply Z.quot_lt; lia).
  lia.
Qed.

Lemma proof_of_splitArrayLargestSum_safety_wit_3 : splitArrayLargestSum_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_splitArrayLargestSum_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_splitArrayLargestSum_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_splitArrayLargestSum_safety_wit_7_split_goal_1 : splitArrayLargestSum_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply dump_spatial_left.
  assert (0 <= (right-left) ÷ 2) by (apply Z.quot_pos; lia).
  assert ((right-left) ÷ 2 < right-left) by (apply Z.quot_lt; lia).
  lia.
Qed.

Lemma proof_of_splitArrayLargestSum_safety_wit_7_split_goal_2 : splitArrayLargestSum_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply dump_spatial_left.
  assert (0 <= (right-left) ÷ 2) by (apply Z.quot_pos; lia).
  assert ((right-left) ÷ 2 < right-left) by (apply Z.quot_lt; lia).
  lia.
Qed.

Lemma proof_of_splitArrayLargestSum_safety_wit_7 : splitArrayLargestSum_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_splitArrayLargestSum_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_splitArrayLargestSum_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_splitArrayLargestSum_entail_wit_1 : splitArrayLargestSum_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists ans.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_splitArrayLargestSum_entail_wit_2_1 : splitArrayLargestSum_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hq0 : 0 <= (right-left) ÷ 2) by (apply Z.quot_pos; lia).
  assert (Hqlt : (right-left) ÷ 2 < right-left) by (apply Z.quot_lt; lia).
  assert (Hbound : res_2 <= left + (right-left) ÷ 2).
  { match goal with H : _ -> SplitFeasible _ _ _ |- _ =>
      specialize (H ltac:(lia)); destruct H as [v [Hp Hv]] end.
    match goal with H : MinimizedMaxSegmentSum _ _ _ |- _ =>
      pose proof (minimized_lower_bound _ _ _ _ H Hp) end. lia. }
  Exists res_2. split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_splitArrayLargestSum_entail_wit_2_2 : splitArrayLargestSum_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hq0 : 0 <= (right-left) ÷ 2) by (apply Z.quot_pos; lia).
  assert (Hqlt : (right-left) ÷ 2 < right-left) by (apply Z.quot_lt; lia).
  assert (Hbound : left + (right-left) ÷ 2 < res_2).
  { destruct (Z_lt_ge_dec (left + (right-left) ÷ 2) res_2); [assumption |].
    exfalso. match goal with H : _ -> SplitInfeasible _ _ _ |- _ =>
      specialize (H ltac:(lia)); apply H end.
    exists res_2. split; [|lia].
    eapply minimized_partition_witness; eassumption. }
  Exists res_2. split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_splitArrayLargestSum_return_wit_1_split_goal_1 : splitArrayLargestSum_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace left with res by lia. assumption.
Qed.

Lemma proof_of_splitArrayLargestSum_return_wit_1 : splitArrayLargestSum_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_splitArrayLargestSum_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_splitArrayLargestSum_partial_solve_wit_1_pure_split_goal_1 : splitArrayLargestSum_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply dump_spatial_left.
  assert (0 <= (right-left) ÷ 2) by (apply Z.quot_pos; lia).
  assert ((right-left) ÷ 2 < right-left) by (apply Z.quot_lt; lia).
  lia.
Qed.

Lemma proof_of_splitArrayLargestSum_partial_solve_wit_1_pure_split_goal_2 : splitArrayLargestSum_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply dump_spatial_left.
  assert (0 <= (right-left) ÷ 2) by (apply Z.quot_pos; lia).
  assert ((right-left) ÷ 2 < right-left) by (apply Z.quot_lt; lia).
  lia.
Qed.

Lemma proof_of_splitArrayLargestSum_partial_solve_wit_1_pure : splitArrayLargestSum_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_splitArrayLargestSum_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_splitArrayLargestSum_partial_solve_wit_1_pure_split_goal_2.
Qed.

