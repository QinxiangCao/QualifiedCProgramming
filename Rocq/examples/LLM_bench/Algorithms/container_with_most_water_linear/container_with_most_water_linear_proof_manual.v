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
From SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear Require Import container_with_most_water_linear_goal.
Require Import AUXLib.MonotonicList.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear.container_with_most_water_linear_lib.
Local Open Scope sac.


Ltac linear_arith :=
  repeat match goal with
  | H : Forall ?P ?l |- context [Znth ?i ?l 0] =>
    let B := fresh "element_bound" in
    pose proof (proj1 (Forall_Znth P 0 l) H i ltac:(lia)) as B;
    clear H
  end;
  solve [nia | int_auto].

Lemma proof_of_maxAreaLinear_safety_wit_10_split_goal_1 : maxAreaLinear_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(linear_arith).
Qed.

Lemma proof_of_maxAreaLinear_safety_wit_10_split_goal_2 : maxAreaLinear_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(linear_arith).
Qed.

Lemma proof_of_maxAreaLinear_safety_wit_10 : maxAreaLinear_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaLinear_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_maxAreaLinear_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_maxAreaLinear_safety_wit_11_split_goal_1 : maxAreaLinear_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(linear_arith).
Qed.

Lemma proof_of_maxAreaLinear_safety_wit_11_split_goal_2 : maxAreaLinear_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(linear_arith).
Qed.

Lemma proof_of_maxAreaLinear_safety_wit_11 : maxAreaLinear_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaLinear_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_maxAreaLinear_safety_wit_11_split_goal_2.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_1_split_goal_1 : maxAreaLinear_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat match goal with H : Forall ?P ?l |- _ => rewrite (Forall_Znth P 0 l) in H end.
  unfold LinearContainerTwoPointerInvariant, LinearContainerBest.
  split.
  - left. reflexivity.
  - intros i j Hpair.
    right.
    exists i, j.
    split.
    + unfold LinearContainerRemaining.
      split.
      * exact Hpair.
      * split.
        -- unfold LinearContainerPair in Hpair. lia.
        -- unfold LinearContainerPair in Hpair. rewrite PreH6 in Hpair. lia.
    + lia.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_1 : maxAreaLinear_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maxAreaLinear_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_1_split_goal_1 : maxAreaLinear_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat match goal with H : Forall ?P ?l |- _ => rewrite (Forall_Znth P 0 l) in H end.
  replace ((right - left) * Znth left l 0)
    with (LinearContainerArea l left right).
  - apply (linear_container_invariant_update_best__best_update
             l left right maximumArea).
    + exact PreH12.
    + unfold LinearContainerPair.
      lia.
    + unfold LinearContainerArea, LinearContainerHeight.
      rewrite Z.min_l by lia.
      lia.
  - unfold LinearContainerArea, LinearContainerHeight.
    rewrite Z.min_l by lia.
    reflexivity.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_1_split_goal_2 : maxAreaLinear_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(linear_arith).
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_1_split_goal_3 : maxAreaLinear_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(linear_arith).
  unfold LinearContainerArea, LinearContainerHeight.
  first [rewrite Z.min_l by lia | rewrite Z.min_r by lia]; reflexivity.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_1_split_goal_4 : maxAreaLinear_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(linear_arith).
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_1_split_goal_5 : maxAreaLinear_entail_wit_2_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(linear_arith).
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_1_split_goal_6 : maxAreaLinear_entail_wit_2_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(linear_arith).
  unfold LinearContainerArea, LinearContainerHeight.
  first [rewrite Z.min_l by lia | rewrite Z.min_r by lia]; reflexivity.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_1 : maxAreaLinear_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_1_split_goal_4.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_1_split_goal_5.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_1_split_goal_6.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_2_split_goal_1 : maxAreaLinear_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat match goal with H : Forall ?P ?l |- _ => rewrite (Forall_Znth P 0 l) in H end.
  replace ((right - left) * Znth right l 0)
    with (LinearContainerArea l left right).
  - apply (linear_container_invariant_update_best__best_update
             l left right maximumArea).
    + exact PreH12.
    + unfold LinearContainerPair.
      lia.
    + unfold LinearContainerArea, LinearContainerHeight.
      rewrite Z.min_r by lia.
      lia.
  - unfold LinearContainerArea, LinearContainerHeight.
    rewrite Z.min_r by lia.
    reflexivity.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_2_split_goal_2 : maxAreaLinear_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(linear_arith).
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_2_split_goal_3 : maxAreaLinear_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(linear_arith).
  unfold LinearContainerArea, LinearContainerHeight.
  first [rewrite Z.min_l by lia | rewrite Z.min_r by lia]; reflexivity.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_2_split_goal_4 : maxAreaLinear_entail_wit_2_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(linear_arith).
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_2_split_goal_5 : maxAreaLinear_entail_wit_2_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(linear_arith).
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_2_split_goal_6 : maxAreaLinear_entail_wit_2_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(linear_arith).
  unfold LinearContainerArea, LinearContainerHeight.
  first [rewrite Z.min_l by lia | rewrite Z.min_r by lia]; reflexivity.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_2 : maxAreaLinear_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_2_split_goal_3.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_2_split_goal_4.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_2_split_goal_5.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_2_split_goal_6.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_3_split_goal_1 : maxAreaLinear_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(linear_arith).
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_3_split_goal_2 : maxAreaLinear_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(linear_arith).
  unfold LinearContainerArea, LinearContainerHeight.
  first [rewrite Z.min_l by lia | rewrite Z.min_r by lia]; reflexivity.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_3_split_goal_3 : maxAreaLinear_entail_wit_2_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(linear_arith).
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_3_split_goal_4 : maxAreaLinear_entail_wit_2_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(linear_arith).
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_3_split_goal_5 : maxAreaLinear_entail_wit_2_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(linear_arith).
  unfold LinearContainerArea, LinearContainerHeight.
  first [rewrite Z.min_l by lia | rewrite Z.min_r by lia]; reflexivity.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_3 : maxAreaLinear_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_3_split_goal_2.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_3_split_goal_3.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_3_split_goal_4.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_3_split_goal_5.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_4_split_goal_1 : maxAreaLinear_entail_wit_2_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(linear_arith).
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_4_split_goal_2 : maxAreaLinear_entail_wit_2_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(linear_arith).
  unfold LinearContainerArea, LinearContainerHeight.
  first [rewrite Z.min_l by lia | rewrite Z.min_r by lia]; reflexivity.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_4_split_goal_3 : maxAreaLinear_entail_wit_2_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(linear_arith).
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_4_split_goal_4 : maxAreaLinear_entail_wit_2_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(linear_arith).
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_4_split_goal_5 : maxAreaLinear_entail_wit_2_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(linear_arith).
  unfold LinearContainerArea, LinearContainerHeight.
  first [rewrite Z.min_l by lia | rewrite Z.min_r by lia]; reflexivity.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_2_4 : maxAreaLinear_entail_wit_2_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_4_split_goal_1.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_4_split_goal_2.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_4_split_goal_3.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_4_split_goal_4.
  - Goal_apply proof_of_maxAreaLinear_entail_wit_2_4_split_goal_5.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_3_1_split_goal_1 : maxAreaLinear_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat match goal with H : Forall ?P ?l |- _ => rewrite (Forall_Znth P 0 l) in H end.
  eapply linear_container_invariant_advance_left__pointer_transitions.
  - intros k Hk.
    apply PreH20.
    lia.
  - unfold LinearContainerPair.
    lia.
  - exact PreH1.
  - lia.
  - exact PreH19.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_3_1 : maxAreaLinear_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maxAreaLinear_entail_wit_3_1_split_goal_1.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_3_2_split_goal_1 : maxAreaLinear_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat match goal with H : Forall ?P ?l |- _ => rewrite (Forall_Znth P 0 l) in H end.
  eapply linear_container_invariant_retreat_right__pointer_transitions.
  - intros k Hk.
    apply PreH20.
    lia.
  - unfold LinearContainerPair.
    lia.
  - exact PreH1.
  - lia.
  - exact PreH19.
Qed.

Lemma proof_of_maxAreaLinear_entail_wit_3_2 : maxAreaLinear_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maxAreaLinear_entail_wit_3_2_split_goal_1.
Qed.

Lemma proof_of_maxAreaLinear_return_wit_1_split_goal_1 : maxAreaLinear_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat match goal with H : Forall ?P ?l |- _ => rewrite (Forall_Znth P 0 l) in H end.
  eapply (linear_container_closed_invariant_maximum__final_result
            l left right maximumArea).
  - lia.
  - lia.
  - intros k Hrange.
    apply PreH11.
    lia.
  - exact PreH10.
Qed.

Lemma proof_of_maxAreaLinear_return_wit_1 : maxAreaLinear_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maxAreaLinear_return_wit_1_split_goal_1.
Qed.
