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
From SimpleC.EE.LLM_bench.Data_structures.stack Require Import stack_goal.
From SimpleC.EE.LLM_bench.Data_structures.stack Require Import stack_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Data_structures.stack.stack_lib.
Local Open Scope sac.

Lemma proof_of_push_entail_wit_1 : push_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_stack.
  Intros concrete.
  Exists concrete.
  unfold StackConcreteView.
  split_pure_spatial.
  - cancel (IntArray.full stack_pre n_pre concrete).
    cancel (IntArray.undef_seg stack_pre n_pre (n_pre + 1)).
  - split_pures.
    + dump_pre_spatial.
      unfold stack_representation in H.
      lia.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      exact H.
Qed.

Lemma proof_of_push_entail_wit_2_split_goal_spatial : push_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_stack.
  Exists (concrete ++ (x_pre :: nil)).
  split_pure_spatial.
  - cancel (IntArray.full stack_pre (n_pre + 1)
              (concrete ++ (x_pre :: nil))).
  - dump_pre_spatial.
    unfold StackConcreteView in *.
    eapply stack_representation_push__push_state; eauto.
Qed.

Lemma proof_of_push_entail_wit_2 : push_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_push_entail_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_pop_entail_wit_1 : pop_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold store_stack.
  Intros concrete.
  match goal with
  | Hrepresentation : stack_representation _ concrete n_pre |- _ =>
      pose proof Hrepresentation as Hrepresentation_parts;
      destruct Hrepresentation_parts as [_ [Hcapacity _]]
  end.
  Exists concrete.
  unfold StackConcreteView.
  split_pure_spatial.
  - cancel (IntArray.full stack_pre n_pre concrete).
  - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_pop_entail_wit_2_split_goal_1 : pop_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold StackConcreteView in PreH3.
  pose proof
    (stack_representation_pop__pop_state
      top rest concrete n_pre PreH1 PreH3)
    as [_ [_ [_ Htop]]].
  dump_pre_spatial.
  exact Htop.
Qed.

Lemma proof_of_pop_entail_wit_2_split_goal_spatial : pop_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold StackConcreteView in PreH3.
  pose proof
    (stack_representation_pop__pop_state
      top rest concrete n_pre PreH1 PreH3)
    as [Hconcrete [Hprefix_length [Hrest_representation _]]].
  assert (Hprefix : sublist 0 (n_pre - 1) concrete = rev rest).
  {
    rewrite Hconcrete.
    rewrite <- Hprefix_length.
    apply sublist_app_exact1.
  }
  unfold store_stack.
  Exists (rev rest).
  sep_apply_l_atomic
    (IntArray.full_split_to_seg
      stack_pre (n_pre - 1) n_pre concrete ltac:(lia)).
  rewrite Hprefix.
  sep_apply_l_atomic
    (IntArray.seg_to_full
      stack_pre 0 (n_pre - 1) (rev rest)).
  sep_apply_l_atomic
    (IntArray.seg_to_undef_seg
      stack_pre (n_pre - 1) n_pre
      (sublist (n_pre - 1) n_pre concrete)).
  replace (stack_pre + 0 * sizeof(INT)) with stack_pre by lia.
  replace (n_pre - 1 - 0) with (n_pre - 1) by lia.
  split_pure_spatial.
  - repeat cancel.
  - dump_pre_spatial.
    exact Hrest_representation.
Qed.

Lemma proof_of_pop_entail_wit_2 : pop_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pop_entail_wit_2_split_goal_spatial.
  - Goal_apply proof_of_pop_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_build_entail_wit_1 : build_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct (Z.eq_dec n_pre 0) as [Hzero | Hpositive].
  - subst n_pre.
    Left.
    split_pure_spatial;
      [ repeat cancel
      | split_pures; dump_pre_spatial; try lia; try int_auto;
        try assumption; try reflexivity ].
  - Right.
    assert (Hone : 1 <= n_pre) by lia.
    pose proof
      (stack_representation_prefix__build_loop
        input 1 ltac:(lia) ltac:(lia))
      as Hrepresentation.
    sep_apply
      (IntArray.full_split_to_seg
        stack_pre 1 n_pre input);
      try lia.
    unfold store_stack.
    Exists (sll_from_array (sublist 0 1 input)).
    Exists (sublist 0 1 input).
    sep_apply
      (IntArray.seg_to_full
        stack_pre 0 1 (sublist 0 1 input)).
    split_pure_spatial;
      [ repeat cancel
      | split_pures; dump_pre_spatial; try lia; try int_auto;
        try assumption; try reflexivity ].
    replace (stack_pre + 0 * sizeof(INT)) with stack_pre by lia.
    replace (1 - 0) with 1 by lia.
    cancel.
Qed.

Lemma proof_of_build_entail_wit_2 : build_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists prefix_2.
  sep_apply
    (IntArray.seg_split_to_seg
      stack_pre i (i + 1) n_pre (sublist i n_pre input));
    try lia.
  sep_apply
    (IntArray.seg_to_undef_seg
      stack_pre i (i + 1)
      (sublist 0 (i + 1 - i) (sublist i n_pre input))).
  replace
    (sublist (i + 1 - i) (n_pre - i) (sublist i n_pre input))
    with (sublist (i + 1) n_pre input).
  2: {
    rewrite Zsublist_Zsublist by lia.
    f_equal; lia.
  }
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try lia; try int_auto;
      try assumption; try reflexivity.
  all: try (rewrite Znth_sublist by lia; f_equal; lia).
Qed.

Lemma proof_of_build_entail_wit_3_split_goal_1 : build_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply build_stack_prefix_succ__build_loop; eauto; lia.
Qed.

Lemma proof_of_build_entail_wit_3 : build_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_build_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_build_entail_wit_5_1_split_goal_1 : build_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold stack_capacity.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_build_entail_wit_5_1_split_goal_spatial : build_entail_wit_5_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n_pre.
  apply Zlength_nil_inv in PreH4.
  subst input.
  unfold store_stack.
  Exists (@nil Z).
  split_pure_spatial.
  - cancel (IntArray.full stack_pre 0 (@nil Z)).
  - dump_pre_spatial.
    unfold stack_representation, sll_from_array, stack_capacity.
    simpl.
    repeat split; lia.
Qed.

Lemma proof_of_build_entail_wit_5_1 : build_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_5_1_split_goal_spatial.
  - Goal_apply proof_of_build_entail_wit_5_1_split_goal_1.
Qed.

Lemma proof_of_build_entail_wit_5_2_split_goal_spatial : build_entail_wit_5_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof
    (build_stack_prefix_complete__build_completion
      prefix input i n_pre PreH1 PreH5 PreH6 PreH7)
    as [Hi Hprefix].
  subst i.
  subst prefix.
  rewrite Zsublist_nil by lia.
  rewrite IntArray.seg_empty.
  Intros_p Hempty.
  cancel (store_stack stack_pre (sll_from_array input) n_pre).
Qed.

Lemma proof_of_build_entail_wit_5_2 : build_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_build_entail_wit_5_2_split_goal_spatial.
Qed.
