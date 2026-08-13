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
From SimpleC.EE.QCP_demos_tutorial Require Import pos_int_pair_goal.
From SimpleC.EE.QCP_demos_tutorial Require Import pos_int_pair_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_tutorial.pos_int_pair_lib.
Local Open Scope sac.

Lemma proof_of_slow_sub_safety_wit_2_split_goal_1 : slow_sub_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_pos_int_pair.
  Intros_p Hx0_nonneg.
  Intros_p Hy0_nonneg.
  prop_apply (store_int_range (&(p_pre # "int_pair" ->ₛ "a")) x0).
  entailer!.
  change Int.max_signed with 2147483647 in *.
  lia.
Qed.

Lemma proof_of_slow_sub_safety_wit_2_split_goal_2 : slow_sub_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_slow_sub_safety_wit_2 : slow_sub_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_slow_sub_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_slow_sub_safety_wit_2_split_goal_2.
Qed.

Lemma proof_of_slow_sub_safety_wit_3_split_goal_1 : slow_sub_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_pos_int_pair.
  Intros_p Hx0_nonneg.
  Intros_p Hy0_nonneg.
  prop_apply (store_int_range (&(p_pre # "int_pair" ->ₛ "b")) y0).
  entailer!.
  change Int.max_signed with 2147483647 in *.
  lia.
Qed.

Lemma proof_of_slow_sub_safety_wit_3_split_goal_2 : slow_sub_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_slow_sub_safety_wit_3 : slow_sub_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_slow_sub_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_slow_sub_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_slow_sub_return_wit_1_split_goal_spatial : slow_sub_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_pos_int_pair.
  entailer!.
  subst y0.
  replace (x - y) with x0 by lia.
  cancel.
Qed.

Lemma proof_of_slow_sub_return_wit_1 : slow_sub_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_slow_sub_return_wit_1_split_goal_spatial.
Qed.
