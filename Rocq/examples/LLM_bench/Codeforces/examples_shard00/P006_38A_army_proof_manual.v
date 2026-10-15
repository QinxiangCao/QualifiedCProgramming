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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P006_38A_army_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P006_38A_army_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P006_38A_army_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_3_split_goal_1 : solver_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH4 (i - 1) ltac:(lia)).
  rewrite Znth_cons by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_3_split_goal_2 : solver_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH4 (i - 1) ltac:(lia)).
  rewrite Znth_cons by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: unfold Spec;
       rewrite Zsublist_nil by lia;
       simpl;
       reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply PreH3;
       assumption.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply Spec_succ__loop_step; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH4 (i - 1) ltac:(lia)).
  rewrite Znth_cons by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_3 : solver_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH4 (i - 1) ltac:(lia)).
  rewrite Znth_cons by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = b_pre) by lia.
  subst i.
  exact PreH11.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
