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
From SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes Require Import sieve_of_eratosthenes_goal.
From SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes Require Import sieve_of_eratosthenes_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes.sieve_of_eratosthenes_lib.
Local Open Scope sac.

Lemma proof_of_solve_entail_wit_1_split_goal_1 : solve_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply SieveInitPrefix_start__sieve_invariants; eauto; lia.
Qed.

Lemma proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solve_entail_wit_1_split_goal_1.
Qed. 

Lemma proof_of_solve_entail_wit_2_split_goal_1 : solve_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply SieveInitPrefix_step__sieve_invariants; eauto; lia.
Qed.

Lemma proof_of_solve_entail_wit_2 : solve_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solve_entail_wit_2_split_goal_1.
Qed. 

Lemma proof_of_solve_entail_wit_3_split_goal_1 : solve_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply SieveInitPrefix_finish__sieve_invariants; eauto; lia.
Qed.

Lemma proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solve_entail_wit_3_split_goal_1.
Qed. 

Lemma proof_of_solve_entail_wit_4_split_goal_1 : solve_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply SieveStage_mark_start__sieve_invariants; eauto; lia.
Qed.

Lemma proof_of_solve_entail_wit_4 : solve_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solve_entail_wit_4_split_goal_1.
Qed. 

Lemma proof_of_solve_entail_wit_5_split_goal_1 : solve_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply SieveMarkState_step__sieve_invariants; eauto; lia.
Qed.

Lemma proof_of_solve_entail_wit_5 : solve_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solve_entail_wit_5_split_goal_1.
Qed. 

Lemma proof_of_solve_entail_wit_6_1_split_goal_1 : solve_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply SieveMarkState_finish__sieve_invariants; eauto; lia.
Qed.

Lemma proof_of_solve_entail_wit_6_1 : solve_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solve_entail_wit_6_1_split_goal_1.
Qed. 

Lemma proof_of_solve_entail_wit_6_2_split_goal_1 : solve_entail_wit_6_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply SieveStage_skip_composite__sieve_invariants; eauto; lia.
Qed.

Lemma proof_of_solve_entail_wit_6_2 : solve_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solve_entail_wit_6_2_split_goal_1.
Qed. 

Lemma proof_of_solve_return_wit_1_split_goal_1 : solve_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply SieveStage_implies_PrimeIndicatorList; eauto; lia.
Qed.

Lemma proof_of_solve_return_wit_1 : solve_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solve_return_wit_1_split_goal_1.
Qed. 

