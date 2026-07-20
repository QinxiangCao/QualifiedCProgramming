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

Lemma proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Proof.
  aggressive_pre_process.
  eapply SieveInitPrefix_start__sieve_invariants; eauto.
Qed.

Lemma proof_of_solve_entail_wit_2 : solve_entail_wit_2.
Proof.
  aggressive_pre_process.
  eapply SieveInitPrefix_step__sieve_invariants; eauto; lia.
Qed.

Lemma proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Proof.
  aggressive_pre_process.
  eapply SieveInitPrefix_finish__sieve_invariants; eauto; lia.
Qed.

Lemma proof_of_solve_entail_wit_5 : solve_entail_wit_5.
Proof.
  aggressive_pre_process.
  eapply SieveStage_mark_start__sieve_invariants; eauto; lia.
Qed.

Lemma proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Proof.
  aggressive_pre_process.
  eapply SieveMarkState_step__sieve_invariants; eauto; lia.
Qed.

Lemma proof_of_solve_entail_wit_7 : solve_entail_wit_7.
Proof.
  aggressive_pre_process.
  eapply SieveMarkState_finish__sieve_invariants; eauto; lia.
Qed.

Lemma proof_of_solve_entail_wit_8_2_split_goal_1 : solve_entail_wit_8_2_split_goal_1.
Proof.
  pre_process.
  eapply SieveStage_skip_composite__sieve_invariants; eauto; lia.
Qed.

Lemma proof_of_solve_entail_wit_8_2 : solve_entail_wit_8_2.
Proof.
  pre_process.
  Exists current_2.
  split_pure_spatial.
  - cancel (IntArray.seg f_pre 1 (n_pre + 1) current_2).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    eapply SieveStage_skip_composite__sieve_invariants; eauto; lia.
Qed.

Lemma proof_of_solve_entail_wit_10 : solve_entail_wit_10.
Proof.
  aggressive_pre_process.
  eapply SieveStage_implies_PrimeIndicatorList; eauto; lia.
Qed.
