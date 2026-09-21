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
From SimpleC.EE.LLM_bench.Algorithms.modular_inverse Require Import modular_inverse_goal.
From SimpleC.EE.LLM_bench.Algorithms.modular_inverse Require Import modular_inverse_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.modular_inverse.modular_inverse_lib.
Local Open Scope sac.

Lemma proof_of_modular_inverse_return_wit_1_split_goal_1 : modular_inverse_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ModularInverse.
  exists (a_pre * Z.quot x_callee_v modulus_pre + y_callee_v - a_pre).
  pose proof (Z.quot_rem x_callee_v modulus_pre ltac:(lia)) as Hquot_rem.
  nia.
Qed.

Lemma proof_of_modular_inverse_return_wit_1_split_goal_2 : modular_inverse_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_abs x_callee_v modulus_pre ltac:(lia)) as Hrem.
  lia.
Qed.

Lemma proof_of_modular_inverse_return_wit_1 : modular_inverse_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modular_inverse_return_wit_1_split_goal_1.
  - Goal_apply proof_of_modular_inverse_return_wit_1_split_goal_2.
Qed. 

Lemma proof_of_modular_inverse_return_wit_2_split_goal_1 : modular_inverse_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ModularInverse.
  exists (a_pre * Z.quot x_callee_v modulus_pre + y_callee_v).
  pose proof (Z.quot_rem x_callee_v modulus_pre ltac:(lia)) as Hquot_rem.
  nia.
Qed.

Lemma proof_of_modular_inverse_return_wit_2_split_goal_2 : modular_inverse_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.rem_bound_abs x_callee_v modulus_pre ltac:(lia)) as Hrem.
  lia.
Qed.

Lemma proof_of_modular_inverse_return_wit_2 : modular_inverse_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_modular_inverse_return_wit_2_split_goal_1.
  - Goal_apply proof_of_modular_inverse_return_wit_2_split_goal_2.
Qed. 

