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
Local Open Scope sac.

Lemma proof_of_modular_inverse_return_wit_1 : modular_inverse_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (a_pre * Z.quot x_callee_v modulus_pre + y_callee_v - a_pre).
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    + dump_pre_spatial.
      pose proof (Z.rem_bound_abs x_callee_v modulus_pre ltac:(lia)) as Hrem.
      lia.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      pose proof (Z.quot_rem x_callee_v modulus_pre ltac:(lia)) as Hquot_rem.
      nia.
Qed.

Lemma proof_of_modular_inverse_return_wit_2 : modular_inverse_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (a_pre * Z.quot x_callee_v modulus_pre + y_callee_v).
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      pose proof (Z.rem_bound_abs x_callee_v modulus_pre ltac:(lia)) as Hrem.
      lia.
    + dump_pre_spatial.
      pose proof (Z.quot_rem x_callee_v modulus_pre ltac:(lia)) as Hquot_rem.
      nia.
Qed.
