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
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import matrix_inverse_gmp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import matrix_inverse_gmp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope sac.

Lemma proof_of_matrix_inverse_gmp_return_wit_1 : matrix_inverse_gmp_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct (PreH4 PreH1) as [Bres [Hrep Hsuccess]].
  Exists Bres lx2_2 laug2_2 linv2_2.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
    cancel (mpz_array inv_pre (n_pre * n_pre) linv2_2).
    cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) laug2_2).
    cancel (mpz_array x_pre n_pre lx2_2).
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity.
Qed.
