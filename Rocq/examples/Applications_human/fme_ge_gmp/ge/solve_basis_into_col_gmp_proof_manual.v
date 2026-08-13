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
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import solve_basis_into_col_gmp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import solve_basis_into_col_gmp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope sac.

(* Lemma proof_of_solve_basis_into_col_gmp_return_wit_1_split_goal_1 :
  solve_basis_into_col_gmp_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  match goal with
  | H : gauss_success _ _ _ X |- _ =>
      destruct H as [Hvec Hsol]
  end.
  eapply inverse_cols_prefix_spec_extend; eauto; lia.
Qed. *)

Lemma proof_of_solve_basis_into_col_gmp_entail_wit_1 :
  solve_basis_into_col_gmp_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists lx2_2 X_2 l2 M2_2.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
    cancel (mpz_array inv_pre (n_pre * n_pre) linv_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) l2).
    cancel (mpz_array x_pre n_pre lx2_2).
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solve_basis_into_col_gmp_return_wit_1 :
  solve_basis_into_col_gmp_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  assert (Hinv_next :
    inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec
      (matrix_set_col B_low_level_spec col_pre X) (col_pre + 1)).
  { destruct PreH29 as [Hvec Hsol].
    eapply inverse_cols_prefix_spec_extend; eauto; lia. }
  Exists (matrix_set_col B_low_level_spec col_pre X) lx2_2 laug2_2 linv2_2.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
    cancel (mpz_array inv_pre (n_pre * n_pre) linv2_2).
    cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) laug2_2).
    cancel (mpz_array x_pre n_pre lx2_2).
  - split_pures; dump_pre_spatial; try exact Hinv_next; try assumption; try lia.
Qed.
