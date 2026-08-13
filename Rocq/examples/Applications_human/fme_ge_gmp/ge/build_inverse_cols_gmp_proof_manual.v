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
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import build_inverse_cols_gmp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import build_inverse_cols_gmp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope sac.

Lemma proof_of_build_inverse_cols_gmp_entail_wit_1 : build_inverse_cols_gmp_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hpartial :
    partial_rep_matrix_cols linv_low_level_spec n_pre 0 A_low_level_spec).
  { apply partial_rep_matrix_cols_0_from_length; assumption. }
  assert (Hprefix :
    inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec
      A_low_level_spec 0).
  { apply inverse_cols_prefix_spec_init; assumption. }
  Exists lx_low_level_spec laug_low_level_spec linv_low_level_spec A_low_level_spec.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
    cancel (mpz_array inv_pre (n_pre * n_pre) linv_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) laug_low_level_spec).
    cancel (mpz_array x_pre n_pre lx_low_level_spec).
  - split_pures; dump_pre_spatial;
      try assumption; try lia; try exact Hpartial; try exact Hprefix.
Qed.

Lemma proof_of_build_inverse_cols_gmp_entail_wit_2 : build_inverse_cols_gmp_entail_wit_2.
Proof.
  aggressive_pre_process.
  Exists Inv2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try lia; try exact PreH3; try exact PreH4.
Qed.

Lemma proof_of_build_inverse_cols_gmp_entail_wit_3 : build_inverse_cols_gmp_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace col with n_pre in * by lia.
  assert (Hrep : rep_matrix linv_cur n_pre n_pre Bcur).
  { apply partial_rep_matrix_cols_full_rep_matrix; assumption. }
  assert (Hsuccess :
    matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bcur).
  { apply matrix_inverse_success_from_cols; [lia | assumption]. }
  Exists lx_cur_2 laug_cur_2 linv_cur Bcur.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
    cancel (mpz_array inv_pre (n_pre * n_pre) linv_cur).
    cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) laug_cur_2).
    cancel (mpz_array x_pre n_pre lx_cur_2).
  - split_pures; dump_pre_spatial;
      try assumption; try lia; try exact Hrep; try exact Hsuccess.
Qed.

Lemma proof_of_build_inverse_cols_gmp_return_wit_1_split_goal_1 :
  build_inverse_cols_gmp_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  refine (ex_intro _ Bfin _).
  split; assumption.
Qed.

Lemma proof_of_build_inverse_cols_gmp_return_wit_1 : build_inverse_cols_gmp_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_build_inverse_cols_gmp_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_build_inverse_cols_gmp_partial_solve_wit_1_pure_split_goal_1 :
  build_inverse_cols_gmp_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (mpz_array_Zlength x_pre n_pre lx_cur).
  Intros_p Hlen.
  dump_pre_spatial.
  exact Hlen.
Qed.

Lemma proof_of_build_inverse_cols_gmp_partial_solve_wit_1_pure :
  build_inverse_cols_gmp_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_build_inverse_cols_gmp_partial_solve_wit_1_pure_split_goal_1.
Qed.
