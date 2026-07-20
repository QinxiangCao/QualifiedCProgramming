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
  unfold build_inverse_cols_gmp_entail_wit_1.
  right.
  intros.
  assert (Hpartial :
    partial_rep_matrix_cols linv_low_level_spec n_pre 0 A_low_level_spec).
  { apply partial_rep_matrix_cols_0_from_length; assumption. }
  assert (Hprefix :
    inverse_cols_prefix_spec zp_low_level_spec n_pre A_low_level_spec
      A_low_level_spec 0).
  { apply inverse_cols_prefix_spec_init; assumption. }
  Exists A_low_level_spec.
  entailer!.
Qed.

Lemma proof_of_build_inverse_cols_gmp_entail_wit_3 : build_inverse_cols_gmp_entail_wit_3.
Proof.
  unfold build_inverse_cols_gmp_entail_wit_3.
  right.
  intros.
  replace col with n_pre in * by lia.
  assert (Hrep : rep_matrix linv_cur n_pre n_pre Bcur).
  { apply partial_rep_matrix_cols_full_rep_matrix; assumption. }
  assert (Hsuccess :
    matrix_inverse_success zp_low_level_spec n_pre A_low_level_spec Bcur).
  { apply matrix_inverse_success_from_cols; [lia | assumption]. }
  Exists Bcur.
  entailer!.
Qed.

Lemma proof_of_build_inverse_cols_gmp_return_wit_1 : build_inverse_cols_gmp_return_wit_1.
Proof.
  unfold build_inverse_cols_gmp_return_wit_1.
  right.
  intros.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
  - split_pures.
    dump_pre_spatial.
    intros _.
    refine (ex_intro _ Bfin _).
    split; assumption.
Qed.

Lemma proof_of_build_inverse_cols_gmp_partial_solve_wit_1_pure : build_inverse_cols_gmp_partial_solve_wit_1_pure.
Proof.
  unfold build_inverse_cols_gmp_partial_solve_wit_1_pure.
  right.
  intros.
  prop_apply_p (mpz_array_Zlength x_pre n_pre lx_cur).
  entailer!.
Qed.
