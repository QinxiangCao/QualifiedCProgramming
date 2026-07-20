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
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import row_scale_mod_gmp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import row_scale_mod_gmp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope sac.

Lemma proof_of_row_scale_mod_gmp_entail_wit_1 : row_scale_mod_gmp_entail_wit_1.
Proof.
  pre_process.
  Exists 0 l_low_level_spec.
  entailer!.
  apply row_scale_prefix_init.
  assumption.
Qed.

Lemma proof_of_row_scale_mod_gmp_entail_wit_2 : row_scale_mod_gmp_entail_wit_2.
Proof.
  unfold row_scale_mod_gmp_entail_wit_2.
  intros.
  set (l_next := replace_Znth (row_pre * cols + j) out lcur_2).
  assert (Hprefix_next :
    row_scale_prefix l_next n_pre cols M_low_level_spec zp_low_level_spec
      row_pre zinv_low_level_spec (j + 1)).
  { subst l_next.
    eapply row_scale_prefix_update; eauto; lia. }
  destruct (Z_lt_dec (j + 1) cols).
  - Left.
    Exists (Znth (row_pre * cols + j) lcur_2 0 * zinv_low_level_spec)
      l_next.
    pose proof (row_major_index_bound n_pre cols row_pre (j + 1)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hnext_bound.
    unfold row_major_index in Hnext_bound.
    split_pure_spatial.
    + subst l_next.
      cancel (store_Z v
        (Znth (row_pre * cols + j) lcur_2 0 * zinv_low_level_spec)).
      cancel (store_Z p_pre zp_low_level_spec).
      cancel (store_Z inv_pre zinv_low_level_spec).
      cancel (mpz_array aug_pre (n_pre * cols)
        (replace_Znth (row_pre * cols + j) out lcur_2)).
    + split_pures; apply dump_spatial_left;
        try exact Hprefix_next; try assumption; try lia.
  - Right.
    Exists (Znth (row_pre * cols + j) lcur_2 0 * zinv_low_level_spec)
      l_next.
    split_pure_spatial.
    + subst l_next.
      cancel (store_Z v
        (Znth (row_pre * cols + j) lcur_2 0 * zinv_low_level_spec)).
      cancel (store_Z p_pre zp_low_level_spec).
      cancel (store_Z inv_pre zinv_low_level_spec).
      cancel (mpz_array aug_pre (n_pre * cols)
        (replace_Znth (row_pre * cols + j) out lcur_2)).
    + split_pures; apply dump_spatial_left;
        try exact Hprefix_next; try assumption; try lia.
Qed.

Lemma proof_of_row_scale_mod_gmp_return_wit_1 : row_scale_mod_gmp_return_wit_1.
Proof.
  unfold row_scale_mod_gmp_return_wit_1.
  left.
  intros.
  assert (Hrep_scale :
    rep_matrix lcur n_pre (n_pre + 1)
      (matrix_row_scale_mod zp_low_level_spec M_low_level_spec row_pre
        zinv_low_level_spec)).
  { replace (n_pre + 1) with cols by lia.
    eapply row_scale_prefix_full_rep_matrix; eauto; lia. }
  assert (Hmat_scale :
    mat_mod zp_low_level_spec n_pre (n_pre + 1)
      (matrix_row_scale_mod zp_low_level_spec M_low_level_spec row_pre
        zinv_low_level_spec)).
  { replace (n_pre + 1) with cols by lia.
    eapply matrix_row_scale_mod_mat_mod; eauto; lia. }
  Exists lcur.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z inv_pre zinv_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
  - split_pures; apply dump_spatial_left; try assumption; try lia.
Qed.

Lemma proof_of_row_scale_mod_gmp_return_wit_2 : row_scale_mod_gmp_return_wit_2.
Proof.
  unfold row_scale_mod_gmp_return_wit_2.
  left.
  intros.
  assert (Hrep_scale :
    rep_matrix lcur n_pre (n_pre + 1)
      (matrix_row_scale_mod zp_low_level_spec M_low_level_spec row_pre
        zinv_low_level_spec)).
  { replace (n_pre + 1) with cols by lia.
    eapply row_scale_prefix_full_rep_matrix; eauto; lia. }
  assert (Hmat_scale :
    mat_mod zp_low_level_spec n_pre (n_pre + 1)
      (matrix_row_scale_mod zp_low_level_spec M_low_level_spec row_pre
        zinv_low_level_spec)).
  { replace (n_pre + 1) with cols by lia.
    eapply matrix_row_scale_mod_mat_mod; eauto; lia. }
  Exists lcur.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z inv_pre zinv_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
  - split_pures; apply dump_spatial_left; try assumption; try lia.
Qed.

Lemma proof_of_row_scale_mod_gmp_partial_solve_wit_4_pure : row_scale_mod_gmp_partial_solve_wit_4_pure.
Proof.
  unfold row_scale_mod_gmp_partial_solve_wit_4_pure.
  right.
  intros.
  pre_process.
  prop_apply (valid_store_ptr (&("aug")) aug_pre).
  Intros.
  split_pures.
  - dump_pre_spatial.
    apply mpz_offset_nonnull; try assumption; lia.
  - dump_pre_spatial.
    apply mpz_offset_nonnull; try assumption; lia.
Qed.
