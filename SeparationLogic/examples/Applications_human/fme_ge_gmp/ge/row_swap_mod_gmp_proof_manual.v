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
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import row_swap_mod_gmp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import row_swap_mod_gmp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope sac.

Lemma proof_of_row_swap_mod_gmp_entail_wit_1 : row_swap_mod_gmp_entail_wit_1.
Proof.
  pre_process.
  Exists 0 0 l_low_level_spec.
  entailer!.
  apply row_swap_prefix_init.
  assumption.
Qed.

Lemma proof_of_row_swap_mod_gmp_entail_wit_3 : row_swap_mod_gmp_entail_wit_3.
Proof.
  unfold row_swap_mod_gmp_entail_wit_3.
  intros.
  subst idx1.
  subst idx2.
  subst lmid.
  destruct (Z_lt_dec (j + 1) cols).
  - assert (Hprefix_next :
      row_swap_prefix
        (replace_Znth (r2_pre * cols + j) (Znth (r1_pre * cols + j) lcur_2 0)
          (replace_Znth (r1_pre * cols + j) (Znth (r2_pre * cols + j) lcur_2 0) lcur_2))
        n_pre cols M_low_level_spec r1_pre r2_pre (j + 1)).
    { apply row_swap_prefix_update; try assumption; lia. }
    pose proof (row_major_index_bound n_pre cols r1_pre (j + 1)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hr1_next_bound.
    pose proof (row_major_index_bound n_pre cols r2_pre (j + 1)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hr2_next_bound.
    unfold row_major_index in Hr1_next_bound, Hr2_next_bound.
    Left. Left. Right.
    Exists (Znth (r2_pre * cols + j) lcur_2 0)
      (Znth (r1_pre * cols + j) lcur_2 0)
      (replace_Znth (r2_pre * cols + j) (Znth (r1_pre * cols + j) lcur_2 0)
        (replace_Znth (r1_pre * cols + j) (Znth (r2_pre * cols + j) lcur_2 0) lcur_2)).
    split_pure_spatial.
    + cancel (store_Z tmp1 (Znth (r1_pre * cols + j) lcur_2 0)).
      cancel (store_Z tmp2 (Znth (r2_pre * cols + j) lcur_2 0)).
      cancel (store_Z p_pre zp_low_level_spec).
      cancel (mpz_array aug_pre (n_pre * cols)
        (replace_Znth (r2_pre * cols + j) (Znth (r1_pre * cols + j) lcur_2 0)
          (replace_Znth (r1_pre * cols + j) (Znth (r2_pre * cols + j) lcur_2 0) lcur_2))).
    + split_pures; apply dump_spatial_left; try assumption; try lia.
  - assert (Hprefix_next :
      row_swap_prefix
        (replace_Znth (r2_pre * cols + j) (Znth (r1_pre * cols + j) lcur_2 0)
          (replace_Znth (r1_pre * cols + j) (Znth (r2_pre * cols + j) lcur_2 0) lcur_2))
        n_pre cols M_low_level_spec r1_pre r2_pre (j + 1)).
    { apply row_swap_prefix_update; try assumption; lia. }
    Left. Right.
    Exists (Znth (r2_pre * cols + j) lcur_2 0)
      (Znth (r1_pre * cols + j) lcur_2 0)
      (replace_Znth (r2_pre * cols + j) (Znth (r1_pre * cols + j) lcur_2 0)
        (replace_Znth (r1_pre * cols + j) (Znth (r2_pre * cols + j) lcur_2 0) lcur_2)).
    split_pure_spatial.
    + cancel (store_Z tmp1 (Znth (r1_pre * cols + j) lcur_2 0)).
      cancel (store_Z tmp2 (Znth (r2_pre * cols + j) lcur_2 0)).
      cancel (store_Z p_pre zp_low_level_spec).
      cancel (mpz_array aug_pre (n_pre * cols)
        (replace_Znth (r2_pre * cols + j) (Znth (r1_pre * cols + j) lcur_2 0)
          (replace_Znth (r1_pre * cols + j) (Znth (r2_pre * cols + j) lcur_2 0) lcur_2))).
    + split_pures; apply dump_spatial_left; try assumption; try lia.
Qed.

Lemma proof_of_row_swap_mod_gmp_return_wit_1 : row_swap_mod_gmp_return_wit_1.
Proof.
  unfold row_swap_mod_gmp_return_wit_1.
  left.
  intros.
  assert (Hrep_swap :
    rep_matrix lcur n_pre (n_pre + 1) (matrix_row_swap M_low_level_spec r1_pre r2_pre)).
  { replace (n_pre + 1) with cols by lia.
    eapply row_swap_prefix_full_rep_matrix; eauto; lia. }
  Exists lcur.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
  - split_pures; apply dump_spatial_left; try assumption; try lia.
Qed.

Lemma proof_of_row_swap_mod_gmp_return_wit_2 : row_swap_mod_gmp_return_wit_2.
Proof.
  unfold row_swap_mod_gmp_return_wit_2.
  left.
  intros.
  assert (Hrep_swap :
    rep_matrix lcur n_pre (n_pre + 1) (matrix_row_swap M_low_level_spec r1_pre r2_pre)).
  { replace (n_pre + 1) with cols by lia.
    eapply row_swap_prefix_full_rep_matrix; eauto; lia. }
  Exists lcur.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
  - split_pures; apply dump_spatial_left; try assumption; try lia.
Qed.

Lemma proof_of_row_swap_mod_gmp_return_wit_3 : row_swap_mod_gmp_return_wit_3.
Proof.
  unfold row_swap_mod_gmp_return_wit_3.
  left.
  intros.
  assert (Hrep_swap :
    rep_matrix lcur n_pre (n_pre + 1) (matrix_row_swap M_low_level_spec r1_pre r2_pre)).
  { replace (n_pre + 1) with cols by lia.
    eapply row_swap_prefix_full_rep_matrix; eauto; lia. }
  Exists lcur.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
  - split_pures; apply dump_spatial_left; try assumption; try lia.
Qed.

Lemma proof_of_row_swap_mod_gmp_return_wit_4 : row_swap_mod_gmp_return_wit_4.
Proof.
  unfold row_swap_mod_gmp_return_wit_4.
  left.
  intros.
  assert (Hrep_swap :
    rep_matrix lcur n_pre (n_pre + 1) (matrix_row_swap M_low_level_spec r1_pre r2_pre)).
  { replace (n_pre + 1) with cols by lia.
    eapply row_swap_prefix_full_rep_matrix; eauto; lia. }
  Exists lcur.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
  - split_pures; apply dump_spatial_left; try assumption; try lia.
Qed.
