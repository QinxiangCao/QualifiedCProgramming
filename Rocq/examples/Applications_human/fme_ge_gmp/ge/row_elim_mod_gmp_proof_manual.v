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
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import row_elim_mod_gmp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import row_elim_mod_gmp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope sac.

Lemma proof_of_row_elim_mod_gmp_entail_wit_1 : row_elim_mod_gmp_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists 0 0 l_low_level_spec.
  split_pure_spatial.
  - cancel (store_Z retval_2 0).
    cancel (store_Z retval 0).
    cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z factor_pre zfactor_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) l_low_level_spec).
  - repeat split_pures; try solve
      [ dump_pre_spatial; int_auto
      | dump_pre_spatial; nia
      | dump_pre_spatial; rewrite Z.compare_lt_iff; lia
      | dump_pre_spatial; apply row_elim_prefix_init; assumption ].
Qed.

Lemma proof_of_row_elim_mod_gmp_entail_wit_2 : row_elim_mod_gmp_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  set (l_next := replace_Znth (target_pre * cols + j) out lcur_2).
  assert (Hnorm_cols :
    mod_norm_spec zp_low_level_spec
      (Znth (target_pre * cols + j) lcur_2 0 -
        zfactor_low_level_spec * Znth (pivot_pre * cols + j) lcur_2 0) out).
  { replace (target_pre * cols + j) with (target_pre * (n_pre + 1) + j) by lia.
    replace (pivot_pre * cols + j) with (pivot_pre * (n_pre + 1) + j) by lia.
    exact PreH1. }
  assert (Hprefix_next :
    row_elim_prefix l_next n_pre cols M_low_level_spec zp_low_level_spec
      pivot_pre target_pre zfactor_low_level_spec (j + 1)).
  { subst l_next.
    eapply row_elim_prefix_update.
    - exact PreH38.
    - lia.
    - lia.
    - exact PreH19.
    - lia.
    - exact Hnorm_cols. }
  destruct (Z_lt_dec (j + 1) cols).
  - Left. Right.
    Exists (zfactor_low_level_spec * (Znth (pivot_pre * (n_pre + 1) + j) lcur_2 0))
      (Znth (target_pre * (n_pre + 1) + j) lcur_2 0 -
        zfactor_low_level_spec * (Znth (pivot_pre * (n_pre + 1) + j) lcur_2 0))
      l_next.
    pose proof (row_major_index_bound n_pre cols target_pre (j + 1)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Htarget_next_bound.
    pose proof (row_major_index_bound n_pre cols pivot_pre (j + 1)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hpivot_next_bound.
    unfold row_major_index in *.
    subst l_next.
    split_pure_spatial.
    + cancel (store_Z v
        (Znth (target_pre * (n_pre + 1) + j) lcur_2 0 -
          zfactor_low_level_spec * (Znth (pivot_pre * (n_pre + 1) + j) lcur_2 0))).
      cancel (store_Z prod
        (zfactor_low_level_spec * (Znth (pivot_pre * (n_pre + 1) + j) lcur_2 0))).
      cancel (store_Z p_pre zp_low_level_spec).
      cancel (store_Z factor_pre zfactor_low_level_spec).
      cancel (mpz_array aug_pre (n_pre * cols)
        (replace_Znth (target_pre * cols + j) out lcur_2)).
    + split_pures; try exact Hprefix_next; try lia;
        dump_pre_spatial; try assumption; try lia.
  - Left. Left. Right.
    Exists (zfactor_low_level_spec * (Znth (pivot_pre * (n_pre + 1) + j) lcur_2 0))
      (Znth (target_pre * (n_pre + 1) + j) lcur_2 0 -
        zfactor_low_level_spec * (Znth (pivot_pre * (n_pre + 1) + j) lcur_2 0))
      l_next.
    assert (Hj_next_eq : j + 1 = cols) by lia.
    assert (Htarget_next_int : target_pre * cols + (j + 1) <= INT_MAX).
    { rewrite Hj_next_eq.
      replace (target_pre * cols + cols) with ((target_pre + 1) * cols) by lia.
      assert ((target_pre + 1) * cols <= n_pre * cols).
      { apply Z.mul_le_mono_nonneg_r; lia. }
      lia. }
    assert (Hpivot_next_int : pivot_pre * cols + (j + 1) <= INT_MAX).
    { rewrite Hj_next_eq.
      replace (pivot_pre * cols + cols) with ((pivot_pre + 1) * cols) by lia.
      assert ((pivot_pre + 1) * cols <= n_pre * cols).
      { apply Z.mul_le_mono_nonneg_r; lia. }
      lia. }
    subst l_next.
    split_pure_spatial.
    + cancel (store_Z v
        (Znth (target_pre * (n_pre + 1) + j) lcur_2 0 -
          zfactor_low_level_spec * (Znth (pivot_pre * (n_pre + 1) + j) lcur_2 0))).
      cancel (store_Z prod
        (zfactor_low_level_spec * (Znth (pivot_pre * (n_pre + 1) + j) lcur_2 0))).
      cancel (store_Z p_pre zp_low_level_spec).
      cancel (store_Z factor_pre zfactor_low_level_spec).
      cancel (mpz_array aug_pre (n_pre * cols)
        (replace_Znth (target_pre * cols + j) out lcur_2)).
    + split_pures; try exact Hprefix_next; try lia;
        dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_row_elim_mod_gmp_return_wit_1 : row_elim_mod_gmp_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  assert (Hrep_elim :
    rep_matrix lcur n_pre (n_pre + 1)
      (matrix_row_elim_mod zp_low_level_spec M_low_level_spec pivot_pre
        target_pre zfactor_low_level_spec)).
  { replace (n_pre + 1) with cols by lia.
    eapply row_elim_prefix_full_rep_matrix; eauto; lia. }
  assert (Hmat_elim :
    mat_mod zp_low_level_spec n_pre (n_pre + 1)
      (matrix_row_elim_mod zp_low_level_spec M_low_level_spec pivot_pre
        target_pre zfactor_low_level_spec)).
  { replace (n_pre + 1) with cols by lia.
    eapply matrix_row_elim_mod_mat_mod; eauto; lia. }
  Exists lcur.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z factor_pre zfactor_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_row_elim_mod_gmp_return_wit_2 : row_elim_mod_gmp_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  assert (Hrep_elim :
    rep_matrix lcur n_pre (n_pre + 1)
      (matrix_row_elim_mod zp_low_level_spec M_low_level_spec pivot_pre
        target_pre zfactor_low_level_spec)).
  { replace (n_pre + 1) with cols by lia.
    eapply row_elim_prefix_full_rep_matrix; eauto; lia. }
  assert (Hmat_elim :
    mat_mod zp_low_level_spec n_pre (n_pre + 1)
      (matrix_row_elim_mod zp_low_level_spec M_low_level_spec pivot_pre
        target_pre zfactor_low_level_spec)).
  { replace (n_pre + 1) with cols by lia.
    eapply matrix_row_elim_mod_mat_mod; eauto; lia. }
  Exists lcur.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z factor_pre zfactor_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_row_elim_mod_gmp_return_wit_3 : row_elim_mod_gmp_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  assert (Hrep_elim :
    rep_matrix lcur n_pre (n_pre + 1)
      (matrix_row_elim_mod zp_low_level_spec M_low_level_spec pivot_pre
        target_pre zfactor_low_level_spec)).
  { replace (n_pre + 1) with cols by lia.
    eapply row_elim_prefix_full_rep_matrix; eauto; lia. }
  assert (Hmat_elim :
    mat_mod zp_low_level_spec n_pre (n_pre + 1)
      (matrix_row_elim_mod zp_low_level_spec M_low_level_spec pivot_pre
        target_pre zfactor_low_level_spec)).
  { replace (n_pre + 1) with cols by lia.
    eapply matrix_row_elim_mod_mat_mod; eauto; lia. }
  Exists lcur.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z factor_pre zfactor_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_row_elim_mod_gmp_return_wit_4 : row_elim_mod_gmp_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  assert (Hrep_elim :
    rep_matrix lcur n_pre (n_pre + 1)
      (matrix_row_elim_mod zp_low_level_spec M_low_level_spec pivot_pre
        target_pre zfactor_low_level_spec)).
  { replace (n_pre + 1) with cols by lia.
    eapply row_elim_prefix_full_rep_matrix; eauto; lia. }
  assert (Hmat_elim :
    mat_mod zp_low_level_spec n_pre (n_pre + 1)
      (matrix_row_elim_mod zp_low_level_spec M_low_level_spec pivot_pre
        target_pre zfactor_low_level_spec)).
  { replace (n_pre + 1) with cols by lia.
    eapply matrix_row_elim_mod_mat_mod; eauto; lia. }
  Exists lcur.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z factor_pre zfactor_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
  - split_pures; dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_row_elim_mod_gmp_partial_solve_wit_8_pure_split_goal_1 :
  row_elim_mod_gmp_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (valid_store_ptr (&("aug")) aug_pre).
  Intros.
  destruct H as [_ Hvalid_aug].
  unfold valid_ptr_value in Hvalid_aug.
  dump_pre_spatial.
  change (sizeof ("__mpz_struct")) with mpz_sizeof.
  rewrite mpz_sizeof_eq_12.
  lia.
Qed.

Lemma proof_of_row_elim_mod_gmp_partial_solve_wit_8_pure_split_goal_2 :
  row_elim_mod_gmp_partial_solve_wit_8_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (valid_store_ptr (&("aug")) aug_pre).
  Intros.
  destruct H as [_ Hvalid_aug].
  unfold valid_ptr_value in Hvalid_aug.
  dump_pre_spatial.
  change (sizeof ("__mpz_struct")) with mpz_sizeof.
  rewrite mpz_sizeof_eq_12.
  lia.
Qed.

Lemma proof_of_row_elim_mod_gmp_partial_solve_wit_8_pure :
  row_elim_mod_gmp_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_row_elim_mod_gmp_partial_solve_wit_8_pure_split_goal_1.
  + Goal_apply proof_of_row_elim_mod_gmp_partial_solve_wit_8_pure_split_goal_2.
Qed.
