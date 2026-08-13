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
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import col_swap_mod_gmp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import col_swap_mod_gmp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope sac.

Lemma proof_of_col_swap_mod_gmp_entail_wit_1_split_goal_1 :
  col_swap_mod_gmp_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).

  apply col_swap_prefix_init. assumption.
Qed.

Lemma proof_of_col_swap_mod_gmp_entail_wit_1 : col_swap_mod_gmp_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_col_swap_mod_gmp_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_col_swap_mod_gmp_entail_wit_3 : col_swap_mod_gmp_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  subst idx1.
  subst idx2.
  subst lmid.
  destruct (Z_lt_dec (i + 1) n_pre) as [Hi_next | Hi_next].
  - Left. Right.
    Exists (Znth (i * cols + c2_pre) lcur_2 0)
      (Znth (i * cols + c1_pre) lcur_2 0)
      (replace_Znth (i * cols + c2_pre)
        (Znth (i * cols + c1_pre) lcur_2 0)
        (replace_Znth (i * cols + c1_pre)
          (Znth (i * cols + c2_pre) lcur_2 0) lcur_2)).
    assert (Hprefix_next :
      col_swap_prefix
        (replace_Znth (i * cols + c2_pre)
          (Znth (i * cols + c1_pre) lcur_2 0)
          (replace_Znth (i * cols + c1_pre)
            (Znth (i * cols + c2_pre) lcur_2 0) lcur_2))
        n_pre cols M_low_level_spec c1_pre c2_pre (i + 1)).
    { apply col_swap_prefix_update; try assumption; lia. }
    assert (Hcols_pos : 0 < cols) by lia.
    assert (Hnext_mul_nonneg : 0 <= (i + 1) * cols).
    { apply Z.mul_nonneg_nonneg; lia. }
    assert (Hnext_mul_le_pred : (i + 1) * cols <= (n_pre - 1) * cols).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    assert (Hnext_idx1_bound :
      0 <= (i + 1) * cols + c1_pre < n_pre * cols) by lia.
    assert (Hnext_idx2_bound :
      0 <= (i + 1) * cols + c2_pre < n_pre * cols) by lia.
    split_pure_spatial.
    + cancel (store_Z tmp1 (Znth (i * cols + c1_pre) lcur_2 0)).
      cancel (store_Z tmp2 (Znth (i * cols + c2_pre) lcur_2 0)).
      cancel (store_Z p_pre zp_low_level_spec).
      cancel (mpz_array aug_pre (n_pre * cols)
        (replace_Znth (i * cols + c2_pre)
          (Znth (i * cols + c1_pre) lcur_2 0)
          (replace_Znth (i * cols + c1_pre)
            (Znth (i * cols + c2_pre) lcur_2 0) lcur_2))).
    + split_pures;
        dump_pre_spatial;
        try assumption;
        lia.
  - Left. Left. Right.
    Exists (Znth (i * cols + c2_pre) lcur_2 0)
      (Znth (i * cols + c1_pre) lcur_2 0)
      (replace_Znth (i * cols + c2_pre)
        (Znth (i * cols + c1_pre) lcur_2 0)
        (replace_Znth (i * cols + c1_pre)
          (Znth (i * cols + c2_pre) lcur_2 0) lcur_2)).
    assert (Hprefix_next :
      col_swap_prefix
        (replace_Znth (i * cols + c2_pre)
          (Znth (i * cols + c1_pre) lcur_2 0)
          (replace_Znth (i * cols + c1_pre)
            (Znth (i * cols + c2_pre) lcur_2 0) lcur_2))
        n_pre cols M_low_level_spec c1_pre c2_pre (i + 1)).
    { apply col_swap_prefix_update; try assumption; lia. }
    assert (Hi_next_eq : i + 1 = n_pre) by lia.
    assert (Hfinal_idx1_int :
      (i + 1) * cols + c1_pre <= INT_MAX).
    { rewrite Hi_next_eq. replace cols with (n_pre + 1) by lia.
      change INT_MAX with 2147483647. nia. }
    assert (Hfinal_idx2_int :
      (i + 1) * cols + c2_pre <= INT_MAX).
    { rewrite Hi_next_eq. replace cols with (n_pre + 1) by lia.
      change INT_MAX with 2147483647. nia. }
    split_pure_spatial.
    + cancel (store_Z tmp1 (Znth (i * cols + c1_pre) lcur_2 0)).
      cancel (store_Z tmp2 (Znth (i * cols + c2_pre) lcur_2 0)).
      cancel (store_Z p_pre zp_low_level_spec).
      cancel (mpz_array aug_pre (n_pre * cols)
        (replace_Znth (i * cols + c2_pre)
          (Znth (i * cols + c1_pre) lcur_2 0)
          (replace_Znth (i * cols + c1_pre)
            (Znth (i * cols + c2_pre) lcur_2 0) lcur_2))).
    + split_pures;
        dump_pre_spatial;
        try assumption;
        lia.
Qed.

Lemma proof_of_col_swap_mod_gmp_return_wit_1 : col_swap_mod_gmp_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  exfalso.
  assert (Hi_eq : i = n_pre) by lia.
  subst i.
  lia.
Qed.

Lemma proof_of_col_swap_mod_gmp_return_wit_2 : col_swap_mod_gmp_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hrep_swap :
    rep_matrix lcur n_pre (n_pre + 1)
      (matrix_col_swap M_low_level_spec c1_pre c2_pre)).
  { replace (n_pre + 1) with cols by lia.
    eapply col_swap_prefix_full_rep_matrix; eauto; lia. }
  assert (Hmat_swap :
    mat_mod zp_low_level_spec n_pre (n_pre + 1)
      (matrix_col_swap M_low_level_spec c1_pre c2_pre)).
  { replace (n_pre + 1) with cols by lia.
    eapply matrix_col_swap_mat_mod; eauto; lia. }
  Exists lcur.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      exact Hrep_swap.
    + dump_pre_spatial.
      exact Hmat_swap.
Qed.

Lemma proof_of_col_swap_mod_gmp_return_wit_3 : col_swap_mod_gmp_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  exfalso.
  assert (Hi_eq : i = n_pre) by lia.
  subst i.
  lia.
Qed.

Lemma proof_of_col_swap_mod_gmp_return_wit_4 : col_swap_mod_gmp_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  exfalso.
  assert (Hi_eq : i = n_pre) by lia.
  subst i.
  lia.
Qed.
