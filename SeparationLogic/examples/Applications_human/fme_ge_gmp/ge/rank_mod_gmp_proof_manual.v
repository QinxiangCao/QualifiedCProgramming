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
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import rank_mod_gmp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import rank_mod_gmp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope sac.

Lemma proof_of_rank_mod_gmp_entail_wit_1 : rank_mod_gmp_entail_wit_1.
Proof.
  unfold rank_mod_gmp_entail_wit_1.
  left.
  intros.
  Exists l_low_level_spec M0_low_level_spec.
  entailer!.
  unfold rank_inv_mod.
  split; [assumption | split].
  - constructor.
  - unfold rref_prefix_mod. repeat split; try lia.
Qed. 

Lemma proof_of_rank_mod_gmp_entail_wit_2 : rank_mod_gmp_entail_wit_2.
Proof.
  unfold rank_mod_gmp_entail_wit_2.
  right.
  intros.
  assert (Hprefix : search_submatrix_zero_prefix_mod n_pre k k k M0).
  { apply search_submatrix_zero_prefix_mod_init. lia. }
  split_pure_spatial; [entailer! |].
  split_pures; apply dump_spatial_left; try assumption; try lia; try nia.
Qed. 

Lemma proof_of_rank_mod_gmp_entail_wit_3_1 : rank_mod_gmp_entail_wit_3_1.
Proof.
  unfold rank_mod_gmp_entail_wit_3_1.
  intros.
  subst col.
  assert (Hprefix_next : search_submatrix_zero_prefix_mod n_pre k (pivot + 1) k M0).
  { eapply search_submatrix_zero_prefix_mod_row_step; eauto; lia. }
  destruct (Z_lt_ge_dec (pivot + 1) n_pre) as [Hlt | Hge].
  - repeat Left.
    split_pure_spatial; [entailer! |].
    split_pures; apply dump_spatial_left; try assumption; try lia; nia.
  - Right.
    split_pure_spatial; [entailer! |].
    split_pures; apply dump_spatial_left; try assumption; try lia; nia.
Qed. 

Lemma proof_of_rank_mod_gmp_entail_wit_3_2 : rank_mod_gmp_entail_wit_3_2.
Proof.
  unfold rank_mod_gmp_entail_wit_3_2.
  intros.
  subst col.
  assert (Hprefix_next : search_submatrix_zero_prefix_mod n_pre k (pivot + 1) k M0).
  { eapply search_submatrix_zero_prefix_mod_row_step; eauto; lia. }
  destruct (Z_lt_ge_dec (pivot + 1) n_pre) as [Hlt | Hge].
  - repeat Left.
    split_pure_spatial; [entailer! |].
    split_pures; apply dump_spatial_left; try assumption; try lia; nia.
  - Right.
    split_pure_spatial; [entailer! |].
    split_pures; apply dump_spatial_left; try assumption; try lia; nia.
Qed. 

Lemma proof_of_rank_mod_gmp_entail_wit_3_3 : rank_mod_gmp_entail_wit_3_3.
Proof.
  unfold rank_mod_gmp_entail_wit_3_3.
  intros.
  assert (Hcur_zero : M0 pivot col = 0).
  {
    pose proof (rep_matrix_nth lcur n_pre cols M0 pivot col PreH35
      ltac:(lia) ltac:(lia))
      as Hnth.
    rewrite <- Hnth.
    rewrite <- PreH2.
    f_equal; unfold row_major_index; lia.
  }
  assert (Hprefix_next :
    search_submatrix_zero_prefix_mod n_pre k pivot (col + 1) M0).
  {
    eapply search_submatrix_zero_prefix_mod_col_step; eauto; lia.
  }
  destruct (Z_lt_ge_dec (col + 1) n_pre) as [Hlt | Hge].
  - repeat Left.
    split_pure_spatial.
    + cancel (store_Z p_pre zp_low_level_spec).
      cancel (mpz_array aug_pre (n_pre * cols) lcur).
    + split_pures; try assumption; try exact Hprefix_next; try lia;
        apply dump_spatial_left; try assumption; try lia; nia.
  - Right.
    split_pure_spatial.
    + cancel (store_Z p_pre zp_low_level_spec).
      cancel (mpz_array aug_pre (n_pre * cols) lcur).
    + split_pures; try assumption; try exact Hprefix_next; try lia;
        apply dump_spatial_left; try assumption; try lia; nia.
Qed. 

Lemma proof_of_rank_mod_gmp_entail_wit_3_4 : rank_mod_gmp_entail_wit_3_4.
Proof.
  unfold rank_mod_gmp_entail_wit_3_4.
  left.
  intros.
  destruct PreH38 as [[Hk_pivot Hpivot_bound] [[Hk_col Hcol_bound] [Hrows Hcur]]].
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
  - split_pures; try reflexivity; try assumption; try lia;
      apply dump_spatial_left; try assumption; lia.
Qed. 

Lemma proof_of_rank_mod_gmp_entail_wit_3_5 : rank_mod_gmp_entail_wit_3_5.
Proof.
  unfold rank_mod_gmp_entail_wit_3_5.
  left.
  intros.
  destruct PreH38 as [[Hk_pivot Hpivot_bound] [[Hk_col Hcol_bound] [Hrows Hcur]]].
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
  - split_pures; try reflexivity; try assumption; try lia;
      apply dump_spatial_left; try assumption; lia.
Qed. 

Lemma proof_of_rank_mod_gmp_entail_wit_4 : rank_mod_gmp_entail_wit_4.
Proof.
  unfold rank_mod_gmp_entail_wit_4.
  left.
  intros.
  assert (Hrep_aug : rep_matrix lcur n_pre (n_pre + 1) M0).
  { replace (n_pre + 1) with cols by lia; exact PreH32. }
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial; [entailer! |].
  split_pures; apply dump_spatial_left; try assumption; try lia; try nia.
Qed. 

Lemma proof_of_rank_mod_gmp_entail_wit_6_1 : rank_mod_gmp_entail_wit_6_1.
Proof.
  unfold rank_mod_gmp_entail_wit_6_1.
  left.
  intros.
  assert (Hrep_swap_cols :
    rep_matrix l2 n_pre cols (matrix_row_swap M0 k pivot)).
  { replace cols with (n_pre + 1) by lia. exact PreH1. }
  assert (Hrep_cur_cols : rep_matrix lcur n_pre cols M0).
  { replace cols with (n_pre + 1) by lia. exact PreH24. }
  assert (Hinv_swap :
    rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec
      (matrix_row_swap M0 k pivot)).
  { eapply row_swap_preserves_rank_inv_mod; eauto; lia. }
  assert (Hmat_swap :
    mat_mod zp_low_level_spec n_pre (n_pre + 1) (matrix_row_swap M0 k pivot)).
  { unfold rank_inv_mod in Hinv_swap. tauto. }
  assert (Hzswap_eq :
    Znth (k * cols + col) l2 0 = matrix_row_swap M0 k pivot k col).
  { replace (k * cols + col) with (row_major_index cols k col)
      by (unfold row_major_index; lia).
    apply (rep_matrix_nth l2 n_pre cols
      (matrix_row_swap M0 k pivot) k col Hrep_swap_cols); lia. }
  assert (Hcur_eq :
    Znth (pivot * cols + col) lcur 0 = M0 pivot col).
  { replace (pivot * cols + col)
      with (row_major_index cols pivot col)
      by (unfold row_major_index; lia).
    apply (rep_matrix_nth lcur n_pre cols M0 pivot col Hrep_cur_cols);
      lia. }
  assert (Hzswap_nz : Znth (k * cols + col) l2 0 <> 0).
  { rewrite Hzswap_eq.
    unfold matrix_row_swap.
    destruct (Z.eq_dec k k); [| lia].
    rewrite <- Hcur_eq.
    exact PreH21. }
  Exists l2 (matrix_row_swap M0 k pivot).
  split_pure_spatial; [entailer! |].
  split_pures; apply dump_spatial_left; try exact Hmat_colswap;
    try exact Hinv_colswap; try exact Hzdiag_nz; try assumption; lia.
Qed. 

Lemma proof_of_rank_mod_gmp_entail_wit_6_2 : rank_mod_gmp_entail_wit_6_2.
Proof.
  unfold rank_mod_gmp_entail_wit_6_2.
  left.
  intros.
  assert (Hmat_cur : mat_mod zp_low_level_spec n_pre (n_pre + 1) M0).
  { unfold rank_inv_mod in PreH24. tauto. }
  assert (Hzkc_nz : Znth (k * cols + col) lcur 0 <> 0).
  { replace (k * cols + col) with (pivot * cols + col) by lia.
    exact PreH20. }
  Exists lcur M0.
  split_pure_spatial.
  - entailer!.
  - split_pures; apply dump_spatial_left; try exact Hmat_cur; try exact Hzkc_nz;
      try assumption; try lia.
Qed. 

Lemma proof_of_rank_mod_gmp_entail_wit_8_1 : rank_mod_gmp_entail_wit_8_1.
Proof.
  unfold rank_mod_gmp_entail_wit_8_1.
  left.
  intros.
  assert (Hrep_swap_src_cols : rep_matrix lswap n_pre cols Mswap).
  { replace cols with (n_pre + 1) by lia. exact PreH22. }
  assert (Hk_col : k <= col).
  { destruct (Z_le_gt_dec k col) as [Hle | Hlt]; [exact Hle | exfalso].
    assert (Hzkc_eq : Znth (k * cols + col) lswap 0 = Mswap k col).
    { replace (k * cols + col) with (row_major_index cols k col)
        by (unfold row_major_index; lia).
      apply (rep_matrix_nth lswap n_pre cols Mswap k col Hrep_swap_src_cols);
        lia. }
    match goal with
    | Hrank : rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec Mswap |- _ =>
        unfold rank_inv_mod in Hrank;
        destruct Hrank as [_ [_ Hrref]]
    end.
    unfold rref_prefix_mod in Hrref.
    destruct Hrref as [_ [_ Hrref_entry]].
    specialize (Hrref_entry k col ltac:(lia) ltac:(lia)).
    rewrite <- Hzkc_eq in Hrref_entry.
    destruct (Z.eq_dec k col); lia. }
  assert (Hrep_colswap_cols :
    rep_matrix l2 n_pre cols (matrix_col_swap Mswap k col)).
  { replace cols with (n_pre + 1) by lia. exact PreH1. }
  assert (Hinv_colswap :
    rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec
      (matrix_col_swap Mswap k col)).
  { eapply col_swap_preserves_rank_inv_mod; eauto; lia. }
  assert (Hmat_colswap :
    mat_mod zp_low_level_spec n_pre cols (matrix_col_swap Mswap k col)).
  { replace cols with (n_pre + 1) by lia. exact PreH2. }
  assert (Hzdiag_eq :
    Znth (k * cols + k) l2 0 = matrix_col_swap Mswap k col k k).
  { replace (k * cols + k) with (row_major_index cols k k)
      by (unfold row_major_index; lia).
    apply (rep_matrix_nth l2 n_pre cols
      (matrix_col_swap Mswap k col) k k Hrep_colswap_cols); lia. }
  assert (Hzold_eq :
    Znth (k * cols + col) lswap 0 = Mswap k col).
  { replace (k * cols + col) with (row_major_index cols k col)
      by (unfold row_major_index; lia).
    apply (rep_matrix_nth lswap n_pre cols Mswap k col Hrep_swap_src_cols);
      lia. }
  assert (Hzdiag_nz : Znth (k * cols + k) l2 0 <> 0).
  { rewrite Hzdiag_eq.
    unfold matrix_col_swap.
    destruct (Z.eq_dec k k); [| lia].
    rewrite <- Hzold_eq.
    exact PreH25. }
  pose proof (row_major_index_bound n_pre cols k k
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hkk_index.
  unfold row_major_index in Hkk_index.
  assert (Hkcols_nonneg : 0 <= k * cols).
  { apply Z.mul_nonneg_nonneg; lia. }
  assert (Hkk_nonneg : 0 <= k * cols + k) by lia.
  assert (Hkk_lt : k * cols + k < n_pre * cols) by lia.
  assert (Hkcols_min : INT_MIN <= k * cols) by lia.
  assert (Hkcols_int : k * cols <= INT_MAX) by lia.
  assert (Hkk_min : INT_MIN <= k * cols + k) by lia.
  assert (Hkk_int : k * cols + k <= INT_MAX) by lia.
  Exists l2 (matrix_col_swap Mswap k col).
  replace (n_pre * cols) with (n_pre * (n_pre + 1)) by lia.
  split_pure_spatial; [entailer! |].
  entailer!.
Qed. 

Lemma proof_of_rank_mod_gmp_entail_wit_8_2 : rank_mod_gmp_entail_wit_8_2.
Proof.
  unfold rank_mod_gmp_entail_wit_8_2.
  left.
  intros.
  subst col.
  assert (Hmat_swap_cols : mat_mod zp_low_level_spec n_pre cols Mswap).
  { replace cols with (n_pre + 1) by lia. exact PreH21. }
  pose proof (row_major_index_bound n_pre cols k k
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hkk_index.
  unfold row_major_index in Hkk_index.
  assert (Hkcols_nonneg : 0 <= k * cols).
  { apply Z.mul_nonneg_nonneg; lia. }
  assert (Hkk_nonneg : 0 <= k * cols + k) by lia.
  assert (Hkk_lt : k * cols + k < n_pre * cols) by lia.
  assert (Hkcols_min : INT_MIN <= k * cols) by lia.
  assert (Hkcols_int : k * cols <= INT_MAX) by lia.
  assert (Hkk_min : INT_MIN <= k * cols + k) by lia.
  assert (Hkk_int : k * cols + k <= INT_MAX) by lia.
  Exists lswap Mswap.
  replace (n_pre * cols) with (n_pre * (n_pre + 1)) by lia.
  split_pure_spatial.
  - entailer!.
  - entailer!.
Qed. 

Lemma proof_of_rank_mod_gmp_entail_wit_9 : rank_mod_gmp_entail_wit_9.
Proof.
  unfold rank_mod_gmp_entail_wit_9.
  left.
  intros.
  pose proof PreH1 as Hinv_spec.
  unfold mod_inverse_spec in Hinv_spec.
  destruct Hinv_spec as [_ [_ [Hinv_range _]]].
  assert (Hrep_aug : rep_matrix l1 n_pre (n_pre + 1) M1).
  { exact PreH27. }
  assert (Hmat_aug : mat_mod zp_low_level_spec n_pre (n_pre + 1) M1).
  { replace (n_pre + 1) with cols by lia. exact PreH28. }
  Exists inv.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z retval (Znth (k * cols + k) l1 0)).
    cancel (store_Z retval_2 inv).
    cancel (store_Z retval_3 0).
    cancel (mpz_array aug_pre (n_pre * cols) l1).
  - split_pures; apply dump_spatial_left; try assumption; try lia; try nia.
Qed. 

Lemma proof_of_rank_mod_gmp_entail_wit_10 : rank_mod_gmp_entail_wit_10.
Proof.
  pre_process.
  assert (HM1kk_pv : M1 k k = Znth (k * cols + k) l1 0).
  { symmetry.
    replace (k * cols + k) with (row_major_index cols k k)
      by (unfold row_major_index; lia).
    apply (rep_matrix_nth l1 n_pre cols M1 k k).
    - replace cols with (n_pre + 1) by lia. exact PreH25.
    - lia.
    - lia. }
  assert (Hp_strict : 1 < zp_low_level_spec) by lia.
  assert (Hrank_scaled :
    rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec
      (matrix_row_scale_mod zp_low_level_spec M1 k zinv_2)).
  { eapply row_scale_preserves_rank_inv_mod;
      [exact Hp_strict | lia | exact PreH27 | exact HM1kk_pv | exact PreH22]. }
  assert (Hprefix_scaled :
    pivot_column_prefix_ready zp_low_level_spec n_pre k 0
      (matrix_row_scale_mod zp_low_level_spec M1 k zinv_2)).
  { eapply row_scale_builds_empty_pivot_prefix;
      [exact Hp_strict | lia | exact HM1kk_pv | exact PreH22]. }
  Exists l2_2 (matrix_row_scale_mod zp_low_level_spec M1 k zinv_2) zinv_2.
  replace (n_pre * cols) with (n_pre * (n_pre + 1)) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z pv (Znth (k * cols + k) l1 0)).
    cancel (store_Z inv zinv_2).
    cancel (store_Z factor 0).
    cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) l2_2).
  - split_pures; apply dump_spatial_left; try assumption; try lia; try nia.
    replace cols with (n_pre + 1) by lia. exact PreH1.
    replace cols with (n_pre + 1) by lia. exact PreH2.
Qed. 

Lemma proof_of_rank_mod_gmp_entail_wit_12 : rank_mod_gmp_entail_wit_12.
Proof.
  unfold rank_mod_gmp_entail_wit_12.
  left.
  intros.
  assert (Hentry_range :
    0 <= Znth (i * cols + k) lcur2 0 < zp_low_level_spec).
  { assert (Hentry_eq : Znth (i * cols + k) lcur2 0 = Mcur i k).
    { replace (i * cols + k) with (row_major_index cols i k)
        by (unfold row_major_index; lia).
      apply (rep_matrix_nth lcur2 n_pre cols Mcur i k PreH30); lia. }
    rewrite Hentry_eq.
    unfold mat_mod in PreH31.
    destruct PreH31 as [_ Hentry].
    apply Hentry; lia. }
  assert (Hrep_aug : rep_matrix lcur2 n_pre (n_pre + 1) Mcur).
  { replace (n_pre + 1) with cols by lia. exact PreH30. }
  assert (Hmat_aug : mat_mod zp_low_level_spec n_pre (n_pre + 1) Mcur).
  { replace (n_pre + 1) with cols by lia. exact PreH31. }
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z pv (Znth (k * cols + k) l1 0)).
    cancel (store_Z inv zinv).
    cancel (store_Z factor (Znth (i * cols + k) lcur2 0)).
    cancel (mpz_array aug_pre (n_pre * cols) lcur2).
  - split_pures; apply dump_spatial_left;
      try exact Hentry_range; try exact Hrep_aug; try exact Hmat_aug;
      try assumption; try lia.
Qed.

Lemma proof_of_rank_mod_gmp_entail_wit_13_1 : rank_mod_gmp_entail_wit_13_1.
Proof.
  pre_process.
  assert (Hfactor_entry : Mcur_2 i k = Znth (i * cols + k) lcur2_2 0).
  { symmetry.
    replace (i * cols + k)
      with (row_major_index (n_pre + 1) i k)
      by (unfold row_major_index; lia).
    apply (rep_matrix_nth lcur2_2 n_pre (n_pre + 1) Mcur_2 i k PreH30); lia. }
  assert (Hrank_next :
    rank_inv_mod zp_low_level_spec n_pre k M0_low_level_spec
      (matrix_row_elim_mod zp_low_level_spec Mcur_2 k i (Znth (i * cols + k) lcur2_2 0))).
  { eapply row_elim_preserves_rank_inv_mod; eauto; lia. }
  assert (Hrep_next_cols :
    rep_matrix l2 n_pre cols
      (matrix_row_elim_mod zp_low_level_spec Mcur_2 k i (Znth (i * cols + k) lcur2_2 0))).
  { replace cols with (n_pre + 1) by lia.
    replace (i * (n_pre + 1) + k) with (i * cols + k) by lia.
    exact PreH1. }
  assert (Hmat_next_cols :
    mat_mod zp_low_level_spec n_pre cols
      (matrix_row_elim_mod zp_low_level_spec Mcur_2 k i (Znth (i * cols + k) lcur2_2 0))).
  { replace cols with (n_pre + 1) by lia.
    replace (i * (n_pre + 1) + k) with (i * cols + k) by lia.
    exact PreH2. }
  assert (Hprefix_next :
    pivot_column_prefix_ready zp_low_level_spec n_pre k (i + 1)
      (matrix_row_elim_mod zp_low_level_spec Mcur_2 k i (Znth (i * cols + k) lcur2_2 0))).
  { eapply row_elim_extends_pivot_prefix; eauto; lia. }
  destruct (Z_lt_ge_dec (i + 1) n_pre) as [Hnext_lt | Hnext_done].
  - Right.
    Exists (Znth (i * cols + k) lcur2_2 0)
      l2 (matrix_row_elim_mod zp_low_level_spec Mcur_2 k i (Znth (i * cols + k) lcur2_2 0)).
    replace (n_pre * cols) with (n_pre * (n_pre + 1)) by lia.
    split_pure_spatial.
    + cancel (store_Z p_pre zp_low_level_spec).
      cancel (store_Z pv (Znth (k * cols + k) l1 0)).
      cancel (store_Z inv zinv).
      cancel (store_Z factor (Znth (i * cols + k) lcur2_2 0)).
      cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) l2).
    + split_pures; apply dump_spatial_left; try assumption; try exact Hrep_next_cols;
        try exact Hmat_next_cols; try exact Hrank_next; try exact Hprefix_next; try lia.
      all: try (
        replace cols with (n_pre + 1) by lia;
        assert (Hi_bound : i + 1 <= n_pre - 1) by lia;
        assert (Hk_bound : k <= n_pre - 1) by lia;
        assert (Hmul_bound :
          (i + 1) * (n_pre + 1) <= (n_pre - 1) * (n_pre + 1))
          by (apply Z.mul_le_mono_nonneg_r; lia);
        assert (Hsum_bound :
          (i + 1) * (n_pre + 1) + k <=
          (n_pre - 1) * (n_pre + 1) + (n_pre - 1)) by lia;
        assert (Hstrict_bound :
          (n_pre - 1) * (n_pre + 1) + (n_pre - 1) <
          n_pre * (n_pre + 1))
          by (ring_simplify; lia);
        lia).
      all: try (
        assert (Hmul_le : (i + 1) * cols <= n_pre * cols)
          by (apply Z.mul_le_mono_nonneg_r; lia);
        lia).
  - Left.
    Exists (Znth (i * cols + k) lcur2_2 0)
      l2 (matrix_row_elim_mod zp_low_level_spec Mcur_2 k i (Znth (i * cols + k) lcur2_2 0)).
    replace (n_pre * cols) with (n_pre * (n_pre + 1)) by lia.
    split_pure_spatial.
    + cancel (store_Z p_pre zp_low_level_spec).
      cancel (store_Z pv (Znth (k * cols + k) l1 0)).
      cancel (store_Z inv zinv).
      cancel (store_Z factor (Znth (i * cols + k) lcur2_2 0)).
      cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) l2).
    + split_pures; apply dump_spatial_left; try assumption; try exact Hrep_next_cols;
        try exact Hmat_next_cols; try exact Hrank_next; try exact Hprefix_next; try lia.
      all: try (replace (i + 1) with n_pre by lia; lia).
      all: try (
        replace (i + 1) with n_pre by lia;
        replace cols with (n_pre + 1) by lia;
        assert (Hprod1 : n_pre * (n_pre + 1) <= 256 * (n_pre + 1))
          by (apply Z.mul_le_mono_nonneg_r; lia);
        assert (Hprod2 : 256 * (n_pre + 1) <= 256 * 257)
          by (apply Z.mul_le_mono_nonneg_l; lia);
        assert (Hk_bound : k <= 255) by lia;
        lia).
Qed.

Lemma proof_of_rank_mod_gmp_entail_wit_13_2 : rank_mod_gmp_entail_wit_13_2.
Proof.
  pre_process.
  assert (Hcur_ik_zero : Mcur_2 i k = 0).
  { replace (i * cols + k)
      with (row_major_index (n_pre + 1) i k) in PreH2
      by (unfold row_major_index; lia).
    rewrite (rep_matrix_nth lcur2_2 n_pre (n_pre + 1) Mcur_2 i k PreH28)
      in PreH2 by lia.
    exact PreH2. }
  assert (Hprefix_next : pivot_column_prefix_ready zp_low_level_spec n_pre k (i + 1) Mcur_2).
  { unfold pivot_column_prefix_ready in *.
    destruct PreH31 as [Hp [Hk_range [Hi_range [Hpivot Hprefix0]]]].
    repeat split; try lia.
    intros r Hr Hr_ne.
    assert (r < i \/ r = i) as [Hr_old | Hr_new] by lia;
    [apply Hprefix0; lia | subst r; exact Hcur_ik_zero]. }
  destruct (Z_lt_ge_dec (i + 1) n_pre) as [Hnext_lt | Hnext_done].
  { Right.
    pose proof (row_major_index_bound n_pre cols (i + 1) k
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hnext_index_bound.
    unfold row_major_index in Hnext_index_bound.
    assert (Hnext_row_nonneg : 0 <= (i + 1) * cols).
    { apply Z.mul_nonneg_nonneg; lia. }
    Exists (Znth (i * cols + k) lcur2_2 0) lcur2_2 Mcur_2.
    replace (n_pre * cols) with (n_pre * (n_pre + 1)) by lia.
    split_pure_spatial.
    { cancel (store_Z p_pre zp_low_level_spec).
      cancel (store_Z pv (Znth (k * cols + k) l1 0)).
      cancel (store_Z inv zinv).
      cancel (store_Z factor (Znth (i * cols + k) lcur2_2 0)).
      cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) lcur2_2). }
    + split_pures; apply dump_spatial_left; try assumption; try exact Hprefix_next; try lia;
        try (replace cols with (n_pre + 1) by lia; assumption).
    all: try (rewrite <- PreH9; lia). }
  { Left.
    Exists (Znth (i * cols + k) lcur2_2 0) lcur2_2 Mcur_2.
    replace (n_pre * cols) with (n_pre * (n_pre + 1)) by lia.
    split_pure_spatial.
    { cancel (store_Z p_pre zp_low_level_spec).
      cancel (store_Z pv (Znth (k * cols + k) l1 0)).
      cancel (store_Z inv zinv).
      cancel (store_Z factor (Znth (i * cols + k) lcur2_2 0)).
      cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) lcur2_2). }
    + split_pures; apply dump_spatial_left; try assumption; try exact Hprefix_next; try lia;
        try (replace cols with (n_pre + 1) by lia; assumption).
    all: try (replace (i + 1) with n_pre by lia; lia).
    all: try (
      replace (i + 1) with n_pre by lia;
      replace cols with (n_pre + 1) by lia;
      assert (Hprod1 : n_pre * (n_pre + 1) <= 256 * (n_pre + 1))
        by (apply Z.mul_le_mono_nonneg_r; lia);
      assert (Hprod2 : 256 * (n_pre + 1) <= 256 * 257)
        by (apply Z.mul_le_mono_nonneg_l; lia);
      assert (Hk_bound : k <= 255) by lia;
      lia). }
Qed.

Lemma proof_of_rank_mod_gmp_entail_wit_13_3 : rank_mod_gmp_entail_wit_13_3.
Proof.
  unfold rank_mod_gmp_entail_wit_13_3.
  intros.
  assert (Hprefix_next : pivot_column_prefix_ready zp_low_level_spec n_pre k (i + 1) Mcur_2).
  { unfold pivot_column_prefix_ready in *.
    destruct PreH33 as [Hp [Hk_range [Hi_range [Hpivot Hprefix0]]]].
    repeat split; try lia.
    intros r Hr Hr_ne.
    assert (r < i \/ r = i) as [Hr_old | Hr_new] by lia;
    [apply Hprefix0; lia | subst r; subst i; contradiction]. }
  destruct (Z_lt_ge_dec (i + 1) n_pre) as [Hnext_lt | Hnext_done].
  { Right.
    Exists zfactor_2 lcur2_2 Mcur_2.
    split_pure_spatial.
    { cancel (store_Z p_pre zp_low_level_spec).
      cancel (store_Z pv (Znth (k * cols + k) l1 0)).
      cancel (store_Z inv zinv).
      cancel (store_Z factor zfactor_2).
      cancel (mpz_array aug_pre (n_pre * cols) lcur2_2). }
    { split_pures; apply dump_spatial_left; try assumption; try exact Hprefix_next; try lia; try nia. } }
  { Left.
    Exists zfactor_2 lcur2_2 Mcur_2.
    split_pure_spatial.
    { cancel (store_Z p_pre zp_low_level_spec).
      cancel (store_Z pv (Znth (k * cols + k) l1 0)).
      cancel (store_Z inv zinv).
      cancel (store_Z factor zfactor_2).
      cancel (mpz_array aug_pre (n_pre * cols) lcur2_2). }
    { split_pures; apply dump_spatial_left; try assumption; try exact Hprefix_next; try lia; try nia. } }
Qed.

Lemma proof_of_rank_mod_gmp_entail_wit_14_1 : rank_mod_gmp_entail_wit_14_1.
Proof.
  unfold rank_mod_gmp_entail_wit_14_1.
  left.
  intros.
  assert (Hready : pivot_column_ready zp_low_level_spec n_pre k Mcur).
  { eapply pivot_column_prefix_ready_full_to_ready; eauto; lia. }
  assert (Hrank_next :
    rank_inv_mod zp_low_level_spec n_pre (k + 1) M0_low_level_spec Mcur).
  { unfold rank_inv_mod.
    unfold rank_inv_mod in PreH30.
    destruct PreH30 as [Hmat [Hreach Hrref]].
    split; [exact Hmat |].
    split; [exact Hreach |].
    eapply rref_prefix_extend_with_ready; eauto. }
  Exists zfactor lcur2 Mcur.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z pv (Znth (k * cols + k) l1 0)).
    cancel (store_Z inv zinv).
    cancel (store_Z factor zfactor).
    cancel (mpz_array aug_pre (n_pre * cols) lcur2).
  - split_pures; apply dump_spatial_left; try assumption; try exact Hrank_next; try lia.
Qed. 

Lemma proof_of_rank_mod_gmp_entail_wit_14_2 : rank_mod_gmp_entail_wit_14_2.
Proof.
  unfold rank_mod_gmp_entail_wit_14_2.
  left.
  intros.
  assert (Hready : pivot_column_ready zp_low_level_spec n_pre k Mcur).
  { eapply pivot_column_prefix_ready_full_to_ready; eauto; lia. }
  assert (Hrank_next :
    rank_inv_mod zp_low_level_spec n_pre (k + 1) M0_low_level_spec Mcur).
  { unfold rank_inv_mod.
    unfold rank_inv_mod in PreH31.
    destruct PreH31 as [Hmat [Hreach Hrref]].
    split; [exact Hmat |].
    split; [exact Hreach |].
    eapply rref_prefix_extend_with_ready; eauto. }
  Exists zfactor lcur2 Mcur.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z pv (Znth (k * cols + k) l1 0)).
    cancel (store_Z inv zinv).
    cancel (store_Z factor zfactor).
    cancel (mpz_array aug_pre (n_pre * cols) lcur2).
  - split_pures; apply dump_spatial_left; try assumption; try exact Hrank_next; try lia.
Qed. 

Lemma proof_of_rank_mod_gmp_return_wit_1 : rank_mod_gmp_return_wit_1.
Proof.
  unfold rank_mod_gmp_return_wit_1.
  left.
  intros.
  assert (Hk_eq : k = n_pre) by lia.
  assert (Hrep_aug : rep_matrix lcur n_pre (n_pre + 1) M0).
  { replace (n_pre + 1) with cols by lia. exact PreH18. }
  assert (Hsuccess : rank_mod_success zp_low_level_spec n_pre M0_low_level_spec k M0).
  { unfold rank_mod_success.
    unfold rank_inv_mod in PreH19.
    destruct PreH19 as [Hmat [Hreach Hrref]].
    split; [exact Hmat |].
    split; [exact Hreach |].
    unfold rank_finished_matrix.
    split; [exact Hrref |].
    intros i j Hi Hj. lia. }
  Exists lcur M0.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial; [entailer! |].
  split_pures; apply dump_spatial_left; try assumption; try exact Hrep_aug; try exact Hsuccess; try lia; try nia.
Qed. 

Lemma proof_of_rank_mod_gmp_return_wit_2 : rank_mod_gmp_return_wit_2.
Proof.
  unfold rank_mod_gmp_return_wit_2.
  left.
  intros.
  assert (Hpivot_eq : pivot = n_pre) by lia.
  assert (Hrep_aug : rep_matrix lcur n_pre (n_pre + 1) M0).
  { replace (n_pre + 1) with cols by lia. exact PreH30. }
  assert (Hsuccess : rank_mod_success zp_low_level_spec n_pre M0_low_level_spec k M0).
  { unfold rank_mod_success.
    unfold rank_inv_mod in PreH31.
    destruct PreH31 as [Hmat [Hreach Hrref]].
    unfold search_submatrix_zero_prefix_mod in PreH33.
    destruct PreH33 as [_ [_ [Hrows _]]].
    split; [exact Hmat |].
    split; [exact Hreach |].
    unfold rank_finished_matrix.
    split; [exact Hrref |].
    intros i j Hi Hj.
    apply Hrows; lia. }
  Exists lcur M0.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial; [entailer! |].
  split_pures; apply dump_spatial_left; try assumption; try exact Hrep_aug; try exact Hsuccess; try lia; try nia.
Qed. 

Lemma proof_of_rank_mod_gmp_return_wit_3 : rank_mod_gmp_return_wit_3.
Proof.
  unfold rank_mod_gmp_return_wit_3.
  left.
  intros.
  assert (Hpivot_eq : pivot = n_pre) by lia.
  assert (Hcol_eq : col = n_pre) by lia.
  assert (Hrep_aug : rep_matrix lcur n_pre (n_pre + 1) M0).
  { replace (n_pre + 1) with cols by lia. exact PreH30. }
  assert (Hsuccess : rank_mod_success zp_low_level_spec n_pre M0_low_level_spec k M0).
  { unfold rank_mod_success.
    unfold rank_inv_mod in PreH31.
    destruct PreH31 as [Hmat [Hreach Hrref]].
    unfold search_submatrix_zero_prefix_mod in PreH33.
    destruct PreH33 as [_ [_ [Hrows _]]].
    split; [exact Hmat |].
    split; [exact Hreach |].
    unfold rank_finished_matrix.
    split; [exact Hrref |].
    intros i j Hi Hj.
    apply Hrows; lia. }
  Exists lcur M0.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial; [entailer! |].
  split_pures; apply dump_spatial_left; try assumption; try exact Hrep_aug; try exact Hsuccess; try lia; try nia.
Qed. 

Lemma proof_of_rank_mod_gmp_return_wit_4 : rank_mod_gmp_return_wit_4.
Proof.
  unfold rank_mod_gmp_return_wit_4.
  left.
  intros.
  assert (Hpivot_eq : pivot = n_pre) by lia.
  assert (Hrep_aug : rep_matrix lcur n_pre (n_pre + 1) M0).
  { replace (n_pre + 1) with cols by lia. exact PreH31. }
  assert (Hsuccess : rank_mod_success zp_low_level_spec n_pre M0_low_level_spec k M0).
  { unfold rank_mod_success.
    unfold rank_inv_mod in PreH32.
    destruct PreH32 as [Hmat [Hreach Hrref]].
    unfold search_submatrix_zero_prefix_mod in PreH34.
    destruct PreH34 as [_ [_ [Hrows _]]].
    split; [exact Hmat |].
    split; [exact Hreach |].
    unfold rank_finished_matrix.
    split; [exact Hrref |].
    intros i j Hi Hj.
    apply Hrows; lia. }
  Exists lcur M0.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial; [entailer! |].
  split_pures; apply dump_spatial_left; try assumption; try exact Hrep_aug; try exact Hsuccess; try lia; try nia.
Qed. 

Lemma proof_of_rank_mod_gmp_partial_solve_wit_11_pure : rank_mod_gmp_partial_solve_wit_11_pure.
Proof.
  pre_process.
  assert (Hentry_range : 0 <= Znth (k * cols + k) l1 0 < zp_low_level_spec).
  { assert (Hentry_eq : Znth (k * cols + k) l1 0 = M1 k k).
    { replace (k * cols + k)
        with (row_major_index (n_pre + 1) k k)
        by (unfold row_major_index; lia).
      apply (rep_matrix_nth l1 n_pre (n_pre + 1) M1 k k PreH26); lia. }
    rewrite Hentry_eq.
    unfold mat_mod in PreH27.
    destruct PreH27 as [_ Hentry].
    apply Hentry; lia. }
  split_pures; apply dump_spatial_left; try assumption; try lia.
Qed.
