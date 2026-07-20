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
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import gauss_solve_mod_gmp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import gauss_solve_mod_gmp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope sac.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_1 : gauss_solve_mod_gmp_entail_wit_1.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_1.
  left.
  intros.
  Exists l_low_level_spec M0_low_level_spec.
  entailer!.
  unfold gauss_inv.
  split; [assumption | split].
  - unfold same_solution_set_mod. intros X. tauto.
  - unfold rref_prefix_mod. repeat split; try lia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_2 : gauss_solve_mod_gmp_entail_wit_2.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_2.
  right.
  intros.
  entailer!.
  unfold pivot_search_zero_prefix.
  repeat split; try lia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_3_1 : gauss_solve_mod_gmp_entail_wit_3_1.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_3_1.
  intros.
  match goal with
  | Hrep : rep_matrix lcur n_pre cols ?Mcur,
    Hprefix0 : pivot_search_zero_prefix n_pre k pivot ?Mcur |- _ =>
      assert (Hcur_zero : Mcur pivot k = 0);
      [ replace (pivot * cols + k) with (row_major_index cols pivot k) in PreH2
          by (unfold row_major_index; lia);
        rewrite (rep_matrix_nth lcur n_pre cols Mcur pivot k Hrep) in PreH2
          by lia;
        exact PreH2
      | assert (Hprefix_next : pivot_search_zero_prefix n_pre k (pivot + 1) Mcur);
        [ unfold pivot_search_zero_prefix in *;
          destruct Hprefix0 as [Hz0 [Hz1 [Hz2 Hzprefix]]];
          repeat split; try lia;
          intros r Hr;
          assert (r < pivot \/ r = pivot) as [Hr_old | Hr_eq] by lia;
          [ apply Hzprefix; lia | subst r; exact Hcur_zero ]
        | idtac ] ]
  end.
  destruct (Z_lt_ge_dec (pivot + 1) n_pre) as [Hmore | Hdone].
  - Left.
    split_pure_spatial.
    + cancel (store_Z p_pre zp_low_level_spec).
      cancel (mpz_array aug_pre (n_pre * cols) lcur).
      cancel (mpz_array x_pre n_pre lx_low_level_spec).
    + split_pures; apply dump_spatial_left;
        try exact Hprefix_next; try assumption; try lia; try nia.
  - Right.
    split_pure_spatial.
    + cancel (store_Z p_pre zp_low_level_spec).
      cancel (mpz_array aug_pre (n_pre * cols) lcur).
      cancel (mpz_array x_pre n_pre lx_low_level_spec).
    + split_pures; apply dump_spatial_left;
        try exact Hprefix_next; try assumption; try lia; try nia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_3_2 : gauss_solve_mod_gmp_entail_wit_3_2.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_3_2.
  right.
  intros.
  cancel.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_3_3 : gauss_solve_mod_gmp_entail_wit_3_3.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_3_3.
  right.
  intros.
  cancel.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_4_1 : gauss_solve_mod_gmp_entail_wit_4_1.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_4_1.
  right.
  intros.
  assert (Hrep_cur_ncols : rep_matrix lcur n_pre (n_pre + 1) M0).
  { rewrite <- PreH9. exact PreH34. }
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
  - apply dump_spatial_left. exact Hrep_cur_ncols.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_4_2 : gauss_solve_mod_gmp_entail_wit_4_2.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_4_2.
  right.
  intros.
  assert (Hrep_cur_ncols : rep_matrix lcur n_pre (n_pre + 1) M0).
  { rewrite <- PreH9. exact PreH34. }
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
  - apply dump_spatial_left. exact Hrep_cur_ncols.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_5_1 : gauss_solve_mod_gmp_entail_wit_5_1.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_5_1.
  left.
  intros.
  assert (Hmat_old : mat_mod zp_low_level_spec n_pre (n_pre + 1) M0).
  { unfold gauss_inv in PreH23.
    destruct PreH23 as [Hmat_old [_ _]].
    exact Hmat_old. }
  assert (Hgauss_swap :
    gauss_inv zp_low_level_spec n_pre k M0_low_level_spec
      (matrix_row_swap M0 k pivot)).
  { eapply row_swap_found_pivot_preserves_gauss; eauto; lia. }
  assert (Hrep_l2_cols :
    rep_matrix l2 n_pre cols (matrix_row_swap M0 k pivot)).
  { replace cols with (n_pre + 1) by lia. exact PreH1. }
  assert (Hzswap_eq :
    Znth (k * cols + k) l2 0 = matrix_row_swap M0 k pivot k k).
  { replace (k * cols + k) with (row_major_index cols k k)
      by (unfold row_major_index; lia).
    apply (rep_matrix_nth l2 n_pre cols
      (matrix_row_swap M0 k pivot) k k Hrep_l2_cols); lia. }
  assert (Hmat_old_cols : mat_mod zp_low_level_spec n_pre cols M0).
  { replace cols with (n_pre + 1) by lia. exact Hmat_old. }
  assert (Hrep_cur_cols : rep_matrix lcur n_pre cols M0).
  { replace cols with (n_pre + 1) by lia. exact PreH22. }
  assert (Hswap_pos :
    0 < matrix_row_swap M0 k pivot k k < zp_low_level_spec).
  { eapply (row_swap_found_pivot_nonzero
      lcur n_pre cols zp_low_level_spec k pivot M0);
      try exact PreH6; try exact Hrep_cur_cols; try exact Hmat_old_cols;
      try exact PreH21; lia. }
  assert (Hzswap_pos : 0 < Znth (k * cols + k) l2 0).
  { rewrite Hzswap_eq; lia. }
  assert (Hzswap_lt : Znth (k * cols + k) l2 0 < zp_low_level_spec).
  { rewrite Hzswap_eq; lia. }
  assert (Hmat_swap :
    mat_mod zp_low_level_spec n_pre cols (matrix_row_swap M0 k pivot)).
  { replace cols with (n_pre + 1) by lia.
    unfold gauss_inv in Hgauss_swap.
    destruct Hgauss_swap as [Hmat_swap [_ _]].
    exact Hmat_swap. }
  Exists l2 (matrix_row_swap M0 k pivot).
  replace (n_pre * cols) with (n_pre * (n_pre + 1)) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) l2).
    cancel (mpz_array x_pre n_pre lx_low_level_spec).
  - split_pures; apply dump_spatial_left; try assumption; try lia; try nia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_5_2 : gauss_solve_mod_gmp_entail_wit_5_2.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_5_2.
  left.
  intros.
  destruct (PreH33 PreH3) as [Hpivot_lt Hentry_nz].
  assert (Hmat_cur : mat_mod zp_low_level_spec n_pre cols M0).
  { unfold gauss_inv in PreH35.
    destruct PreH35 as [Hmat_cur [_ _]].
    rewrite PreH9.
    exact Hmat_cur. }
  assert (Hzkk_eq : Znth (k * cols + k) lcur 0 = M0 k k).
  { replace (k * cols + k) with (row_major_index cols k k)
      by (unfold row_major_index; lia).
    apply (rep_matrix_nth lcur n_pre cols M0 k k PreH34); lia. }
  assert (Hzkk_range : 0 <= Znth (k * cols + k) lcur 0 < zp_low_level_spec).
  { rewrite Hzkk_eq.
    unfold mat_mod in Hmat_cur.
    destruct Hmat_cur as [_ Hentry].
    apply Hentry; lia. }
  assert (Hzkk_nz : Znth (k * cols + k) lcur 0 <> 0).
  { replace (k * cols + k) with (pivot * cols + k) by lia.
    exact Hentry_nz. }
  assert (Hzkk_pos : 0 < Znth (k * cols + k) lcur 0) by lia.
  Exists lcur M0.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
    cancel (mpz_array x_pre n_pre lx_low_level_spec).
  - split_pures; apply dump_spatial_left; try assumption; try lia; try nia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_5_3 : gauss_solve_mod_gmp_entail_wit_5_3.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_5_3.
  left.
  intros.
  destruct (PreH33 PreH3) as [Hpivot_lt Hentry_nz].
  assert (Hmat_cur : mat_mod zp_low_level_spec n_pre cols M0).
  { unfold gauss_inv in PreH35.
    destruct PreH35 as [Hmat_cur [_ _]].
    rewrite PreH9.
    exact Hmat_cur. }
  assert (Hzkk_eq : Znth (k * cols + k) lcur 0 = M0 k k).
  { replace (k * cols + k) with (row_major_index cols k k)
      by (unfold row_major_index; lia).
    apply (rep_matrix_nth lcur n_pre cols M0 k k PreH34); lia. }
  assert (Hzkk_range : 0 <= Znth (k * cols + k) lcur 0 < zp_low_level_spec).
  { rewrite Hzkk_eq.
    unfold mat_mod in Hmat_cur.
    destruct Hmat_cur as [_ Hentry].
    apply Hentry; lia. }
  assert (Hzkk_nz : Znth (k * cols + k) lcur 0 <> 0).
  { replace (k * cols + k) with (pivot * cols + k) by lia.
    exact Hentry_nz. }
  assert (Hzkk_pos : 0 < Znth (k * cols + k) lcur 0) by lia.
  Exists lcur M0.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
    cancel (mpz_array x_pre n_pre lx_low_level_spec).
  - split_pures; apply dump_spatial_left; try assumption; try lia; try nia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_6 : gauss_solve_mod_gmp_entail_wit_6.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_6.
  left.
  intros.
  pose proof PreH1 as Hinv_spec.
  unfold mod_inverse_spec in Hinv_spec.
  destruct Hinv_spec as [_ [_ [Hinv_range _]]].
  assert (Hrep_aug : rep_matrix l1 n_pre (n_pre + 1) M1).
  { replace (n_pre + 1) with cols by lia. exact PreH32. }
  assert (Hmat_aug : mat_mod zp_low_level_spec n_pre (n_pre + 1) M1).
  { replace (n_pre + 1) with cols by lia. exact PreH33. }
  Exists inv.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z retval (Znth (k * cols + k) l1 0)).
    cancel (store_Z retval_2 inv).
    cancel (store_Z retval_3 0).
    cancel (mpz_array aug_pre (n_pre * cols) l1).
    cancel (mpz_array x_pre n_pre lx_low_level_spec).
  - split_pures; apply dump_spatial_left; try assumption; try lia; try nia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_7 : gauss_solve_mod_gmp_entail_wit_7.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_7.
  left.
  intros.
  assert (HM1kk_pv : M1 k k = Znth (k * cols + k) l1 0).
  { symmetry.
    replace (k * cols + k) with (row_major_index cols k k)
      by (unfold row_major_index; lia).
    apply (rep_matrix_nth l1 n_pre cols M1 k k).
    - replace cols with (n_pre + 1) by lia. exact PreH27.
    - lia.
    - lia. }
  assert (Hp_strict : 1 < zp_low_level_spec) by lia.
  assert (Hgauss_scaled :
    gauss_inv zp_low_level_spec n_pre k M0_low_level_spec
      (matrix_row_scale_mod zp_low_level_spec M1 k zinv_2)).
  { eapply row_scale_preserves_gauss_inv;
      [exact Hp_strict | lia | exact PreH29 | exact HM1kk_pv | exact PreH26]. }
  assert (Hprefix_scaled :
    pivot_column_prefix_ready zp_low_level_spec n_pre k 0
      (matrix_row_scale_mod zp_low_level_spec M1 k zinv_2)).
  { eapply row_scale_builds_empty_pivot_prefix;
      [exact Hp_strict | lia | exact HM1kk_pv | exact PreH26]. }
  Exists l2_2 (matrix_row_scale_mod zp_low_level_spec M1 k zinv_2) zinv_2.
  replace (n_pre * cols) with (n_pre * (n_pre + 1)) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z pv (Znth (k * cols + k) l1 0)).
    cancel (store_Z inv zinv_2).
    cancel (store_Z factor 0).
    cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) l2_2).
    cancel (mpz_array x_pre n_pre lx_low_level_spec).
  - split_pures; apply dump_spatial_left; try assumption; try lia; try nia.
    + replace cols with (n_pre + 1) by lia. exact PreH1.
    + replace cols with (n_pre + 1) by lia. exact PreH2.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_8 : gauss_solve_mod_gmp_entail_wit_8.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_8.
  left.
  intros.
  Exists 0 l2 M2.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z pv (Znth (k * cols + k) l1 0)).
    cancel (store_Z inv zinv).
    cancel (store_Z factor 0).
    cancel (mpz_array aug_pre (n_pre * cols) l2).
    cancel (mpz_array x_pre n_pre lx_low_level_spec).
  - split_pures; apply dump_spatial_left; try assumption; try lia; try nia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_9 : gauss_solve_mod_gmp_entail_wit_9.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_9.
  left.
  intros.
  assert (Hentry_range :
            0 <= Znth (i * cols + k) lcur2 0 < zp_low_level_spec).
  { assert (Hzik_eq : Znth (i * cols + k) lcur2 0 = Mcur i k).
    { replace (i * cols + k) with (row_major_index cols i k)
        by (unfold row_major_index; lia).
      apply (rep_matrix_nth lcur2 n_pre cols Mcur i k PreH35); lia. }
    rewrite Hzik_eq.
    unfold mat_mod in PreH36.
    destruct PreH36 as [_ Hentry].
    apply Hentry; lia. }
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z pv (Znth (k * cols + k) l1 0)).
    cancel (store_Z inv zinv).
    cancel (store_Z factor (Znth (i * cols + k) lcur2 0)).
    cancel (mpz_array aug_pre (n_pre * cols) lcur2).
    cancel (mpz_array x_pre n_pre lx_low_level_spec).
  - split_pures; apply dump_spatial_left;
      try assumption; try lia.
    + replace (n_pre + 1) with cols by lia. exact PreH35.
    + replace (n_pre + 1) with cols by lia. exact PreH36.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_10_1 : gauss_solve_mod_gmp_entail_wit_10_1.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_10_1.
  intros.
  assert (Hrep_cur_ncols : rep_matrix lcur2 n_pre (n_pre + 1) Mcur).
  { exact PreH32. }
  assert (Hfactor_entry : Mcur i k = Znth (i * cols + k) lcur2 0) by
    (symmetry;
     replace (i * cols + k)
       with (row_major_index (n_pre + 1) i k)
       by (unfold row_major_index; lia);
     apply (rep_matrix_nth lcur2 n_pre (n_pre + 1) Mcur i k Hrep_cur_ncols);
     lia).
  assert (Hgauss_next :
    gauss_inv zp_low_level_spec n_pre k M0_low_level_spec
      (matrix_row_elim_mod zp_low_level_spec Mcur k i
         (Znth (i * cols + k) lcur2 0))).
  { eapply row_elim_preserves_gauss_inv.
    - lia.
    - lia.
    - exact PreH29.
    - exact PreH34. }
  assert (Hrep_next_cols :
    rep_matrix l2 n_pre cols
      (matrix_row_elim_mod zp_low_level_spec Mcur k i
         (Znth (i * cols + k) lcur2 0))).
  { replace cols with (n_pre + 1) at 1 by lia. exact PreH1. }
  assert (Hmat_next_cols :
    mat_mod zp_low_level_spec n_pre cols
      (matrix_row_elim_mod zp_low_level_spec Mcur k i
         (Znth (i * cols + k) lcur2 0))).
  { replace cols with (n_pre + 1) at 1 by lia. exact PreH2. }
  assert (Hprefix_next :
    pivot_column_prefix_ready zp_low_level_spec n_pre k (i + 1)
      (matrix_row_elim_mod zp_low_level_spec Mcur k i
         (Znth (i * cols + k) lcur2 0))).
  { eapply row_elim_extends_pivot_prefix.
    - exact PreH35.
    - lia.
    - exact PreH29.
    - exact Hfactor_entry. }
  destruct (Z_lt_ge_dec (i + 1) n_pre) as [Hnext_lt | Hnext_ge].
  - Right.
    Exists (Znth (i * cols + k) lcur2 0) l2
      (matrix_row_elim_mod zp_low_level_spec Mcur k i
         (Znth (i * cols + k) lcur2 0)).
    replace (n_pre * cols) with (n_pre * (n_pre + 1)) by lia.
    split_pure_spatial.
    + cancel (store_Z p_pre zp_low_level_spec).
      cancel (store_Z pv (Znth (k * cols + k) l1 0)).
      cancel (store_Z inv zinv).
      cancel (store_Z factor (Znth (i * cols + k) lcur2 0)).
      cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) l2).
      cancel (mpz_array x_pre n_pre lx_low_level_spec).
    + pose proof (row_major_index_bound n_pre cols (i + 1) k
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hnext_index.
      unfold row_major_index in Hnext_index.
      assert (Hnext_idx_nonneg : 0 <= (i + 1) * cols + k) by lia.
      assert (Hnext_idx_lt : (i + 1) * cols + k < n_pre * (n_pre + 1)).
      { replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
        lia. }
      assert (Hnext_row_min : -2147483648 <= (i + 1) * cols) by lia.
      assert (Hnext_row_max : (i + 1) * cols <= 2147483647) by lia.
      assert (Hnext_idx_min : -2147483648 <= (i + 1) * cols + k) by lia.
      assert (Hnext_idx_max : (i + 1) * cols + k <= 2147483647) by lia.
      split_pures; apply dump_spatial_left;
        try exact Hrep_next_cols; try exact Hmat_next_cols;
        try exact Hgauss_next; try exact Hprefix_next;
        try exact Hnext_idx_nonneg; try exact Hnext_idx_lt;
        try exact Hnext_row_min; try exact Hnext_row_max;
        try exact Hnext_idx_min; try exact Hnext_idx_max;
        try assumption; lia. (*
        try solve [apply dump_spatial_left; exact Hrep_next_cols];
        try solve [apply dump_spatial_left; exact Hmat_next_cols];
        try solve [apply dump_spatial_left; exact Hgauss_next];
        try solve [apply dump_spatial_left; exact Hprefix_next];
        try solve [apply dump_spatial_left; assumption];
        try solve [apply dump_spatial_left; lia];
        try solve [apply dump_spatial_left; nia]).
      all: try match goal with
      | |- _ |-- “ _ ” =>
          apply dump_spatial_left;
          try assumption; try exact Hgauss_next; try exact Hprefix_next; try lia
      end.
      all: try nia. *)
  - Left.
    Exists (Znth (i * cols + k) lcur2 0) l2
      (matrix_row_elim_mod zp_low_level_spec Mcur k i
         (Znth (i * cols + k) lcur2 0)).
    replace (n_pre * cols) with (n_pre * (n_pre + 1)) by lia.
    split_pure_spatial.
    + cancel (store_Z p_pre zp_low_level_spec).
      cancel (store_Z pv (Znth (k * cols + k) l1 0)).
      cancel (store_Z inv zinv).
      cancel (store_Z factor (Znth (i * cols + k) lcur2 0)).
      cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) l2).
      cancel (mpz_array x_pre n_pre lx_low_level_spec).
    + assert (Hnext_done_eq : i + 1 = n_pre) by lia.
      assert (Hnext_row_min : -2147483648 <= (i + 1) * cols) by lia.
      assert (Hnext_row_max : (i + 1) * cols <= 2147483647).
      { replace (i + 1) with n_pre by lia.
        replace cols with (n_pre + 1) by lia.
        exact PreH19. }
      assert (Hnext_idx_min : -2147483648 <= (i + 1) * cols + k) by lia.
      assert (Hnext_idx_max : (i + 1) * cols + k <= 2147483647).
      { replace (i + 1) with n_pre by lia.
        replace cols with (n_pre + 1) by lia.
        assert (Hprod1 : n_pre * (n_pre + 1) <= 256 * (n_pre + 1)).
        { apply Z.mul_le_mono_nonneg_r; lia. }
        assert (Hprod2 : 256 * (n_pre + 1) <= 256 * 257).
        { apply Z.mul_le_mono_nonneg_l; lia. }
        assert (Hk_bound : k <= 255) by lia.
        lia. }
      split_pures; apply dump_spatial_left;
        try exact Hrep_next_cols; try exact Hmat_next_cols;
        try exact Hgauss_next; try exact Hprefix_next;
        try exact Hnext_done_eq;
        try exact Hnext_row_min; try exact Hnext_row_max;
        try exact Hnext_idx_min; try exact Hnext_idx_max;
        try assumption; lia. (*
      all: try match goal with
      | |- _ |-- “ _ ” =>
          apply dump_spatial_left;
          try assumption; try exact Hgauss_next; try exact Hprefix_next; try lia
      end.
      all: try nia. *)
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_10_2 : gauss_solve_mod_gmp_entail_wit_10_2.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_10_2.
  intros.
  assert (Hcur_ik_zero : Mcur i k = 0).
  { replace (i * cols + k)
      with (row_major_index (n_pre + 1) i k) in PreH2
      by (unfold row_major_index; lia).
    rewrite (rep_matrix_nth lcur2 n_pre (n_pre + 1) Mcur i k PreH30) in PreH2
      by lia.
    lia. }
  assert (Hprefix_next :
            pivot_column_prefix_ready zp_low_level_spec n_pre k (i + 1) Mcur).
  { unfold pivot_column_prefix_ready in *.
    destruct PreH33 as [Hp [Hk_range [Hi_range [Hpivot Hprefix]]]].
    repeat split; try lia.
    intros r Hr Hr_ne.
    assert (r < i \/ r = i) as [Hr_old | Hr_new] by lia.
    - apply Hprefix; lia.
    - subst r. exact Hcur_ik_zero. }
  destruct (Z_lt_ge_dec (i + 1) n_pre) as [Hnext_lt | Hnext_ge].
  - Right.
    Exists (Znth (i * cols + k) lcur2 0) lcur2 Mcur.
    replace (n_pre * cols) with (n_pre * (n_pre + 1)) by lia.
    split_pure_spatial.
    + cancel (store_Z p_pre zp_low_level_spec).
      cancel (store_Z pv (Znth (k * cols + k) l1 0)).
      cancel (store_Z inv zinv).
      cancel (store_Z factor (Znth (i * cols + k) lcur2 0)).
      cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) lcur2).
      cancel (mpz_array x_pre n_pre lx_low_level_spec).
    + split_pures.
      all: try match goal with
      | |- _ |-- “ _ ” =>
          apply dump_spatial_left;
          try assumption; try exact Hprefix_next; try lia
      end.
      all: try (replace cols with (n_pre + 1) by lia; assumption).
      all: try nia.
  - Left.
    Exists (Znth (i * cols + k) lcur2 0) lcur2 Mcur.
    replace (n_pre * cols) with (n_pre * (n_pre + 1)) by lia.
    split_pure_spatial.
    + cancel (store_Z p_pre zp_low_level_spec).
      cancel (store_Z pv (Znth (k * cols + k) l1 0)).
      cancel (store_Z inv zinv).
      cancel (store_Z factor (Znth (i * cols + k) lcur2 0)).
      cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) lcur2).
      cancel (mpz_array x_pre n_pre lx_low_level_spec).
    + split_pures.
      all: try match goal with
      | |- _ |-- “ _ ” =>
          apply dump_spatial_left;
          try assumption; try exact Hprefix_next; try lia
      end.
      all: try (replace cols with (n_pre + 1) by lia; assumption).
      * replace (i + 1) with n_pre by lia. lia.
      * replace (i + 1) with n_pre by lia.
        replace cols with (n_pre + 1) by lia.
        assert (Hprod1 : n_pre * (n_pre + 1) <= 256 * (n_pre + 1)).
        { apply Z.mul_le_mono_nonneg_r; lia. }
        assert (Hprod2 : 256 * (n_pre + 1) <= 256 * 257).
        { apply Z.mul_le_mono_nonneg_l; lia. }
        assert (Hk_bound : k <= 255) by lia.
        lia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_10_3 : gauss_solve_mod_gmp_entail_wit_10_3.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_10_3.
  intros.
  subst i.
  assert (Hprefix_next :
    pivot_column_prefix_ready zp_low_level_spec n_pre k (k + 1) Mcur).
  { unfold pivot_column_prefix_ready in *.
    destruct PreH38 as [Hp [Hk_range [Hi_range [Hpivot Hprefix]]]].
    repeat split; try lia.
    intros r Hr Hr_ne.
    apply Hprefix; lia. }
  destruct (Z_lt_ge_dec (k + 1) n_pre) as [Hnext_lt | Hnext_done].
  - Right.
    Exists zfactor lcur2 Mcur.
    split_pure_spatial.
    + cancel (store_Z p_pre zp_low_level_spec).
      cancel (store_Z pv (Znth (k * cols + k) l1 0)).
      cancel (store_Z inv zinv).
      cancel (store_Z factor zfactor).
      cancel (mpz_array aug_pre (n_pre * cols) lcur2).
      cancel (mpz_array x_pre n_pre lx_low_level_spec).
    + pose proof (row_major_index_bound n_pre cols (k + 1) k
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hnext_index.
      unfold row_major_index in Hnext_index.
      assert (Hnext_idx_nonneg : 0 <= (k + 1) * cols + k) by lia.
      assert (Hnext_idx_lt : (k + 1) * cols + k < n_pre * cols) by lia.
      assert (Hnext_row_min : -2147483648 <= (k + 1) * cols) by lia.
      assert (Hnext_row_max : (k + 1) * cols <= 2147483647) by lia.
      assert (Hnext_idx_min : -2147483648 <= (k + 1) * cols + k) by lia.
      assert (Hnext_idx_max : (k + 1) * cols + k <= 2147483647) by lia.
      split_pures; apply dump_spatial_left;
        try exact PreH35; try exact PreH36; try exact PreH37;
        try exact Hprefix_next; try exact Hnext_idx_nonneg;
        try exact Hnext_idx_lt; try exact Hnext_row_min;
        try exact Hnext_row_max; try exact Hnext_idx_min;
        try exact Hnext_idx_max; try assumption; lia.
  - Left.
    Exists zfactor lcur2 Mcur.
    split_pure_spatial.
    + cancel (store_Z p_pre zp_low_level_spec).
      cancel (store_Z pv (Znth (k * cols + k) l1 0)).
      cancel (store_Z inv zinv).
      cancel (store_Z factor zfactor).
      cancel (mpz_array aug_pre (n_pre * cols) lcur2).
      cancel (mpz_array x_pre n_pre lx_low_level_spec).
    + assert (Hnext_done_eq : k + 1 = n_pre) by lia.
      assert (Hnext_row_min : -2147483648 <= (k + 1) * cols) by lia.
      assert (Hnext_row_max : (k + 1) * cols <= 2147483647).
      { replace (k + 1) with n_pre by lia. exact PreH17. }
      assert (Hnext_idx_min : -2147483648 <= (k + 1) * cols + k) by lia.
      assert (Hnext_idx_max : (k + 1) * cols + k <= 2147483647).
      { replace (k + 1) with n_pre by lia.
        replace cols with (n_pre + 1) by lia.
        assert (Hprod1 : n_pre * (n_pre + 1) <= 256 * (n_pre + 1)).
        { apply Z.mul_le_mono_nonneg_r; lia. }
        assert (Hprod2 : 256 * (n_pre + 1) <= 256 * 257).
        { apply Z.mul_le_mono_nonneg_l; lia. }
        assert (Hk_bound : k <= 255) by lia.
        lia. }
      split_pures; apply dump_spatial_left;
        try exact PreH35; try exact PreH36; try exact PreH37;
        try exact Hprefix_next; try exact Hnext_done_eq;
        try exact Hnext_row_min; try exact Hnext_row_max;
        try exact Hnext_idx_min; try exact Hnext_idx_max;
        try assumption; lia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_12_1 : gauss_solve_mod_gmp_entail_wit_12_1.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_12_1.
  left.
  intros.
  assert (Hready : pivot_column_ready zp_low_level_spec n_pre k Mcur).
  { eapply pivot_column_prefix_ready_full_to_ready.
    - exact PreH36.
    - lia. }
  assert (Hrref_next : rref_prefix_mod zp_low_level_spec n_pre (k + 1) Mcur).
  { unfold gauss_inv in PreH35.
    destruct PreH35 as [_ [_ Hrref]].
    eapply rref_prefix_extend_with_ready.
    - exact Hrref.
    - exact Hready. }
  Exists zfactor lcur2 Mcur.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z pv (Znth (k * cols + k) l1 0)).
    cancel (store_Z inv zinv).
    cancel (store_Z factor zfactor).
    cancel (mpz_array aug_pre (n_pre * cols) lcur2).
    cancel (mpz_array x_pre n_pre lx_low_level_spec).
  - split_pures; dump_pre_spatial;
      try assumption;
      try exact Hready;
      try exact Hrref_next;
      try lia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_12_2 : gauss_solve_mod_gmp_entail_wit_12_2.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_12_2.
  left.
  intros.
  assert (Hready : pivot_column_ready zp_low_level_spec n_pre k Mcur).
  { eapply pivot_column_prefix_ready_full_to_ready.
    - exact PreH37.
    - lia. }
  assert (Hrref_next : rref_prefix_mod zp_low_level_spec n_pre (k + 1) Mcur).
  { unfold gauss_inv in PreH36.
    destruct PreH36 as [_ [_ Hrref]].
    eapply rref_prefix_extend_with_ready.
    - exact Hrref.
    - exact Hready. }
  Exists zfactor lcur2 Mcur.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (store_Z pv (Znth (k * cols + k) l1 0)).
    cancel (store_Z inv zinv).
    cancel (store_Z factor zfactor).
    cancel (mpz_array aug_pre (n_pre * cols) lcur2).
    cancel (mpz_array x_pre n_pre lx_low_level_spec).
  - split_pures; dump_pre_spatial;
      try assumption;
      try exact Hready;
      try exact Hrref_next;
      try lia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_13 : gauss_solve_mod_gmp_entail_wit_13.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_13.
  left.
  intros.
  assert (Hgauss_next :
            gauss_inv zp_low_level_spec n_pre (k + 1)
              M0_low_level_spec Mdone).
  { unfold gauss_inv in PreH27.
    destruct PreH27 as [Hmat [Hsame _]].
    unfold gauss_inv.
    split; [exact Hmat | split; [exact Hsame | exact PreH29]]. }
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) ldone).
    cancel (mpz_array x_pre n_pre lx_low_level_spec).
  - split_pures; dump_pre_spatial;
      try assumption;
      try exact Hgauss_next;
      try lia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_15 : gauss_solve_mod_gmp_entail_wit_15.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_15.
  left.
  intros.
  assert (Hk_eq : k = n_pre) by lia.
  subst k.
  assert (Hfinished : gauss_finished_matrix zp_low_level_spec n_pre M0) by
    (unfold gauss_finished_matrix;
     unfold gauss_inv in PreH22;
     tauto).
  Exists lcur M0.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
    cancel (mpz_array x_pre n_pre lx_low_level_spec).
  - split_pures; dump_pre_spatial;
      try assumption;
      try exact Hfinished;
      try lia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_16 : gauss_solve_mod_gmp_entail_wit_16.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_16.
  intros.
  assert (Hrhs_empty : rhs_copy_prefix lx_low_level_spec n_pre 0 Mfin) by
    (unfold rhs_copy_prefix; repeat split; try lia).
  destruct (Z_lt_ge_dec 0 n_pre) as [Hn_pos | Hn_done].
  - Right.
    Exists lx_low_level_spec.
    split_pure_spatial.
    + cancel (store_Z p_pre zp_low_level_spec).
      cancel (mpz_array aug_pre (n_pre * cols) lfin).
      cancel (mpz_array x_pre n_pre lx_low_level_spec).
    + split_pures; dump_pre_spatial;
        try assumption;
        try exact Hrhs_empty;
        try lia;
        try nia.
  - Left.
    Exists lx_low_level_spec.
    split_pure_spatial.
    + cancel (store_Z p_pre zp_low_level_spec).
      cancel (mpz_array aug_pre (n_pre * cols) lfin).
      cancel (mpz_array x_pre n_pre lx_low_level_spec).
    + split_pures; dump_pre_spatial;
        try assumption;
        try exact Hrhs_empty;
        try lia;
        try nia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_entail_wit_17 : gauss_solve_mod_gmp_entail_wit_17.
Proof.
  unfold gauss_solve_mod_gmp_entail_wit_17.
  intros.
  assert (Hrhs_next :
    rhs_copy_prefix
      (replace_Znth i (Znth (i * cols + n_pre) lfin 0) lxcur_2)
      n_pre (i + 1) Mfin)
    by (eapply rhs_copy_prefix_update_from_matrix; eauto; lia).
  destruct (Z_lt_ge_dec (i + 1) n_pre) as [Hnext_lt | Hnext_done].
  - Right.
    Exists (replace_Znth i (Znth (i * cols + n_pre) lfin 0) lxcur_2).
    split_pure_spatial.
    + cancel (store_Z p_pre zp_low_level_spec).
      cancel (mpz_array aug_pre (n_pre * cols) lfin).
      cancel (mpz_array x_pre n_pre
        (replace_Znth i (Znth (i * cols + n_pre) lfin 0) lxcur_2)).
    + split_pures; dump_pre_spatial;
        try assumption;
        try exact Hrhs_next;
        try lia;
        try nia.
  - Left.
    Exists (replace_Znth i (Znth (i * cols + n_pre) lfin 0) lxcur_2).
    split_pure_spatial.
    + cancel (store_Z p_pre zp_low_level_spec).
      cancel (mpz_array aug_pre (n_pre * cols) lfin).
      cancel (mpz_array x_pre n_pre
        (replace_Znth i (Znth (i * cols + n_pre) lfin 0) lxcur_2)).
    + split_pures; dump_pre_spatial;
        try assumption;
        try exact Hrhs_next;
        try lia;
        try nia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_return_wit_1 : gauss_solve_mod_gmp_return_wit_1.
Proof.
  unfold gauss_solve_mod_gmp_return_wit_1.
  left.
  intros.
  assert (Hrep_fin_aug : rep_matrix lfin n_pre (n_pre + 1) Mfin).
  { replace (n_pre + 1) with cols by lia. assumption. }
  pose (X := vector_from_aug_rhs Mfin n_pre).
  assert (Hsuccess :
    rep_vector lxcur n_pre X /\
    gauss_success zp_low_level_spec n_pre M0_low_level_spec X).
  { subst X.
    eapply gauss_finished_success_from_rhs_copy; eauto; lia. }
  destruct Hsuccess as [Hrep_vec Hgauss_success].
  Exists X lxcur lfin Mfin.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lfin).
    cancel (mpz_array x_pre n_pre lxcur).
  - split_pures; dump_pre_spatial;
      try assumption;
      try exact Hrep_fin_aug;
      try exact Hrep_vec;
      try exact Hgauss_success;
      try lia;
      try nia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_return_wit_2 : gauss_solve_mod_gmp_return_wit_2.
Proof.
  unfold gauss_solve_mod_gmp_return_wit_2.
  left.
  intros.
  assert (Hrep_fin_aug : rep_matrix lfin n_pre (n_pre + 1) Mfin).
  { replace (n_pre + 1) with cols by lia. assumption. }
  pose (X := vector_from_aug_rhs Mfin n_pre).
  assert (Hsuccess :
    rep_vector lxcur n_pre X /\
    gauss_success zp_low_level_spec n_pre M0_low_level_spec X).
  { subst X.
    eapply gauss_finished_success_from_rhs_copy; eauto; lia. }
  destruct Hsuccess as [Hrep_vec Hgauss_success].
  Exists X lxcur lfin Mfin.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lfin).
    cancel (mpz_array x_pre n_pre lxcur).
  - split_pures; dump_pre_spatial;
      try assumption;
      try exact Hrep_fin_aug;
      try exact Hrep_vec;
      try exact Hgauss_success;
      try lia;
      try nia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_return_wit_3 : gauss_solve_mod_gmp_return_wit_3.
Proof.
  unfold gauss_solve_mod_gmp_return_wit_3.
  left.
  intros.
  assert (Hrep_cur_aug : rep_matrix lcur n_pre (n_pre + 1) M0).
  { replace (n_pre + 1) with cols by lia. assumption. }
  Exists lx_low_level_spec lcur M0.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
    cancel (mpz_array x_pre n_pre lx_low_level_spec).
  - split_pures; dump_pre_spatial;
      try assumption;
      try exact Hrep_cur_aug;
      try lia;
      try nia.
Qed.

Lemma proof_of_gauss_solve_mod_gmp_return_wit_4 : gauss_solve_mod_gmp_return_wit_4.
Proof.
  unfold gauss_solve_mod_gmp_return_wit_4.
  left.
  intros.
  assert (Hrep_cur_aug : rep_matrix lcur n_pre (n_pre + 1) M0).
  { replace (n_pre + 1) with cols by lia. assumption. }
  Exists lx_low_level_spec lcur M0.
  replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) lcur).
    cancel (mpz_array x_pre n_pre lx_low_level_spec).
  - split_pures; dump_pre_spatial;
      try assumption;
      try exact Hrep_cur_aug;
      try lia;
      try nia.
Qed.
