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
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import build_aug_basis_gmp_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import build_aug_basis_gmp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope sac.

Lemma proof_of_build_aug_basis_gmp_entail_wit_1 : build_aug_basis_gmp_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  prop_apply (mpz_array_Zlength aug_pre (n_pre * (n_pre + 1)) laug_low_level_spec).
  Intros_p Hlen.
  Exists laug_low_level_spec.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * (n_pre + 1)) laug_low_level_spec).
  - repeat split_pures; try solve
      [ dump_pre_spatial; int_auto
      | dump_pre_spatial; nia
      | dump_pre_spatial; apply partial_rep_matrix_0_from_length;
          [unfold matrix_shape; lia | exact Hlen] ].
Qed.

Lemma proof_of_build_aug_basis_gmp_entail_wit_2 : build_aug_basis_gmp_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Exists laug_cur_2.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) laug_cur_2).
  - repeat split_pures; try solve [dump_pre_spatial; int_auto | dump_pre_spatial; nia].
Qed.

Lemma proof_of_build_aug_basis_gmp_entail_wit_3_1 : build_aug_basis_gmp_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  set (l_next := replace_Znth idx 1 laug_cur_2).
  assert (Hpart_next :
    partial_rep_matrix l_next n_pre cols (idx + 1)
      (matrix_aug_basis n_pre A_low_level_spec col_pre)).
  { subst l_next.
    eapply (partial_rep_matrix_update_next
      laug_cur_2 n_pre cols idx
      (matrix_aug_basis n_pre A_low_level_spec col_pre) i j 1).
    - exact PreH34.
    - lia.
    - lia.
    - unfold row_major_index; lia.
    - unfold matrix_aug_basis, matrix_aug_with_vector, basis_vector.
      subst i j.
      destruct Z.eq_dec; try lia.
      destruct Z.eq_dec; lia. }
  Left. Right.
  Exists l_next.
  subst l_next.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) (replace_Znth idx 1 laug_cur_2)).
  - split_pures; try exact Hpart_next; try lia;
      dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_build_aug_basis_gmp_entail_wit_3_2 : build_aug_basis_gmp_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  set (l_next := replace_Znth idx 1 laug_cur_2).
  assert (Hpart_next :
    partial_rep_matrix l_next n_pre cols (idx + 1)
      (matrix_aug_basis n_pre A_low_level_spec col_pre)).
  { subst l_next.
    eapply (partial_rep_matrix_update_next
      laug_cur_2 n_pre cols idx
      (matrix_aug_basis n_pre A_low_level_spec col_pre) i j 1).
    - exact PreH35.
    - split; assumption.
    - split; [assumption | subst j; rewrite PreH8; lia].
    - unfold row_major_index; exact PreH23.
    - unfold matrix_aug_basis, matrix_aug_with_vector, basis_vector.
      subst i j.
      destruct (Z.eq_dec n_pre n_pre) as [_ | Hneq]; [| contradiction].
      destruct (Z.eq_dec col_pre col_pre) as [_ | Hneq]; [reflexivity | contradiction]. }
  Left. Right.
  Exists l_next.
  subst l_next.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) (replace_Znth idx 1 laug_cur_2)).
  - split_pures; try exact Hpart_next; try lia;
      dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_build_aug_basis_gmp_entail_wit_3_3 : build_aug_basis_gmp_entail_wit_3_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  set (l_next := replace_Znth idx 0 laug_cur_2).
  assert (Hpart_next :
    partial_rep_matrix l_next n_pre cols (idx + 1)
      (matrix_aug_basis n_pre A_low_level_spec col_pre)).
  { subst l_next.
    eapply (partial_rep_matrix_update_next
      laug_cur_2 n_pre cols idx
      (matrix_aug_basis n_pre A_low_level_spec col_pre) i j 0).
    - exact PreH34.
    - split; assumption.
    - split; [assumption | subst j; rewrite PreH8; lia].
    - unfold row_major_index; exact PreH23.
    - unfold matrix_aug_basis, matrix_aug_with_vector, basis_vector.
      subst j.
      destruct (Z.eq_dec n_pre n_pre) as [_ | Hneq]; [| contradiction].
      destruct (Z.eq_dec i col_pre) as [Heq | Hneq]; [contradiction | reflexivity]. }
  Left. Right.
  Exists l_next.
  subst l_next.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) (replace_Znth idx 0 laug_cur_2)).
  - split_pures; try exact Hpart_next; try lia;
      dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_build_aug_basis_gmp_entail_wit_3_4 : build_aug_basis_gmp_entail_wit_3_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  Left. Right.
  set (l_next := replace_Znth idx 0 laug_cur_2).
  assert (Hpart_next :
    partial_rep_matrix l_next n_pre cols (idx + 1)
      (matrix_aug_basis n_pre A_low_level_spec col_pre)).
  { subst l_next.
    eapply (partial_rep_matrix_update_next
      laug_cur_2 n_pre cols idx
      (matrix_aug_basis n_pre A_low_level_spec col_pre) i j 0).
    - exact PreH35.
    - split; assumption.
    - split; [assumption | subst j; rewrite PreH8; lia].
    - unfold row_major_index; exact PreH23.
    - unfold matrix_aug_basis, matrix_aug_with_vector, basis_vector.
      subst j.
      destruct (Z.eq_dec n_pre n_pre) as [_ | Hneq]; [| contradiction].
      destruct (Z.eq_dec i col_pre) as [Heq | Hneq]; [contradiction | reflexivity]. }
  Exists l_next.
  subst l_next.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) (replace_Znth idx 0 laug_cur_2)).
  - split_pures; try exact Hpart_next; try lia;
      dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_build_aug_basis_gmp_entail_wit_3_5 : build_aug_basis_gmp_entail_wit_3_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  set (v := Znth (i * n_pre + j) la_low_level_spec 0).
  assert (Hj_lt_n : j < n_pre) by lia.
  assert (Hval : v = matrix_aug_basis n_pre A_low_level_spec col_pre i j).
  { subst v.
    replace (i * n_pre + j) with (row_major_index n_pre i j)
      by (unfold row_major_index; lia).
    rewrite (rep_matrix_nth la_low_level_spec n_pre n_pre
      A_low_level_spec i j PreH32); try lia.
    unfold matrix_aug_basis, matrix_aug_with_vector.
    destruct (Z.eq_dec j n_pre) as [Heq | Hneq]; [contradiction | reflexivity]. }
  set (l_next := replace_Znth idx v laug_cur_2).
  assert (Hpart_next :
    partial_rep_matrix l_next n_pre cols (idx + 1)
      (matrix_aug_basis n_pre A_low_level_spec col_pre)).
  { subst l_next.
    eapply (partial_rep_matrix_update_next
      laug_cur_2 n_pre cols idx
      (matrix_aug_basis n_pre A_low_level_spec col_pre) i j v).
    - exact PreH34.
    - split; assumption.
    - split; assumption.
    - unfold row_major_index; exact PreH22.
    - exact Hval. }
  subst v.
  destruct (Z_lt_dec (j + 1) n_pre) as [Hj_next_lt | Hj_next_ge].
  - Right.
    assert (Hsrc_next_bounds : 0 <= i * n_pre + (j + 1) < n_pre * n_pre).
    { split.
      - lia.
      - assert (Hle : (i + 1) * n_pre <= n_pre * n_pre).
        { apply Z.mul_le_mono_nonneg_r; lia. }
        replace ((i + 1) * n_pre) with (i * n_pre + n_pre) in Hle by ring.
        assert (i * n_pre + (j + 1) < i * n_pre + n_pre) by lia.
        lia. }
    Exists l_next.
    subst l_next.
    split_pure_spatial.
    + cancel (mpz_array aug_pre (n_pre * cols)
        (replace_Znth idx (Znth (i * n_pre + j) la_low_level_spec 0) laug_cur_2)).
      cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
      cancel (store_Z p_pre zp_low_level_spec).
    + split_pures; try exact Hpart_next; try lia;
        dump_pre_spatial; try assumption; try lia.
  - Left.
    Exists l_next.
    subst l_next.
    split_pure_spatial.
    + cancel (mpz_array aug_pre (n_pre * cols)
        (replace_Znth idx (Znth (i * n_pre + j) la_low_level_spec 0) laug_cur_2)).
      cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
      cancel (store_Z p_pre zp_low_level_spec).
    + split_pures; try exact Hpart_next; try lia;
        dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_build_aug_basis_gmp_entail_wit_4_1 : build_aug_basis_gmp_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  assert (Hj_cols : j = cols) by lia.
  assert (Hidx_next : idx = (i + 1) * cols).
  { rewrite PreH21. rewrite Hj_cols. ring. }
  Exists laug_cur_2.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) laug_cur_2).
  - split_pures; try exact PreH32; try lia;
      dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_build_aug_basis_gmp_entail_wit_4_2 : build_aug_basis_gmp_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  assert (Hj_cols : j = cols) by lia.
  assert (Hidx_next : idx = (i + 1) * cols).
  { rewrite PreH21. rewrite Hj_cols. ring. }
  Exists laug_cur_2.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) laug_cur_2).
  - split_pures; try exact PreH33; try lia;
      dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_build_aug_basis_gmp_entail_wit_4_3 : build_aug_basis_gmp_entail_wit_4_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  assert (Hj_cols : j = cols) by lia.
  assert (Hidx_next : idx = (i + 1) * cols).
  { rewrite PreH21. rewrite Hj_cols. ring. }
  Exists laug_cur_2.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) laug_cur_2).
  - split_pures; try exact PreH32; try lia;
      dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_build_aug_basis_gmp_entail_wit_4_4 : build_aug_basis_gmp_entail_wit_4_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  assert (Hj_cols : j = cols) by lia.
  assert (Hidx_next : idx = (i + 1) * cols).
  { rewrite PreH21. rewrite Hj_cols. ring. }
  Exists laug_cur_2.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
    cancel (mpz_array aug_pre (n_pre * cols) laug_cur_2).
  - split_pures; try exact PreH33; try lia;
      dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_build_aug_basis_gmp_return_wit_1 : build_aug_basis_gmp_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  assert (Hi_done : i = n_pre) by lia.
  assert (Hidx_full : idx = n_pre * cols).
  { rewrite PreH19. rewrite Hi_done. ring. }
  Exists laug_cur.
  split_pure_spatial.
  - cancel (store_Z p_pre zp_low_level_spec).
    cancel (mpz_array a_pre (n_pre * n_pre) la_low_level_spec).
    replace (n_pre * (n_pre + 1)) with (n_pre * cols) by lia.
    cancel (mpz_array aug_pre (n_pre * cols) laug_cur).
  - split_pures.
    + dump_pre_spatial.
      replace (n_pre + 1) with cols by lia.
      apply partial_full_implies_rep_matrix.
      rewrite <- Hidx_full.
      exact PreH26.
    + dump_pre_spatial.
      apply matrix_aug_basis_mat_mod; assumption.
Qed.
