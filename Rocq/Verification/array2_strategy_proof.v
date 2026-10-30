From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.Verification Require Import array2_strategy_goal.
Import naive_C_Rules.
Local Open Scope sac.
Local Open Scope string.

Lemma array2_strategy1_correctness : array2_strategy1.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  prop_apply (IntArray2.full_Zlength p n m rows).
  Intros.
  sep_apply_l_atomic (IntArray2.full_split_to_missing_i p i n m rows).
  - dump_pre_spatial.
    lia.
  - rewrite (Znth_indep rows i __default_app1_Z nil) by lia.
    sep_apply_l_atomic
      (IntArray.full_split_to_missing_i
        (p + i * m * sizeof_front_end_type FET_int)
        j m (Znth i rows nil) 0).
    + dump_pre_spatial.
      lia.
    + cancel (IntArray2.missing_i p i 0 n m rows).
      cancel (IntArray.missing_i
        (p + i * m * sizeof_front_end_type FET_int)
        j 0 m (Znth i rows nil)).
      Intros_r v.
      apply_sepcon_adjoint.
      Intros_p Hval.
      subst v.
      cancel.
Qed.

Lemma array2_strategy4_correctness : array2_strategy4.
Proof.
  pre_process_default.
  Intros_p H.
  subst rows2.
  cancel.
Qed.

Lemma array2_strategy5_correctness : array2_strategy5.
Proof.
  pre_process_default.
Qed.

Lemma array2_strategy2_correctness : array2_strategy2.
Proof.
  pre_process_default.
  prop_apply (IntArray2.missing_i_Zlength p i 0 n m rows).
  Intros.
  pose proof (IntArray2.missing_i_merge_to_full
        p i n m rows (Znth i rows __default_app1_Z)).
  change (IntArray2.ElemArray.full (IntArray2.row_addr p m i)
m (Znth i rows __default_app1_Z)) with (IntArray.full (p + i * m * sizeof ( INT )) m
(Znth i rows __default_app1_Z)) in H2.
  sep_apply H2 ; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.


Lemma array2_strategy6_correctness : array2_strategy6.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  prop_apply (IntArray2.full_Zlength p n m rows). Intros.
  sep_apply (IntArray2.full_split_to_missing_i p i n m rows) ; try lia.
  cancel (IntArray2.missing_i p i 0 n m rows).
  rewrite (Znth_indep rows i __default_app1_Z nil) by lia.
  change (IntArray2.ElemArray.full (IntArray2.row_addr p m i) m (Znth i rows nil)) with
    (IntArray.full (p + i * m * sizeof ( INT )) m (Znth i rows nil)).
  sep_apply (IntArray.full_split_to_missing_i (p + i * m * sizeof ( INT )) j m (Znth i rows nil) 0) ; try lia.
  cancel (IntArray.missing_i (p + i * m * sizeof (INT)) j 0 m (Znth i rows nil)).
  Intros_r v.
  pre_process_default.
  Intros. subst.
  replace ((i * m + j) * sizeof ( INT )) with (i * m * sizeof ( INT ) + j * sizeof ( INT )) by lia.
  rewrite Z.add_assoc.
  cancel.
Qed.

Lemma array2_strategy7_correctness : array2_strategy7.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  subst w.
  rewrite !Z.mul_assoc.
  prop_apply (IntArray2.full_Zlength p n m rows).
  Intros.
  sep_apply (IntArray2.full_split_to_missing_i p i n m rows); try lia.
  cancel (IntArray2.missing_i p i 0 n m rows).
  rewrite (Znth_indep rows i __default_app1_Z nil) by lia.
  change (IntArray2.ElemArray.full (IntArray2.row_addr p m i)
    m (Znth i rows nil)) with
    (IntArray.full (p + i * m * sizeof (INT)) m
      (Znth i rows nil)).
  sep_apply (IntArray.full_split_to_missing_i
    (p + i * m * sizeof (INT)) j m (Znth i rows nil) 0); try lia.
  cancel (IntArray.missing_i (p + i * m * sizeof (INT))
    j 0 m (Znth i rows nil)).
  Intros_r v.
  apply_sepcon_adjoint.
  Intros_p Hval.
  subst v.
  cancel.
Qed.

Lemma array2_strategy8_correctness : array2_strategy8.
Proof.
  pre_process_default.
  subst w.
  prop_apply (IntArray2.missing_i_Zlength p i 0 n m rows).
  Intros.
  pose proof (IntArray2.missing_i_merge_to_full
        p i n m rows (Znth i rows __default_app1_Z)) as Hmerge.
  change (IntArray2.ElemArray.full (IntArray2.row_addr p m i)
    m (Znth i rows __default_app1_Z)) with
    (IntArray.full (p + i * m * sizeof (INT)) m
      (Znth i rows __default_app1_Z)) in Hmerge.
  rewrite !Z.mul_assoc.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

Lemma array2_strategy9_correctness : array2_strategy9.
Proof.
  exact array2_strategy2_correctness.
Qed.

Lemma array2_strategy10_correctness : array2_strategy10.
Proof.
  pre_process_default.
  prop_apply (IntArray2.missing_i_Zlength p i 0 n m rows).
  Intros.
  pose proof (IntArray2.missing_i_merge_to_full p i n m rows row) as Hmerge.
  change (IntArray2.ElemArray.full (IntArray2.row_addr p m i) m row) with
    (IntArray.full (p + i * m * sizeof (INT)) m row) in Hmerge.
  sep_apply Hmerge; try lia.
  cancel.
Qed.

Lemma array2_strategy11_correctness : array2_strategy11.
Proof.
  pre_process_default.
  subst w.
  prop_apply (IntArray2.missing_i_Zlength p i 0 n m rows).
  Intros.
  pose proof (IntArray2.missing_i_merge_to_full p i n m rows row) as Hmerge.
  change (IntArray2.ElemArray.full (IntArray2.row_addr p m i) m row) with
    (IntArray.full (p + i * m * sizeof (INT)) m row) in Hmerge.
  rewrite !Z.mul_assoc.
  sep_apply Hmerge; try lia.
  cancel.
Qed.

Lemma array2_strategy12_correctness : array2_strategy12.
Proof.
  exact array2_strategy10_correctness.
Qed.
