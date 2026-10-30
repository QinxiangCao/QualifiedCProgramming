From SimpleC.Verification Require Import StrategyPrelude.
From AUXLib Require Import ListLib.
From SimpleC.EE.QCP_demos_LLM Require Import graph_matrix_strategy_goal.
Require Import SimpleC.EE.QCP_demos_LLM.graph_matrix_lib.
Import naive_C_Rules.
Local Open Scope sac.
Local Open Scope string.

Lemma graph_matrix_strategy1_correctness : graph_matrix_strategy1.
Proof.
  LLM_pre_process ltac:(lia || nia).
  sep_apply (@GraphMatrixFlat.store_graph_elim n model0 p rows).
  cancel.
Qed.

Lemma graph_matrix_strategy2_correctness : graph_matrix_strategy2.
Proof.
  LLM_pre_process ltac:(lia || nia).
  cbn [poly_store poly_undef_store].
  subst size.
  sep_apply (@GraphMatrixFlat.store_graph_elim n model0 p rows).
  Intros_p Hmodel.
  prop_apply (IntArray2.full_Zlength p n n rows).
  Intros.
  sep_apply_l_atomic (IntArray2.full_split_to_missing_i
    p i n n rows).
  - dump_pre_spatial.
    lia.
  - rewrite (Znth_indep rows i nil __default_app1_Z) by lia.
    sep_apply_l_atomic
      (IntArray.full_split_to_missing_i
        (p + i * n * sizeof_front_end_type FET_int)
        j n (Znth i rows __default_app1_Z) 0).
    + dump_pre_spatial.
      lia.
    + split_pure_spatial.
      2: {
        dump_pre_spatial.
        exact Hmodel.
      }
      cancel (IntArray2.missing_i p i 0 n n rows).
      replace (p + i * n * 4)
        with (p + i * n * sizeof (INT))
        by (rewrite sizeof_int; lia).
      replace (p + (i * n + j) * 4)
        with (p + (i * n + j) * sizeof (INT))
        by (rewrite sizeof_int; lia).
      cancel (IntArray.missing_i
        (p + i * n * sizeof_front_end_type FET_int)
        j 0 n (Znth i rows __default_app1_Z)).
      Intros_r v.
      apply_sepcon_adjoint.
      Intros_p Hval.
      subst v.
      replace ((i * n + j) * sizeof (INT))
        with (i * n * sizeof (INT) + j * sizeof (INT))
        by lia.
      rewrite Z.add_assoc.
      cancel.
Qed.

Lemma graph_matrix_strategy3_correctness : graph_matrix_strategy3.
Proof.
  LLM_pre_process ltac:(lia || nia).
  subst size.
  eapply GraphMatrixFlat.store_graph_intro.
  eauto.
Qed.

Lemma graph_matrix_strategy4_correctness : graph_matrix_strategy4.
Proof.
  LLM_pre_process ltac:(lia || nia).
  cbn [poly_store poly_undef_store].
  subst w.
  sep_apply (@GraphMatrixFlat.store_graph_elim size model0 p rows).
  Intros_p Hmodel.
  prop_apply (IntArray2.full_Zlength p size size rows).
  Intros.
  sep_apply (IntArray2.full_split_to_missing_i p i size size rows);
    try lia.
  cancel (IntArray2.missing_i p i 0 size size rows).
  replace (Znth i rows nil) with (Znth i rows __default_app1_Z)
    by (apply Znth_indep; try lia).
  change (IntArray2.ElemArray.full (IntArray2.row_addr p size i)
    size (Znth i rows __default_app1_Z)) with
    (IntArray.full (p + i * size * sizeof (INT))
      size (Znth i rows __default_app1_Z)).
  sep_apply (IntArray.full_split_to_missing_i
    (p + i * size * sizeof (INT)) j size
    (Znth i rows __default_app1_Z) 0); try lia.
  split_pure_spatial.
  2: {
    dump_pre_spatial.
    exact Hmodel.
  }
  rewrite !Z.mul_assoc.
  cancel (IntArray.missing_i
    (p + i * size * sizeof (INT))
    j 0 size (Znth i rows __default_app1_Z)).
  cancel (IntArray2.missing_i p i 0 size size rows).
  Intros_r v.
  apply_sepcon_adjoint.
  Intros_p Hval.
  subst v.
  replace (p + i * size * sizeof (INT) + j * 4)
    with (p + i * size * sizeof (INT) + j * sizeof (INT))
      by (rewrite sizeof_int; lia).
  cancel.
Qed.

Lemma graph_matrix_strategy6_correctness : graph_matrix_strategy6.
Proof.
  LLM_pre_process ltac:(lia || nia).
  subst size.
  eapply GraphMatrixPtr.store_graph_intro.
  eauto.
Qed.

Lemma graph_matrix_strategy7_correctness : graph_matrix_strategy7.
Proof.
  LLM_pre_process ltac:(lia || nia).
  cbn [poly_store poly_undef_store].
  sep_apply (@GraphMatrixPtr.store_graph_elim size model0 p rows).
  Intros_p Hmodel.
  prop_apply (IntPtrArray2.full_Zlength p size rows).
  Intros.
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i p i size rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows i nil __default_app1_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows __default_app1_Z))
      (Znth i rows __default_app1_Z)) with
      (IntArray.full row_ptr (Zlength (Znth i rows __default_app1_Z))
        (Znth i rows __default_app1_Z)).
    normalize.
    split_pure_spatial.
    + cancel (IntPtrArray2.missing_i p size i row_ptr rows).
      cancel (IntArray.full row_ptr
        (Zlength (Znth i rows __default_app1_Z))
        (Znth i rows __default_app1_Z)).
      Intros_r v.
      apply_sepcon_adjoint.
      Intros_p Hval.
      subst v.
      cancel.
    + dump_pre_spatial.
      exact Hmodel.
Qed.

Lemma graph_matrix_strategy8_correctness : graph_matrix_strategy8.
Proof.
  LLM_pre_process ltac:(lia || nia).
  cbn [poly_store poly_undef_store].
  subst read_ptr.
  unfold GraphMatrixPtr.row_rep.
  Intros_p Hmodel.
  prop_apply (GraphMatrixPtr.missing_i_rows_Zlength p size i row_ptr rows).
  Intros.
  rewrite (Znth_indep rows i nil __default_app1_Z) by lia.
  sep_apply_l_atomic
    (IntArray.full_split_to_missing_i row_ptr j
      (Zlength (Znth i rows __default_app1_Z))
      (Znth i rows __default_app1_Z) 0).
  - dump_pre_spatial.
    lia.
  - normalize.
    split_pure_spatial.
    + cancel (IntArray.missing_i row_ptr j 0
        (Zlength (Znth i rows __default_app1_Z))
        (Znth i rows __default_app1_Z)).
      cancel (IntPtrArray2.missing_i p size i row_ptr rows).
      cancel.
      Intros_r v.
      apply_sepcon_adjoint.
      Intros_p Hval.
      subst v.
      cancel.
    + dump_pre_spatial.
      exact Hmodel.
Qed.

Lemma graph_matrix_strategy9_correctness : graph_matrix_strategy9.
Proof.
  LLM_pre_process ltac:(lia || nia).
  cbn [poly_store poly_undef_store].
  unfold GraphMatrixPtr.row_rep.
  Intros_p Hmodel.
  prop_apply (GraphMatrixPtr.missing_i_rows_Zlength p size i row_ptr rows).
  Intros.
  rewrite (Znth_indep rows i nil __default_app1_Z) by lia.
  normalize.
  split_pure_spatial.
  + cancel (IntArray.full row_ptr
      (Zlength (Znth i rows __default_app1_Z))
      (Znth i rows __default_app1_Z)).
    cancel (IntPtrArray2.missing_i p size i row_ptr rows).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros_p Hval.
    subst v.
    cancel.
  + dump_pre_spatial.
    exact Hmodel.
Qed.

Lemma graph_matrix_strategy10_correctness : graph_matrix_strategy10.
Proof.
  LLM_pre_process ltac:(lia || nia).
  cbn [poly_store poly_undef_store].
  prop_apply (GraphMatrixPtr.missing_i_rows_Zlength
    p size i row_ptr rows).
  Intros.
  unfold GraphMatrixPtr.row_rep.
  rewrite (Znth_indep rows i nil __default_app1_Z) by lia.
  normalize.
  split_pure_spatial.
  + cancel (IntArray.full row_ptr
      (Zlength (Znth i rows __default_app1_Z))
      (Znth i rows __default_app1_Z)).
    cancel (IntPtrArray2.missing_i p size i row_ptr rows).
    cancel.
  + dump_pre_spatial.
    exact H.
Qed.

Lemma graph_matrix_strategy11_correctness : graph_matrix_strategy11.
Proof.
  LLM_pre_process ltac:(lia || nia).
  sep_apply (@GraphMatrixPtr.row_rep_merge
    size model0 p i row_ptr rows).
  unfold GraphMatrixPtr.store_graph, GraphMatrixPtr.matrix_rep,
    GraphMatrixPtr.Core.matrix_rep.
  normalize.
  cancel.
  lia.
Qed.
