Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic GraphLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.

Module GraphMatrixLib.
  Include GraphLibSig
    Arch32 BigEndian
    naive_C_Rules naive_C_Rules naive_C_Rules naive_C_Rules naive_C_Rules
    naive_C_Rules.
End GraphMatrixLib.

Module GraphMatrixFlat.

Module Core := GraphMatrixLib.IntMatrixRowsRep.

Definition matrix_rep
    (size : Z)
    (matrix : addr) (rows : list (list Z))
    : Assertion :=
  Core.matrix_rep size matrix rows.

Definition store_graph
    (size : Z)
    (model : list (list Z) -> Prop)
    (matrix : addr) (rows : list (list Z))
    : Assertion :=
  “ model rows ” && matrix_rep size matrix rows.
  
Lemma store_graph_elim_matrix :
  forall size model matrix rows,
    store_graph size model matrix rows
    |-- “ model rows ” && matrix_rep size matrix rows.
Proof.
  intros.
  unfold store_graph.
  normalize.
  cancel.
Qed.

Lemma store_graph_elim :
  forall size model matrix rows,
    store_graph size model matrix rows
    |-- “ model rows ” && IntArray2.full matrix size size rows.
Proof.
  intros.
  unfold store_graph, matrix_rep, Core.matrix_rep.
  change (Core.CellArray2.full matrix size size rows) with
    (IntArray2.full matrix size size rows).
  normalize.
  cancel.
Qed.

Lemma store_graph_model :
  forall size model matrix rows,
    store_graph size model matrix rows |-- “ model rows ”.
Proof.
  intros.
  unfold store_graph.
  Intros_p Hmodel.
  dump_pre_spatial.
  exact Hmodel.
Qed.

Lemma store_graph_intro_matrix :
  forall size model matrix rows,
    model rows ->
    matrix_rep size matrix rows
    |-- store_graph size model matrix rows.
Proof.
  intros size model matrix rows Hmodel.
  unfold store_graph.
  normalize.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    exact Hmodel.
Qed.

Lemma store_graph_intro :
  forall size model matrix rows,
    model rows ->
    IntArray2.full matrix size size rows
    |-- store_graph size model matrix rows.
Proof.
  intros size model matrix rows Hmodel.
  unfold store_graph, matrix_rep, Core.matrix_rep.
  change (Core.CellArray2.full matrix size size rows) with
    (IntArray2.full matrix size size rows).
  normalize.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    exact Hmodel.
Qed.

End GraphMatrixFlat.

Module GraphMatrixPtr.

Module Core := GraphMatrixLib.IntPtrMatrixRowsRep.

Definition matrix_rep
    (row_count : Z)
    (matrix : addr) (rows : list (list Z))
    : Assertion :=
  Core.matrix_rep row_count matrix rows.

Definition store_graph
    (row_count : Z)
    (model : list (list Z) -> Prop)
    (matrix : addr) (rows : list (list Z))
    : Assertion :=
  “ model rows ” && matrix_rep row_count matrix rows.

Definition row_rep
    (row_count : Z)
    (model : list (list Z) -> Prop)
    (matrix : addr) (row_index row_ptr : addr)
    (rows : list (list Z))
    : Assertion :=
  “ model rows ” &&
  ((matrix + row_index * sizeof (PTR)) # Ptr |-> row_ptr) **
  IntArray.full row_ptr
    (Zlength (Znth row_index rows nil))
    (Znth row_index rows nil) **
  IntPtrArray2.missing_i matrix row_count row_index row_ptr rows.

Lemma store_graph_elim_matrix :
  forall row_count model matrix rows,
    store_graph row_count model matrix rows
    |-- “ model rows ” && matrix_rep row_count matrix rows.
Proof.
  intros.
  unfold store_graph.
  normalize.
  cancel.
Qed.

Lemma store_graph_elim :
  forall row_count model matrix rows,
    store_graph row_count model matrix rows
    |-- “ model rows ” && IntPtrArray2.full matrix row_count rows.
Proof.
  intros.
  unfold store_graph, matrix_rep, Core.matrix_rep.
  change (Core.CellPtrArray2.full matrix row_count rows) with
    (IntPtrArray2.full matrix row_count rows).
  normalize.
  cancel.
Qed.

Lemma store_graph_model :
  forall row_count model matrix rows,
    store_graph row_count model matrix rows |-- “ model rows ”.
Proof.
  intros.
  unfold store_graph.
  Intros_p Hmodel.
  dump_pre_spatial.
  exact Hmodel.
Qed.

Lemma store_graph_intro_matrix :
  forall row_count model matrix rows,
    model rows ->
    matrix_rep row_count matrix rows
    |-- store_graph row_count model matrix rows.
Proof.
  intros row_count model matrix rows Hmodel.
  unfold store_graph.
  normalize.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    exact Hmodel.
Qed.

Lemma store_graph_intro :
  forall row_count model matrix rows,
    model rows ->
    IntPtrArray2.full matrix row_count rows
    |-- store_graph row_count model matrix rows.
Proof.
  intros row_count model matrix rows Hmodel.
  unfold store_graph, matrix_rep, Core.matrix_rep.
  change (Core.CellPtrArray2.full matrix row_count rows) with
    (IntPtrArray2.full matrix row_count rows).
  normalize.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    exact Hmodel.
Qed.

Lemma store_graph_split_row :
  forall row_count matrix_model matrix rows row_index,
    0 <= row_index < row_count ->
    store_graph row_count matrix_model matrix rows
    |-- EX row_ptr,
          row_rep row_count matrix_model matrix row_index row_ptr rows.
Proof.
  intros row_count matrix_model matrix rows row_index Hrow.
  sep_apply (@store_graph_elim row_count matrix_model matrix rows).
  Intros_p Hmodel.
  prop_apply (IntPtrArray2.full_Zlength matrix row_count rows).
  Intros.
  sep_apply_l_atomic
    (IntPtrArray2.full_split_to_missing_i matrix row_index row_count rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold row_rep.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth row_index rows nil))
      (Znth row_index rows nil)) with
      (IntArray.full row_ptr
        (Zlength (Znth row_index rows nil))
        (Znth row_index rows nil)).
    change (sizeof (PTR)) with ptr_size_Z.
    fold_arch.
    normalize.
    split_pure_spatial.
    + cancel (IntPtrArray2.missing_i
        matrix row_count row_index row_ptr rows).
      cancel (IntArray.full row_ptr
        (Zlength (Znth row_index rows nil))
        (Znth row_index rows nil)).
      cancel.
    + dump_pre_spatial.
      exact Hmodel.
Qed.

Lemma missing_i_rows_Zlength :
  forall matrix row_count row_index row_ptr rows,
    IntPtrArray2.missing_i matrix row_count row_index row_ptr rows
    |-- “ Zlength rows = row_count ”.
Proof.
  intros.
  unfold IntPtrArray2.missing_i.
  Intros row_ptrs.
  normalize.
  dump_pre_spatial.
  tauto.
Qed.

Lemma row_rep_merge :
  forall row_count matrix_model matrix row_index row_ptr rows,
    0 <= row_index < row_count ->
    row_rep row_count matrix_model matrix row_index row_ptr rows
    |-- store_graph row_count matrix_model matrix rows.
Proof.
  intros row_count matrix_model matrix row_index row_ptr rows Hrow.
  unfold row_rep.
  Intros_p Hmodel.
  prop_apply
    (missing_i_rows_Zlength matrix row_count row_index row_ptr rows).
  Intros.
  pose proof
    (IntPtrArray2.missing_i_merge_to_full
      matrix row_index row_count row_ptr rows
      (Znth row_index rows nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth row_index rows nil))
    (Znth row_index rows nil)) with
    (IntArray.full row_ptr
      (Zlength (Znth row_index rows nil))
      (Znth row_index rows nil)) in Hmerge.
  change (sizeof (PTR)) with ptr_size_Z.
  fold_arch.
  sep_apply_l_atomic (Hmerge Hrow).
  rewrite replace_Znth_Znth by lia.
  sep_apply (@store_graph_intro row_count matrix_model matrix rows Hmodel).
  cancel.
Qed.

End GraphMatrixPtr.
