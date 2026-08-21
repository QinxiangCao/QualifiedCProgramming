Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem CommonAssertion StoreAux ArrayLib Array2Lib PtrArray2Lib.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list.

(**
  Core interfaces for matrix-backed graph data.

  The library keeps two layers separate.

  - [MatrixRowsRepLib] is the assertion-facing layer used by C annotations:
    a concrete matrix in memory is paired with a pure predicate over its rows.
  - [MatrixGraphModelLib] is a pure model layer: it explains when a matrix
    layout represents a graph, but it does not introduce another assertion
    wrapper.

  This mirrors the actual DFS/Floyd use case: C memory is first recovered as
  rows, then algorithm-specific pure predicates relate those rows to a graph or
  to a mutable matrix state.

  Current public graph-model support is intentionally small: the assertion
  layer is polymorphic over the element store, and the pure graph layer provides
  the boolean adjacency-matrix model used by DFS.  Weighted graph matrix models
  can be added later when Floyd/Dijkstra are moved to a shared pure model.
*)

Module Type GraphLibCoreSig
  (Arch : CArchSig)
  (Endian : CEndianSig)
  (CRules: SeparationLogicSig)
  (DePredSig : DerivedPredSig Arch Endian CRules)
  (SLibSig : StoreLibSig Arch Endian CRules DePredSig)
  (ALibSig : ArrayLibSig Arch Endian CRules DePredSig SLibSig)
  (A2LibSig : Array2LibSig Arch Endian CRules DePredSig SLibSig ALibSig)
  (P2LibSig : PtrArray2LibSig Arch Endian CRules DePredSig SLibSig ALibSig).

Import CRules.
Import DePredSig.
Import SLibSig.
Import ALibSig.
Import A2LibSig.
Import P2LibSig.
Local Open Scope sac.

Definition vertex_index (n v : Z) : Prop :=
  0 <= v < n.

Definition matrix_cell {A : Type}
    (rows : list (list A)) (default : A) (u v : Z) : A :=
  Znth v (Znth u rows nil) default.

Definition matrix_shape {A : Type}
    (n : Z) (rows : list (list A)) : Prop :=
  Zlength rows = n /\
  forall i,
    vertex_index n i ->
    Zlength (Znth i rows nil) = n.

Record matrix_layout (A : Type) : Type := mkMatrixLayout {
  matrix_size : Z;
  matrix_rows : list (list A);
}.

Arguments matrix_size {A} _.
Arguments matrix_rows {A} _.

Module Type MATRIX_LAYOUT_STORE.
  Parameter Inline Cell : Type.
  Parameter Inline Layout : Type.

  Parameter Inline layout_size : Layout -> Z.
  Parameter Inline layout_rows : Layout -> list (list Cell).
  Parameter Inline layout_rep : addr -> Layout -> Assertion.
End MATRIX_LAYOUT_STORE.

Module MatrixLayoutStore (ES : ELEMENT_STORE).
Import ES.
Module CellArray2 := Array2Lib ES.

Definition Cell : Type := A.
Definition Layout : Type := matrix_layout Cell.

Definition layout_size : Layout -> Z :=
  @matrix_size Cell.

Definition layout_rows : Layout -> list (list Cell) :=
  @matrix_rows Cell.

Definition layout_rep (matrix : addr) (layout : Layout) : Assertion :=
  CellArray2.full matrix (layout_size layout) (layout_size layout)
    (layout_rows layout).

End MatrixLayoutStore.

Module MatrixRowsRepLib (ES : ELEMENT_STORE).
Import ES.
Module CellArray2 := Array2Lib ES.

Definition matrix_rep
    (size : Z)
    (matrix : addr) (rows : list (list A))
    : Assertion :=
  CellArray2.full matrix size size rows.

Definition graph_rep
    (size : Z)
    (model : list (list A) -> Prop)
    (matrix : addr) (rows : list (list A))
    : Assertion :=
  “ model rows ” && matrix_rep size matrix rows.

Lemma graph_rep_elim_matrix :
  forall size model matrix rows,
    graph_rep size model matrix rows
    |-- “ model rows ” && matrix_rep size matrix rows.
Proof.
  intros.
  unfold graph_rep.
  normalize.
  cancel.
Qed.

Lemma graph_rep_elim :
  forall size model matrix rows,
    graph_rep size model matrix rows
    |-- “ model rows ” && CellArray2.full matrix size size rows.
Proof.
  intros.
  unfold graph_rep, matrix_rep.
  normalize.
  cancel.
Qed.

Lemma graph_rep_model :
  forall size model matrix rows,
    graph_rep size model matrix rows |-- “ model rows ”.
Proof.
  intros.
  unfold graph_rep.
  Intros_p Hmodel.
  dump_pre_spatial.
  exact Hmodel.
Qed.

Lemma graph_rep_intro_matrix :
  forall size model matrix rows,
    model rows ->
    matrix_rep size matrix rows
    |-- graph_rep size model matrix rows.
Proof.
  intros size model matrix rows Hmodel.
  unfold graph_rep.
  normalize.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    exact Hmodel.
Qed.

Lemma graph_rep_intro :
  forall size model matrix rows,
    model rows ->
    CellArray2.full matrix size size rows
    |-- graph_rep size model matrix rows.
Proof.
  intros size model matrix rows Hmodel.
  unfold graph_rep, matrix_rep.
  normalize.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    exact Hmodel.
Qed.

End MatrixRowsRepLib.

Module MatrixPtrRowsRepLib (ES : ELEMENT_STORE).
Import ES.
Module CellPtrArray2 := PtrArray2Lib ES.

Definition matrix_rep
    (row_count : Z)
    (matrix : addr) (rows : list (list A))
    : Assertion :=
  CellPtrArray2.full matrix row_count rows.

Definition graph_rep
    (row_count : Z)
    (model : list (list A) -> Prop)
    (matrix : addr) (rows : list (list A))
    : Assertion :=
  “ model rows ” && matrix_rep row_count matrix rows.

Lemma graph_rep_elim_matrix :
  forall row_count model matrix rows,
    graph_rep row_count model matrix rows
    |-- “ model rows ” && matrix_rep row_count matrix rows.
Proof.
  intros.
  unfold graph_rep.
  normalize.
  cancel.
Qed.

Lemma graph_rep_elim :
  forall row_count model matrix rows,
    graph_rep row_count model matrix rows
    |-- “ model rows ” && CellPtrArray2.full matrix row_count rows.
Proof.
  intros.
  unfold graph_rep, matrix_rep.
  normalize.
  cancel.
Qed.

Lemma graph_rep_model :
  forall row_count model matrix rows,
    graph_rep row_count model matrix rows |-- “ model rows ”.
Proof.
  intros.
  unfold graph_rep.
  Intros_p Hmodel.
  dump_pre_spatial.
  exact Hmodel.
Qed.

Lemma graph_rep_intro_matrix :
  forall row_count model matrix rows,
    model rows ->
    matrix_rep row_count matrix rows
    |-- graph_rep row_count model matrix rows.
Proof.
  intros row_count model matrix rows Hmodel.
  unfold graph_rep.
  normalize.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    exact Hmodel.
Qed.

Lemma graph_rep_intro :
  forall row_count model matrix rows,
    model rows ->
    CellPtrArray2.full matrix row_count rows
    |-- graph_rep row_count model matrix rows.
Proof.
  intros row_count model matrix rows Hmodel.
  unfold graph_rep, matrix_rep.
  normalize.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    exact Hmodel.
Qed.

End MatrixPtrRowsRepLib.

Module Type MATRIX_GRAPH_VIEW.
  Parameter Inline Cell : Type.
  Parameter Inline G : Type.
  Parameter Inline View : Type.

  Parameter Inline storage_size : G -> Z.
  Parameter Inline graph_wf : G -> Prop.
  Parameter Inline vertex_valid : G -> Z -> Prop.

  Parameter Inline cell_default : Cell.
  Parameter Inline cell_valid : Cell -> Prop.
  Parameter Inline cell_view : Cell -> View.
  Parameter Inline graph_view : G -> Z -> Z -> View.
  Parameter Inline view_rel : View -> View -> Prop.

  Axiom vertex_valid_storage :
    forall g v,
      graph_wf g ->
      vertex_valid g v ->
      vertex_index (storage_size g) v.
End MATRIX_GRAPH_VIEW.

Module MatrixGraphModelLib
  (MLS : MATRIX_LAYOUT_STORE)
  (MGV : MATRIX_GRAPH_VIEW with Definition Cell := MLS.Cell).

Definition G : Type := MGV.G.
Definition Layout : Type := MLS.Layout.
Definition layout_size := MLS.layout_size.
Definition layout_rows := MLS.layout_rows.

Definition cell (layout : Layout) (u v : Z) : MLS.Cell :=
  matrix_cell (layout_rows layout) MGV.cell_default u v.

Definition cells_valid (g : G) (layout : Layout) : Prop :=
  forall i j,
    vertex_index (layout_size layout) i ->
    vertex_index (layout_size layout) j ->
    MGV.cell_valid (cell layout i j).

Definition model (g : G) (layout : Layout) : Prop :=
  MGV.graph_wf g /\
  layout_size layout = MGV.storage_size g /\
  matrix_shape (layout_size layout) (layout_rows layout) /\
  cells_valid g layout /\
  forall u v,
    MGV.vertex_valid g u ->
    MGV.vertex_valid g v ->
    MGV.view_rel
      (MGV.cell_view (cell layout u v))
      (MGV.graph_view g u v).

Lemma model_graph_wf :
  forall g layout,
    model g layout ->
    MGV.graph_wf g.
Proof.
  intros g layout Hmodel.
  unfold model in Hmodel.
  tauto.
Qed.

Lemma model_size :
  forall g layout,
    model g layout ->
    MLS.layout_size layout = MGV.storage_size g.
Proof.
  intros g layout Hmodel.
  unfold model in Hmodel.
  tauto.
Qed.

Lemma model_shape :
  forall g layout,
    model g layout ->
    matrix_shape (MLS.layout_size layout) (MLS.layout_rows layout).
Proof.
  intros g layout Hmodel.
  unfold model in Hmodel.
  tauto.
Qed.

Lemma model_cell_valid :
  forall g layout i j,
    model g layout ->
    vertex_index (MLS.layout_size layout) i ->
    vertex_index (MLS.layout_size layout) j ->
    MGV.cell_valid (cell layout i j).
Proof.
  intros g layout i j Hmodel Hi Hj.
  unfold model in Hmodel.
  destruct Hmodel as [_ [_ [_ [Hcells _]]]].
  exact (Hcells i j Hi Hj).
Qed.

Lemma model_view :
  forall g layout u v,
    model g layout ->
    MGV.vertex_valid g u ->
    MGV.vertex_valid g v ->
    MGV.view_rel
      (MGV.cell_view (cell layout u v))
      (MGV.graph_view g u v).
Proof.
  intros g layout u v Hmodel Hu Hv.
  unfold model in Hmodel.
  destruct Hmodel as [_ [_ [_ [_ Hview]]]].
  exact (Hview u v Hu Hv).
Qed.

Lemma model_active_cell_valid :
  forall g layout u v,
    model g layout ->
    MGV.vertex_valid g u ->
    MGV.vertex_valid g v ->
    MGV.cell_valid (cell layout u v).
Proof.
  intros g layout u v Hmodel Hu Hv.
  pose proof (model_graph_wf g layout Hmodel) as Hwf.
  pose proof (model_size g layout Hmodel) as Hsize.
  eapply (model_cell_valid g layout u v); auto;
    rewrite Hsize; eapply MGV.vertex_valid_storage; eauto.
Qed.

End MatrixGraphModelLib.

Definition bit_cell (x : Z) : Prop :=
  x = 0 \/ x = 1.

Module Type BOOLEAN_MATRIX_GRAPH.
  Parameter Inline G : Type.
  Parameter Inline vertex_count : G -> Z.
  Parameter Inline graph_wf : G -> Prop.
  Parameter Inline vertex_valid : G -> Z -> Prop.
  Parameter Inline graph_step : G -> Z -> Z -> Prop.

  Axiom vertex_valid_count :
    forall g v,
      graph_wf g ->
      vertex_valid g v ->
      vertex_index (vertex_count g) v.
End BOOLEAN_MATRIX_GRAPH.

Module BooleanMatrixGraphView (BG : BOOLEAN_MATRIX_GRAPH).
  Definition Cell : Type := Z.
  Definition G : Type := BG.G.
  Definition View : Type := Prop.
  Definition storage_size : G -> Z := BG.vertex_count.
  Definition graph_wf : G -> Prop := BG.graph_wf.
  Definition vertex_valid : G -> Z -> Prop := BG.vertex_valid.
  Definition cell_default : Cell := 0.
  Definition cell_valid : Cell -> Prop := bit_cell.
  Definition cell_view (x : Cell) : View := x = 1.
  Definition graph_view : G -> Z -> Z -> View := BG.graph_step.
  Definition view_rel (P Q : View) : Prop := P <-> Q.

  Lemma vertex_valid_storage :
    forall g v,
      graph_wf g ->
      vertex_valid g v ->
      vertex_index (storage_size g) v.
  Proof.
    intros g v Hwf Hv.
    apply BG.vertex_valid_count; auto.
  Qed.
End BooleanMatrixGraphView.

Module BooleanMatrixGraphModelLib
  (MLS : MATRIX_LAYOUT_STORE with Definition Cell := Z)
  (BG : BOOLEAN_MATRIX_GRAPH).
  Module MGV := BooleanMatrixGraphView BG.
  Module MCore := MatrixGraphModelLib MLS MGV.
  Include MCore.

  Definition boolean_model : BG.G -> MLS.Layout -> Prop := model.

  Lemma model_step :
    forall g layout u v,
      model g layout ->
      BG.vertex_valid g u ->
      BG.vertex_valid g v ->
      (cell layout u v = 1 <-> BG.graph_step g u v).
  Proof.
    intros g layout u v Hmodel Hu Hv.
    apply (model_view g layout u v); auto.
  Qed.

  Lemma model_bit_cell :
    forall g layout u v,
      model g layout ->
      BG.vertex_valid g u ->
      BG.vertex_valid g v ->
      bit_cell (cell layout u v).
  Proof.
    intros g layout u v Hmodel Hu Hv.
    eapply (model_active_cell_valid g layout u v); eauto.
  Qed.
End BooleanMatrixGraphModelLib.

End GraphLibCoreSig.
