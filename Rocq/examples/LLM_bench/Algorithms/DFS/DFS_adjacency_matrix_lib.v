Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.SL Require Import GraphLib.
Require Import SimpleC.EE.QCP_demos_LLM.graph_matrix_lib.
From SimpleC.EE.LLM_bench.Algorithms.DFS Require Export concrete_graphs.
Require Import GraphLib.reachable.reachable_basic.
From MonadLib.StateRelMonad Require Import StateRelBasic.
Require Import Algorithms.DFS.DFS.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Import MonadNotation.
Local Open Scope Z_scope.
Local Open Scope monad.
Import naive_C_Rules.
Local Open Scope sac.

Module DFSAdjacencyMatrixGraphLib.
  Include GraphLibSig
    Arch32 BigEndian
    naive_C_Rules naive_C_Rules naive_C_Rules naive_C_Rules naive_C_Rules
    naive_C_Rules.
End DFSAdjacencyMatrixGraphLib.

(** Annotation-facing application combinator used by generated refinement
    obligations. *)
Definition applyf {A B : Type} (f : A -> B) (a : A) : B := f a.

Module DFSAdjacencyMatrix.

Module BooleanGraph <: DFSAdjacencyMatrixGraphLib.BOOLEAN_MATRIX_GRAPH.
  Definition G : Type := ZSimpleGraph.G.
  Definition vertex_count : G -> Z := ZSimpleGraph.vertex_count.
  Definition graph_wf : G -> Prop := ZSimpleGraph.graph_wf.
  Definition vertex_valid : G -> Z -> Prop := ZSimpleGraph.vertex_valid.
  Definition graph_step : G -> Z -> Z -> Prop := ZSimpleGraph.graph_step.

  Lemma vertex_valid_count :
    forall g v,
      graph_wf g ->
      vertex_valid g v ->
      DFSAdjacencyMatrixGraphLib.vertex_index (vertex_count g) v.
  Proof.
    intros g v _ Hv.
    exact Hv.
  Qed.
End BooleanGraph.

Module MatrixGraph :=
  DFSAdjacencyMatrixGraphLib.BooleanIntMatrixGraphModelLib BooleanGraph.

Definition matrix_layout
    (g : ZSimpleGraph.G) (rows : list (list Z))
    : DFSAdjacencyMatrixGraphLib.IntMatrixLayoutStore.Layout :=
  DFSAdjacencyMatrixGraphLib.mkMatrixLayout
    Z (ZSimpleGraph.vertex_count g) rows.

(** Annotation-facing specialization: [E] is not determined by [G] and [V],
    so Rocq cannot infer the concrete [Graph G V E] instance from [DFS g u]. *)
Definition dfs_program
    (g : ZSimpleGraph.G) (u : Z) : program (Z -> Prop) unit :=
  @DFS
    ZSimpleGraph.G Z ZSimpleGraph.E
    ZSimpleGraph.graph_instance g u.

(** Annotation-facing specialization of graph reachability. *)
Definition graph_reachable
    (g : ZSimpleGraph.G) (u v : Z) : Prop :=
  @reachable
    ZSimpleGraph.G Z ZSimpleGraph.E
    ZSimpleGraph.graph_instance
    g u v.

(** The loop left after the initial visit performed by [dfs_program]. *)
Definition dfs_loop
    (g : ZSimpleGraph.G) (source : Z) : program (Z -> Prop) unit :=
  whileP
    (fun visited_set =>
      exists neighbor,
        ZSimpleGraph.graph_step g source neighbor /\
        ~ visited_set neighbor)
    (neighbor <- get (fun visited_set neighbor =>
       ZSimpleGraph.graph_step g source neighbor /\
       ~ visited_set neighbor);;
     dfs_program g neighbor).

(** Continuation used when one recursive DFS call returns to the enclosing
    vertex's remaining abstract loop. *)
Definition dfs_continue
    (g : ZSimpleGraph.G) (source : Z)
    (_ : unit) : program (Z -> Prop) unit :=
  dfs_loop g source.

(** The source is visited, and every outgoing neighbor whose matrix column is
    already scanned is in the current abstract visited set. *)
Definition processed_neighbors
    (g : ZSimpleGraph.G) (source upto : Z)
    (visited_set : Z -> Prop) : Prop :=
  visited_set source /\
  forall v,
    0 <= v < upto ->
    ZSimpleGraph.graph_step g source v ->
    visited_set v.

(** DFS only adds vertices to the visited set. *)
Definition visited_extension
    (before after : Z -> Prop) : Prop :=
  forall v, before v -> after v.

(** The public entry point starts from an empty visited set.  Naming this
    predicate also keeps the annotation-level contract free of nested binders. *)
Definition empty_visited (visited_set : Z -> Prop) : Prop :=
  forall v, ~ visited_set v.

(** Annotation-facing pure relation between a square 0/1 matrix and the graph.
    The short name is kept for generated goals; the definition is provided by
    [GraphLib]'s boolean integer matrix instance. *)
Definition adjacency_matrix_model
    (g : ZSimpleGraph.G) (rows : list (list Z)) : Prop :=
  MatrixGraph.model g (matrix_layout g rows).

Definition visited
    (visited_ptr : addr) (g : ZSimpleGraph.G) (visited_set : Z -> Prop)
    : Assertion :=
  EX values : list Z,
    “ ZSimpleGraph.visited_values g values visited_set ” &&
    IntArray.full visited_ptr (ZSimpleGraph.vertex_count g) values.

Lemma adjacency_matrix_model_as_matrix_model :
  forall g rows,
    adjacency_matrix_model g rows ->
    MatrixGraph.model g (matrix_layout g rows).
Proof.
  intros g rows Hmodel.
  exact Hmodel.
Qed.

Lemma adjacency_matrix_model_step :
  forall g rows u v,
    adjacency_matrix_model g rows ->
    ZSimpleGraph.vertex_valid g u ->
    ZSimpleGraph.vertex_valid g v ->
    (Znth v (Znth u rows nil) 0 = 1 <->
     ZSimpleGraph.graph_step g u v).
Proof.
  intros g rows u v Hmodel Hu Hv.
  pose proof
    (adjacency_matrix_model_as_matrix_model g rows Hmodel)
    as Hmatrix.
  pose proof
    (MatrixGraph.model_step g (matrix_layout g rows) u v
      Hmatrix Hu Hv) as Hstep.
  unfold MatrixGraph.cell, matrix_layout in Hstep.
  simpl in Hstep.
  exact Hstep.
Qed.

Lemma adjacency_matrix_model_bit :
  forall g rows u v,
    adjacency_matrix_model g rows ->
    ZSimpleGraph.vertex_valid g u ->
    ZSimpleGraph.vertex_valid g v ->
    (Znth v (Znth u rows nil) 0 = 0 \/
     Znth v (Znth u rows nil) 0 = 1).
Proof.
  intros g rows u v Hmodel Hu Hv.
  pose proof
    (adjacency_matrix_model_as_matrix_model g rows Hmodel)
    as Hmatrix.
  pose proof
    (MatrixGraph.model_bit_cell g (matrix_layout g rows) u v
      Hmatrix Hu Hv) as Hbit.
  unfold MatrixGraph.cell, matrix_layout in Hbit.
  simpl in Hbit.
  exact Hbit.
Qed.

Lemma adjacency_matrix_model_nonzero_step :
  forall g rows u v d,
    adjacency_matrix_model g rows ->
    ZSimpleGraph.vertex_valid g u ->
    ZSimpleGraph.vertex_valid g v ->
    Znth v (Znth u rows d) 0 <> 0 ->
    ZSimpleGraph.graph_step g u v.
Proof.
  intros g rows u v d Hmodel Hu Hv Hnonzero.
  assert (Hrow:
    Znth u rows d = Znth u rows nil).
  { pose proof
      (MatrixGraph.model_shape g (matrix_layout g rows) Hmodel)
      as Hshape.
    unfold matrix_layout in Hshape.
    simpl in Hshape.
    destruct Hshape as [Hlen _].
    apply Znth_indep.
    rewrite Hlen.
    unfold ZSimpleGraph.vertex_valid in Hu.
    exact Hu. }
  rewrite Hrow in Hnonzero.
  pose proof
    (adjacency_matrix_model_bit g rows u v Hmodel Hu Hv)
    as [Hzero | Hone].
  - contradiction.
  - apply (proj1
      (adjacency_matrix_model_step g rows u v Hmodel Hu Hv)).
    exact Hone.
Qed.

Lemma adjacency_matrix_model_zero_not_step :
  forall g rows u v d,
    adjacency_matrix_model g rows ->
    ZSimpleGraph.vertex_valid g u ->
    ZSimpleGraph.vertex_valid g v ->
    Znth v (Znth u rows d) 0 = 0 ->
    ~ ZSimpleGraph.graph_step g u v.
Proof.
  intros g rows u v d Hmodel Hu Hv Hzero Hedge.
  assert (Hrow:
    Znth u rows d = Znth u rows nil).
  { pose proof
      (MatrixGraph.model_shape g (matrix_layout g rows) Hmodel)
      as Hshape.
    unfold matrix_layout in Hshape.
    simpl in Hshape.
    destruct Hshape as [Hlen _].
    apply Znth_indep.
    rewrite Hlen.
    unfold ZSimpleGraph.vertex_valid in Hu.
    exact Hu. }
  rewrite Hrow in Hzero.
  apply (proj2
    (adjacency_matrix_model_step g rows u v Hmodel Hu Hv)) in Hedge.
  lia.
Qed.

End DFSAdjacencyMatrix.
Lemma visited_values_after_visit__dfs_core :
  forall g values before u,
    ZSimpleGraph.visited_values g values before ->
    ZSimpleGraph.vertex_valid g u ->
    ZSimpleGraph.visited_values g (replace_Znth u 1 values)
      (fun v => before v \/ v = u).
Proof.
  intros g values before u Hvalues Hu.
  unfold ZSimpleGraph.visited_values in *.
  destruct Hvalues as [Hlen [Hvalid Hvalue]].
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - split.
    + intros v [Hv | ->]; auto.
    + intros v Hv.
      specialize (Hvalue v Hv) as [H01 Hiff].
      destruct (Z.eq_dec v u) as [-> | Hne].
      * rewrite Znth_replace_Znth_Same by
            (unfold ZSimpleGraph.vertex_valid in *; lia).
        split; [auto |].
        split; [tauto | intros; right; reflexivity].
      * rewrite Znth_replace_Znth_Diff by
            (unfold ZSimpleGraph.vertex_valid in *; lia).
        split; [exact H01 |].
        split.
        -- intros [Hb | Heq]; [apply Hiff; exact Hb | contradiction].
        -- intros Hbit. left. apply Hiff. exact Hbit.
Qed.
Lemma matrix_split_merge__dfs_core :
  forall matrix n rows i j (d : list Z),
    0 <= i < n ->
    0 <= j < n ->
    ((matrix + (i * n + j) * sizeof (INT)) # Int
      |-> Znth j (Znth i rows d) 0) **
    IntArray.missing_i (matrix + i * n * sizeof (INT))
      j 0 n (Znth i rows d) **
    IntArray2.missing_i matrix i 0 n n rows
    |-- IntArray2.full matrix n n rows.
Proof.
  intros matrix n rows i j d Hi Hj.
  replace (matrix + (i * n + j) * sizeof (INT))
    with ((matrix + i * n * sizeof (INT)) + j * sizeof (INT)) by lia.
  prop_apply (IntArray.missing_i_Zlength
    (matrix + i * n * sizeof (INT)) j 0 n (Znth i rows d)).
  Intros. rename H into Hrowlen.
  prop_apply (IntArray2.missing_i_Zlength matrix i 0 n n rows).
  Intros. rename H into Hrowslen.
  sep_apply (IntArray.missing_i_merge_to_full
    (matrix + i * n * sizeof (INT)) j n
    (Znth j (Znth i rows d) 0) (Znth i rows d)); try lia.
  rewrite replace_Znth_Znth by lia.
  pose proof (IntArray2.missing_i_merge_to_full
    matrix i n n rows (Znth i rows d)) as Hmerge_rows.
  change (IntArray2.ElemArray.full (IntArray2.row_addr matrix n i)
    n (Znth i rows d))
    with (IntArray.full (matrix + i * n * sizeof (INT))
      n (Znth i rows d)) in Hmerge_rows.
  sep_apply Hmerge_rows; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.
