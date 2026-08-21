Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
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

Definition applyf {A B : Type} (f : A -> B) (a : A) : B := f a.

Module DFSAdjacencyMatrix2Darray.

Definition dfs_program
    (g : ZSimpleGraph.G) (u : Z) : program (Z -> Prop) unit :=
  @DFS
    ZSimpleGraph.G Z ZSimpleGraph.E
    ZSimpleGraph.graph_instance g u.

Definition graph_reachable
    (g : ZSimpleGraph.G) (u v : Z) : Prop :=
  @reachable
    ZSimpleGraph.G Z ZSimpleGraph.E
    ZSimpleGraph.graph_instance
    g u v.

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

Definition dfs_continue
    (g : ZSimpleGraph.G) (source : Z)
    (_ : unit) : program (Z -> Prop) unit :=
  dfs_loop g source.

Definition processed_neighbors
    (g : ZSimpleGraph.G) (source upto : Z)
    (visited_set : Z -> Prop) : Prop :=
  visited_set source /\
  forall v,
    0 <= v < upto ->
    ZSimpleGraph.graph_step g source v ->
    visited_set v.

Definition visited_extension
    (before after : Z -> Prop) : Prop :=
  forall v, before v -> after v.

Definition empty_visited (visited_set : Z -> Prop) : Prop :=
  forall v, ~ visited_set v.

Definition adjacency_matrix_model
    (g : ZSimpleGraph.G) (rows : list (list Z)) : Prop :=
  ZSimpleGraph.graph_wf g /\
  Zlength rows = ZSimpleGraph.vertex_count g /\
  Forall
    (fun row => Zlength row = ZSimpleGraph.vertex_count g)
    rows /\
  forall u v,
    ZSimpleGraph.vertex_valid g u ->
    ZSimpleGraph.vertex_valid g v ->
    let value := Znth v (Znth u rows nil) 0 in
    (value = 0 \/ value = 1) /\
    (value = 1 <-> ZSimpleGraph.graph_step g u v).

Definition graph_rep
    (matrix : addr) (g : ZSimpleGraph.G) (rows : list (list Z))
    : Assertion :=
  “ adjacency_matrix_model g rows ” &&
  IntPtrArray2.full
    matrix
    (ZSimpleGraph.vertex_count g)
    rows.

Definition graph (matrix : addr) (g : ZSimpleGraph.G) : Assertion :=
  EX rows : list (list Z),
    graph_rep matrix g rows.

Definition visited
    (visited_ptr : addr) (g : ZSimpleGraph.G) (visited_set : Z -> Prop)
    : Assertion :=
  EX values : list Z,
    “ ZSimpleGraph.visited_values g values visited_set ” &&
    IntArray.full visited_ptr (ZSimpleGraph.vertex_count g) values.

End DFSAdjacencyMatrix2Darray.

Require Import Coq.micromega.Lia.

Lemma visited_values_after_visit__dfs_2darray :
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

Lemma matrix_ptr_split_merge__dfs_2darray :
  forall matrix n rows i j row_ptr (d : list Z),
    0 <= i < n ->
    0 <= j < n ->
    (row_ptr + j * sizeof (INT)) # Int
      |-> Znth j (Znth i rows d) 0 **
    IntArray.missing_i row_ptr j 0 n (Znth i rows d) **
    StorePtrAsElement.storeA matrix i row_ptr **
    IntPtrArray2.missing_i matrix n i row_ptr rows
    |-- IntPtrArray2.full matrix n rows.
Proof.
  intros matrix n rows i j row_ptr d Hi Hj.
  prop_apply (IntArray.missing_i_Zlength
    row_ptr j 0 n (Znth i rows d)).
  Intros. rename H into Hrowlen.
  sep_apply (IntArray.missing_i_merge_to_full
    row_ptr j n
    (Znth j (Znth i rows d) 0) (Znth i rows d)); try lia.
  rewrite replace_Znth_Znth by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    matrix i n row_ptr rows (Znth i rows d)) as Hmerge_rows.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth i rows d)) (Znth i rows d)) with
    (IntArray.full row_ptr (Zlength (Znth i rows d))
      (Znth i rows d)) in Hmerge_rows.
  replace n with (Zlength (Znth i rows d)) at 1 by lia.
  sep_apply Hmerge_rows; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

Lemma adjacency_matrix_model_row_length__dfs_2darray_core :
  forall g rows u,
    DFSAdjacencyMatrix2Darray.adjacency_matrix_model g rows ->
    ZSimpleGraph.vertex_valid g u ->
    Zlength (Znth u rows nil) = ZSimpleGraph.vertex_count g.
Proof.
  intros g rows u Hmodel Hu.
  unfold DFSAdjacencyMatrix2Darray.adjacency_matrix_model in Hmodel.
  destruct Hmodel as [_ [Hrows [Hforall _]]].
  rewrite Forall_forall in Hforall.
  apply Hforall.
  unfold Znth.
  apply nth_In.
  replace (length rows) with (Z.to_nat (Zlength rows)).
  - apply Z2Nat.inj_lt.
    + unfold ZSimpleGraph.vertex_valid in Hu. lia.
    + rewrite Hrows. unfold ZSimpleGraph.vertex_valid in Hu. lia.
    + rewrite Hrows. unfold ZSimpleGraph.vertex_valid in Hu. lia.
  - rewrite Zlength_correct. rewrite Nat2Z.id. reflexivity.
Qed.
