Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.micromega.Lia.
Require Import SetsClass.SetsClass.
From RecordUpdate Require Import RecordUpdate.
From AUXLib Require Import ListLib.
From MonadLib Require Import MonadLib.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelMonad.
From MaxMinLib Require Import MaxMin Interface.
From GraphLib Require Import graph_basic reachable_basic path path_basic epath Zweight dijkstra.
Require Import Algorithms.Dijkstra.Dijkstra.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
From SimpleC.EE.LLM_bench.Algorithms.Dijkstra Require Export concrete_graphs.

Import ListNotations.
Import SetsNotation.
Import MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope monad.
Import naive_C_Rules.
Local Open Scope sac.

Ltac dijkstra_cleanup :=
  intros;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : exists _, _ |- _ => destruct H
  | H : False |- _ => contradiction
  | H : Some _ = Some _ |- _ => inversion H; clear H; subst
  | H : (_, _) = (_, _) |- _ => inversion H; clear H; subst
  end;
  subst; simpl in *; try contradiction; try discriminate;
  try tauto; try lia; eauto.

Module DijkstraLinkedForwardStar.

Definition state : Type := @St Z.

#[local] Existing Instance DijkstraGraph.weight_instance.

Notation dijkstra_step_aux := (@step_aux DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance).
Notation dijkstra_weight := (@weight DijkstraGraph.G DijkstraGraph.E DijkstraGraph.weight_instance).
Notation dijkstra_valid_epath := (@valid_epath DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance).
Notation dijkstra_epath_weight := (@epath_weight DijkstraGraph.G DijkstraGraph.E DijkstraGraph.weight_instance).
Notation dijkstra_is_epath_through_vset := (@is_epath_through_vset DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance).
Notation dijkstra_reachable := (@reachable DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance).
Notation dijkstra_min_epath := (@min_value_weight_epath DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.weight_instance).
Notation dijkstra_min_epath_in_vset := (@min_value_weight_epath_in_vset DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.weight_instance).

Definition shortest_path_relaxation_bounded
    (g : DijkstraGraph.G) (src bound : Z) : Prop :=
  @GraphLib.reachable.epath.shortest_path_relaxation_bounded
    DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E
    DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance
    DijkstraGraph.PathData DijkstraGraph.path_instance
    DijkstraGraph.weight_instance
    g src bound.

Notation dijkstra_visited_dist_final := (fun g src s => @visited_dist_final DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance g DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.weight_instance src s).
Notation dijkstra_unvisited_dist_optimal := (fun g src s => @unvisited_dist_optimal DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance g DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.weight_instance src s).

Notation dijkstra_visited_le_unvisited := (@visited_le_unvisited Z).

Notation dijkstra_first_step_invariant := (fun g src done s => @Dijkstra.first_step_invariant DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance g DijkstraGraph.weight_instance src done s).
Notation dijkstra_relax_step_invariant := (fun g cur_vertex s0 done s => @Dijkstra.relax_step_invariant DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance g DijkstraGraph.weight_instance cur_vertex s0 done s).

Definition initial_state (src : Z) : state :=
  @initSt Z DijkstraGraph.vertex_eqdec src.

Notation dijkstra_distance_correct := (fun g src s => @distance_correct DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance g DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.weight_instance src s).
Notation dijkstra_valid_epath_cons_inv := (@valid_epath_cons_inv DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.empty_path_instance DijkstraGraph.single_path_instance DijkstraGraph.concat_path_instance DijkstraGraph.destruct1n_path_instance).
Notation dijkstra_valid_epath_nil_inv := (@valid_epath_nil_inv DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance).
Notation dijkstra_valid_epath_inv_n1 := (@valid_epath_inv_n1 DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.empty_path_instance DijkstraGraph.single_path_instance DijkstraGraph.concat_path_instance DijkstraGraph.destruct1n_path_instance).
Notation dijkstra_reachable_valid_epath := (@reachable_valid_epath DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.empty_path_instance DijkstraGraph.single_path_instance DijkstraGraph.concat_path_instance).
Notation dijkstra_valid_epath_reachable := (@valid_epath_reachable DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.empty_path_instance DijkstraGraph.single_path_instance DijkstraGraph.concat_path_instance DijkstraGraph.destruct1n_path_instance).
Notation dijkstra_is_epath_through_vset_single := (@is_epath_through_vset_single DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.single_path_instance).
Notation dijkstra_is_epath_through_vset_subset := (@is_epath_through_vset_subset DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance).

Notation dijkstra_is_epath_through_vset_greedy_cut := (fun g Hwf u p v S Hpath Hunvisited => @is_epath_through_vset_greedy_cut DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.empty_path_instance DijkstraGraph.single_path_instance DijkstraGraph.concat_path_instance DijkstraGraph.destruct1n_path_instance DijkstraGraph.stepunique_instance g Hwf u p v S Hpath Hunvisited).
Notation dijkstra_greedy_choice_correct := (fun g Hwf src Hnonneg u S dist => @dijkstra.dijkstra_greedy_choice_correct DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.stepunique_instance g Hwf DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.empty_path_instance DijkstraGraph.single_path_instance DijkstraGraph.concat_path_instance DijkstraGraph.destruct1n_path_instance DijkstraGraph.weight_instance src Hnonneg u S dist).
Notation dijkstra_visited_keep := (fun g src u v S e dist => @dijkstra.dijkstra_visited_keep DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance g DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.single_path_instance DijkstraGraph.concat_path_instance DijkstraGraph.weight_instance src u v S e dist).
Notation dijkstra_invariant_implies_final := (fun g Hwf src Hnonneg cur_vertex s0 s1 => @Dijkstra.invariant_implies_final DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.stepunique_instance DijkstraGraph.simple_graph_instance g Hwf DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.empty_path_instance DijkstraGraph.single_path_instance DijkstraGraph.concat_path_instance DijkstraGraph.destruct1n_path_instance DijkstraGraph.weight_instance src Hnonneg cur_vertex s0 s1).

Definition storage_index (i : Z) : Prop :=
  0 <= i < DijkstraGraph.max_vertices.

Definition max_priority_queue_size : Z := 200005.

Definition edge_index (edge_count i : Z) : Prop :=
  0 <= i < edge_count.

Definition dist_cell (values : list Z) (v : Z) : Z :=
  Znth v values DijkstraGraph.infinity.

Definition distance_as_cell (d : option Z) : Z :=
  DijkstraGraph.distance_as_cell d.

Definition cell_as_distance (x : Z) : option Z :=
  DijkstraGraph.cell_as_distance x.

Definition vector_shape (values : list Z) : Prop :=
  Zlength values = DijkstraGraph.max_vertices.

Definition dist_values_safe (values : list Z) : Prop :=
  forall v, storage_index v ->
    0 <= dist_cell values v <= DijkstraGraph.infinity.

Definition dist_init_loop (i : Z) (values : list Z) : Prop :=
  vector_shape values /\
  0 <= i <= DijkstraGraph.max_vertices /\
  forall v,
    storage_index v ->
    v < i ->
    dist_cell values v = DijkstraGraph.infinity.

Definition graph_has_size (g : DijkstraGraph.G) (n : Z) : Prop :=
  DijkstraGraph.vertex_count g = n /\
  0 <= n <= DijkstraGraph.max_vertices.

Lemma graph_has_size_bounds :
  forall g n,
    graph_has_size g n ->
    0 <= n <= DijkstraGraph.max_vertices.
Proof. unfold graph_has_size; tauto. Qed.

Definition vertex_valid (g : DijkstraGraph.G) (v : Z) : Prop :=
  DijkstraGraph.vertex_valid g v.

Ltac dijkstra_bounds_cleanup :=
  unfold graph_has_size, vertex_valid, DijkstraGraph.vertex_valid,
    storage_index, edge_index, vector_shape, dist_values_safe in *;
  dijkstra_cleanup.

Ltac dijkstra_storage_bounds :=
  rewrite ?Zlength_replace_Znth, ?Zlength_correct, ?repeat_length in *;
  unfold storage_index, vector_shape, DijkstraGraph.max_vertices in *;
  lia.

Lemma graph_has_size_vertex_valid_bounds :
  forall g n v,
    graph_has_size g n ->
    vertex_valid g v ->
    0 < n <= DijkstraGraph.max_vertices /\
    0 <= v < n.
Proof. dijkstra_bounds_cleanup. Qed.

Lemma graph_has_size_vertex_valid_storage :
  forall g n v,
    graph_has_size g n ->
    vertex_valid g v ->
    storage_index v.
Proof. dijkstra_bounds_cleanup. Qed.

Inductive next_chain (next_values : list Z) : Z -> Z -> Prop :=
| next_chain_here : forall e,
    0 <= e < Zlength next_values ->
    next_chain next_values e e
| next_chain_next : forall cur e,
    0 <= cur < Zlength next_values ->
    Znth cur next_values (-1) <> -1 ->
    next_chain next_values (Znth cur next_values (-1)) e ->
    next_chain next_values cur e.

Definition forward_star_edge
  (head_values to_values weight_values next_values : list Z)
  (u v w : Z) : Prop :=
  storage_index u /\
  exists e,
    next_chain next_values (Znth u head_values (-1)) e /\
    0 <= e < Zlength to_values /\
    Znth e to_values 0 = v /\
    Znth e weight_values 0 = w.

Definition edge_values_safe
    (vertex_count edge_count : Z)
    (to_values weight_values next_values : list Z) : Prop :=
  Zlength to_values = edge_count /\
  Zlength weight_values = edge_count /\
  Zlength next_values = edge_count /\
  forall e,
    edge_index edge_count e ->
    0 <= Znth e to_values 0 < vertex_count /\
    storage_index (Znth e to_values 0) /\
    0 <= Znth e weight_values 0 <= DijkstraGraph.infinity /\
    (Znth e next_values (-1) = -1 \/
      edge_index edge_count (Znth e next_values (-1))).

Definition head_values_safe
    (vertex_count edge_count : Z) (head_values : list Z) : Prop :=
  Zlength head_values = vertex_count /\
  forall u,
    0 <= u < vertex_count ->
    Znth u head_values (-1) = -1 \/
    edge_index edge_count (Znth u head_values (-1)).

Definition forward_star_chain_wf
    (head_values to_values next_values : list Z) : Prop :=
  (forall edge,
    0 <= edge < Zlength next_values ->
    Znth edge next_values (-1) <> -1 ->
    ~ next_chain next_values (Znth edge next_values (-1)) edge) /\
  (forall u i j,
    storage_index u ->
    next_chain next_values (Znth u head_values (-1)) i ->
    next_chain next_values (Znth u head_values (-1)) j ->
    0 <= i < Zlength to_values ->
    0 <= j < Zlength to_values ->
    Znth i to_values 0 = Znth j to_values 0 ->
    i = j) /\
  forall u edge,
    storage_index u ->
    Znth u head_values (-1) <> -1 ->
    next_chain next_values (Znth u head_values (-1)) edge ->
    0 <= edge < Zlength next_values.

Definition forward_star_model
    (g : DijkstraGraph.G) (edge_count : Z)
    (head_values to_values weight_values next_values : list Z) : Prop :=
  DijkstraGraph.graph_wf g /\
  graph_has_size g (Zlength head_values) /\
  0 <= edge_count <= max_priority_queue_size /\
  head_values_safe (DijkstraGraph.vertex_count g) edge_count head_values /\
  edge_values_safe
    (DijkstraGraph.vertex_count g) edge_count
    to_values weight_values next_values /\
  (forall u v w,
    vertex_valid g u ->
    vertex_valid g v ->
    (DijkstraGraph.edge_weight g u v = Some w <->
      forward_star_edge head_values to_values weight_values next_values
        u v w)) /\
  (forall u v w1 w2,
    forward_star_edge head_values to_values weight_values next_values
      u v w1 ->
    forward_star_edge head_values to_values weight_values next_values
      u v w2 ->
    w1 = w2) /\
  forward_star_chain_wf head_values to_values next_values.

Module GraphForwardStar.

Definition store_graph
    (g : DijkstraGraph.G) (edge_count : Z)
    (head to weight next : addr) : Assertion :=
  EX head_values : list Z,
  EX to_values : list Z,
  EX weight_values : list Z,
  EX next_values : list Z,
    “ forward_star_model
        g edge_count head_values to_values weight_values next_values ” &&
    IntArray.full head (DijkstraGraph.vertex_count g) head_values **
    IntArray.full to edge_count to_values **
    IntArray.full weight edge_count weight_values **
    IntArray.full next edge_count next_values.

Lemma store_graph_elim :
  forall g edge_count head to weight next,
    store_graph g edge_count head to weight next |--
    EX head_values : list Z,
    EX to_values : list Z,
    EX weight_values : list Z,
    EX next_values : list Z,
      “ forward_star_model
          g edge_count head_values to_values weight_values next_values ” &&
      IntArray.full head (DijkstraGraph.vertex_count g) head_values **
      IntArray.full to edge_count to_values **
      IntArray.full weight edge_count weight_values **
      IntArray.full next edge_count next_values.
Proof.
  intros.
  unfold store_graph.
  normalize.
  cancel.
Qed.

Lemma store_graph_elim_with_size :
  forall g vertex_count edge_count head to weight next,
    graph_has_size g vertex_count ->
    store_graph g edge_count head to weight next |--
    EX head_values : list Z,
    EX to_values : list Z,
    EX weight_values : list Z,
    EX next_values : list Z,
      “ forward_star_model
          g edge_count head_values to_values weight_values next_values ” &&
      IntArray.full head vertex_count head_values **
      IntArray.full to edge_count to_values **
      IntArray.full weight edge_count weight_values **
      IntArray.full next edge_count next_values.
Proof.
  intros.
  unfold store_graph.
  destruct H as [Hvertex_count _].
  rewrite Hvertex_count.
  normalize.
  cancel.
Qed.

Lemma store_graph_intro :
  forall g edge_count head to weight next
         head_values to_values weight_values next_values,
    forward_star_model
      g edge_count head_values to_values weight_values next_values ->
    IntArray.full head (DijkstraGraph.vertex_count g) head_values **
    IntArray.full to edge_count to_values **
    IntArray.full weight edge_count weight_values **
    IntArray.full next edge_count next_values |--
    store_graph g edge_count head to weight next.
Proof.
  intros.
  unfold store_graph.
  Exists head_values to_values weight_values next_values.
  normalize.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    exact H.
Qed.

Lemma store_graph_intro_with_size :
  forall g vertex_count edge_count head to weight next
         head_values to_values weight_values next_values,
    graph_has_size g vertex_count ->
    forward_star_model
      g edge_count head_values to_values weight_values next_values ->
    IntArray.full head vertex_count head_values **
    IntArray.full to edge_count to_values **
    IntArray.full weight edge_count weight_values **
    IntArray.full next edge_count next_values |--
    store_graph g edge_count head to weight next.
Proof.
  intros.
  unfold store_graph.
  Exists head_values to_values weight_values next_values.
  destruct H as [Hvertex_count _].
  rewrite Hvertex_count.
  normalize.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    exact H0.
Qed.

End GraphForwardStar.

Lemma forward_star_model_chain_wf :
  forall g edge_count head_values to_values weight_values next_values,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    forward_star_chain_wf head_values to_values next_values.
Proof. unfold forward_star_model; dijkstra_cleanup. Qed.

Lemma forward_star_model_graph_wf :
  forall g edge_count head_values to_values weight_values next_values,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    DijkstraGraph.graph_wf g.
Proof. unfold forward_star_model; dijkstra_cleanup. Qed.

Lemma forward_star_model_head_safe :
  forall g edge_count head_values to_values weight_values next_values,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    head_values_safe
      (DijkstraGraph.vertex_count g) edge_count head_values.
Proof. unfold forward_star_model; dijkstra_cleanup. Qed.

Lemma forward_star_model_edge_safe :
  forall g edge_count head_values to_values weight_values next_values,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_values_safe
      (DijkstraGraph.vertex_count g) edge_count
      to_values weight_values next_values.
Proof. unfold forward_star_model; dijkstra_cleanup. Qed.

Lemma forward_star_model_edge_iff :
  forall g edge_count head_values to_values weight_values next_values,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    forall u v w,
      vertex_valid g u ->
      vertex_valid g v ->
      (DijkstraGraph.edge_weight g u v = Some w <->
        forward_star_edge head_values to_values weight_values next_values
          u v w).
Proof. unfold forward_star_model; dijkstra_cleanup. Qed.

Definition graph_dist_model
    (g : DijkstraGraph.G) (dist_values : list Z) (s : state) : Prop :=
  vector_shape dist_values /\
  dist_values_safe dist_values /\
  forall v,
    vertex_valid g v ->
    dist_cell dist_values v = distance_as_cell (@dist Z s v).

Definition visited_set_empty (visited_set : Z -> Prop) : Prop :=
  forall v, ~ visited_set v.

Definition visited_set_add
    (visited_set : Z -> Prop) (u : Z) (visited_set' : Z -> Prop) : Prop :=
  forall v, visited_set' v <-> visited_set v \/ v = u.

Definition visited_set_valid
    (g : DijkstraGraph.G) (visited_set : Z -> Prop) : Prop :=
  forall v, visited_set v -> vertex_valid g v.

Definition graph_state_invalid_default
    (g : DijkstraGraph.G) (s : state) : Prop :=
  forall v,
    ~ vertex_valid g v ->
    @dist Z s v = None /\ ~ @visited Z s v.

Definition graph_state_model
    (g : DijkstraGraph.G) (visited_set : Z -> Prop)
    (dist_values : list Z) (s : state) : Prop :=
  graph_dist_model g dist_values s /\
  (forall v,
    vertex_valid g v ->
    (visited_set v <-> @visited Z s v)) /\
  graph_state_invalid_default g s.

Definition set_state_visited (u : Z) (s : state) : state :=
  s <| visited ::= fun vs => vs ∪ [u] |>.

Definition dijkstra_init_dist
    (vertex_count src : Z) (dist_values : list Z) : Prop :=
  vector_shape dist_values /\
  dist_values_safe dist_values /\
  0 < vertex_count <= DijkstraGraph.max_vertices /\
  0 <= src < vertex_count /\
  forall v,
    0 <= v < vertex_count ->
    dist_cell dist_values v =
      if Z.eq_dec v src then 0 else DijkstraGraph.infinity.

Definition initial_dist_values (src : Z) : list Z :=
  replace_Znth src 0
    (repeat DijkstraGraph.infinity
      (Z.to_nat DijkstraGraph.max_vertices)).

Lemma initial_dist_values_shape :
  forall src,
    storage_index src ->
    vector_shape (initial_dist_values src).
Proof.
  intros src Hsrc; unfold initial_dist_values, vector_shape; dijkstra_storage_bounds.
Qed.

Lemma initial_dist_values_cell :
  forall src v,
    storage_index src ->
    storage_index v ->
    dist_cell (initial_dist_values src) v =
      if Z.eq_dec v src then 0 else DijkstraGraph.infinity.
Proof.
  intros src v Hsrc Hv.
  unfold initial_dist_values, dist_cell.
  destruct (Z.eq_dec v src) as [Heq | Hne].
  - subst; rewrite Znth_replace_Znth_Same by dijkstra_storage_bounds;
      destruct (Z.eq_dec src src); congruence.
  - rewrite Znth_replace_Znth_Diff, Znth_repeat by dijkstra_storage_bounds;
      destruct (Z.eq_dec v src); congruence.
Qed.

Lemma initial_dist_values_safe :
  forall src,
    storage_index src ->
    dist_values_safe (initial_dist_values src).
Proof.
  intros src Hsrc v Hv.
  rewrite initial_dist_values_cell by auto.
  destruct (Z.eq_dec v src); unfold DijkstraGraph.infinity; lia.
Qed.

Lemma initial_dist_values_init :
  forall vertex_count src,
    0 < vertex_count <= DijkstraGraph.max_vertices ->
    0 <= src < vertex_count ->
    dijkstra_init_dist vertex_count src (initial_dist_values src).
Proof.
  intros vertex_count src Hcount Hsrc.
  assert (Hstorage_src : storage_index src) by (unfold storage_index; lia).
  unfold dijkstra_init_dist.
  split; [apply initial_dist_values_shape; exact Hstorage_src |].
  split; [apply initial_dist_values_safe; exact Hstorage_src |].
  do 2 (split; [lia |]).
  intros v0 Hv0; rewrite initial_dist_values_cell;
    [reflexivity | exact Hstorage_src | unfold storage_index; lia].
Qed.

Lemma dist_init_loop_start :
  forall values,
    vector_shape values ->
    dist_init_loop 0 values.
Proof.
  intros values Hshape; unfold dist_init_loop.
  repeat split; auto; unfold storage_index, DijkstraGraph.max_vertices in *; lia.
Qed.

Lemma dist_init_loop_step :
  forall i values,
    i < DijkstraGraph.max_vertices ->
    dist_init_loop i values ->
    dist_init_loop
      (i + 1)
      (replace_Znth i DijkstraGraph.infinity values).
Proof.
  intros i values Hi Hloop.
  unfold dist_init_loop in *.
  destruct Hloop as (Hshape & Hrange & Hall).
  split.
  - unfold vector_shape in *; rewrite Zlength_replace_Znth; exact Hshape.
  - split.
    + lia.
    + intros v Hv Hvlt.
      unfold storage_index in Hv.
      unfold dist_cell.
      destruct (Z.eq_dec v i) as [Heq | Hne].
      * subst; rewrite Znth_replace_Znth_Same by dijkstra_bounds_cleanup; reflexivity.
      * rewrite Znth_replace_Znth_Diff by dijkstra_bounds_cleanup.
        apply Hall; unfold storage_index; lia.
Qed.

Lemma dist_init_loop_replace_source_cell :
  forall src values v,
    storage_index src ->
    storage_index v ->
    dist_init_loop DijkstraGraph.max_vertices values ->
    dist_cell (replace_Znth src 0 values) v =
      if Z.eq_dec v src then 0 else DijkstraGraph.infinity.
Proof.
  intros src values v Hsrc Hv Hloop.
  unfold dist_init_loop in Hloop.
  destruct Hloop as (Hshape & _ & Hall).
  unfold dist_cell.
  destruct (Z.eq_dec v src) as [Heq | Hne].
  - subst; rewrite Znth_replace_Znth_Same by dijkstra_bounds_cleanup;
      destruct (Z.eq_dec src src); congruence.
  - rewrite Znth_replace_Znth_Diff by dijkstra_bounds_cleanup.
    pose proof (Hall v Hv ltac:(unfold storage_index in Hv; lia)) as Hinf.
    unfold dist_cell in Hinf; rewrite Hinf.
    destruct (Z.eq_dec v src); congruence.
Qed.

Lemma dist_init_loop_to_dijkstra_init_dist :
	forall vertex_count src values,
	  0 < vertex_count <= DijkstraGraph.max_vertices ->
	  0 <= src < vertex_count ->
	  dist_init_loop DijkstraGraph.max_vertices values ->
	  dijkstra_init_dist
	    vertex_count src (replace_Znth src 0 values).
Proof.
  intros vertex_count src values Hcount Hsrc Hloop.
  assert (Hsrc_storage : storage_index src) by (unfold storage_index; lia).
  pose proof Hloop as (Hshape & _ & _).
  unfold dijkstra_init_dist.
  split.
  - unfold vector_shape in *.
    rewrite Zlength_replace_Znth.
    exact Hshape.
  - split.
    + unfold dist_values_safe.
      intros v Hv.
      rewrite dist_init_loop_replace_source_cell by auto.
      destruct (Z.eq_dec v src); unfold DijkstraGraph.infinity; lia.
    + split; [lia |].
      split; [lia |].
      intros v Hv.
      rewrite dist_init_loop_replace_source_cell;
        [reflexivity | exact Hsrc_storage | unfold storage_index; lia | exact Hloop].
Qed.

Definition dijkstra_shortest_dist
    (g : DijkstraGraph.G) (src : Z) (dist_values : list Z) : Prop :=
  exists s : state,
    graph_dist_model g dist_values s /\
    dijkstra_distance_correct g src s.

Fixpoint priority_queue_ordered (items : list (Z * Z)) : Prop :=
  match items with
  | nil => True
  | item :: items_tail =>
      (forall item0, In item0 items_tail -> fst item <= fst item0) /\
      priority_queue_ordered items_tail
  end.

Definition priority_queue_refines_unvisited_dist
    (g : DijkstraGraph.G) (visited_set : Z -> Prop)
    (dist_values : list Z) (items : list (Z * Z)) : Prop :=
  (forall v,
    vertex_valid g v ->
    ~ visited_set v ->
    dist_cell dist_values v < DijkstraGraph.infinity ->
    In (dist_cell dist_values v, v) items) /\
  (forall d v,
    In (d, v) items ->
    d = dist_cell dist_values v ->
    ~ visited_set v) /\
  (forall d v,
    In (d, v) items ->
    dist_cell dist_values v <= d) /\
  (forall d v, In (d, v) items -> d < DijkstraGraph.infinity) /\
  NoDup items.

Definition priority_queue_vertices_valid
    (g : DijkstraGraph.G) (items : list (Z * Z)) : Prop :=
  forall item,
    In item items ->
    vertex_valid g (snd item).

(** Basic loop-state predicates.

    These are intentionally placed immediately after the graph/dist/queue
    models they depend on.  They are lightweight safety and bridge states used
    by generated VCs before the later shortest-path mathematics enters. *)

Definition dijkstra_loop_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z)
    (queue_items : list (Z * Z)) : Prop :=
  DijkstraGraph.graph_wf g /\
  vertex_valid g src /\
  nonnegative_edges g /\
  vector_shape dist_values /\
  dist_values_safe dist_values /\
  priority_queue_ordered queue_items /\
  priority_queue_vertices_valid g queue_items.

Definition dijkstra_loop_bridge_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (queue_items : list (Z * Z)) : Prop :=
  dijkstra_loop_state g src visited_set dist_values queue_items /\
  priority_queue_refines_unvisited_dist g visited_set dist_values queue_items.

Definition state_distance_cell (v : Z) (s : state) : Z :=
  distance_as_cell (@dist Z s v).

Lemma initial_state_source_distance_cell :
  forall src,
    state_distance_cell src (initial_state src) = 0.
Proof.
  intros src.
  unfold state_distance_cell, initial_state, distance_as_cell.
  simpl.
  destruct (DijkstraGraph.vertex_eqdec src src) as [_ | Hcontra].
  - reflexivity.
  - contradiction Hcontra. reflexivity.
Qed.

Definition set_state_distance (v distance : Z) (s : state) : state :=
  @mkSt Z
    (@visited Z s)
    (fun u =>
      if Z.eq_dec u v then cell_as_distance distance else @dist Z s u).

Lemma distance_as_cell_cell_as_distance_safe :
  forall x,
    0 <= x <= DijkstraGraph.infinity ->
    distance_as_cell (cell_as_distance x) = x.
Proof.
  intros x Hx; unfold distance_as_cell, cell_as_distance,
    DijkstraGraph.distance_as_cell, DijkstraGraph.cell_as_distance;
    destruct (Z.eq_dec x DijkstraGraph.infinity); subst; reflexivity.
Qed.

Lemma graph_state_model_dist_cell :
  forall g visited_set dist_values s v,
    graph_state_model g visited_set dist_values s ->
    vertex_valid g v ->
    state_distance_cell v s = dist_cell dist_values v.
Proof.
  intros g visited_set dist_values s v ((_ & _ & Hcells) & _) Hvalid.
  unfold state_distance_cell; symmetry; auto.
Qed.

Lemma dist_values_safe_replace_Znth :
  forall dist_values v candidate,
    vector_shape dist_values ->
    dist_values_safe dist_values ->
    storage_index v ->
    0 <= candidate < DijkstraGraph.infinity ->
    dist_values_safe (replace_Znth v candidate dist_values).
Proof.
  intros dist_values v candidate Hshape Hsafe Hstorage Hcandidate u Hu.
  unfold dist_values_safe, dist_cell in *.
  destruct (Z.eq_dec u v) as [-> | Hne].
  - rewrite Znth_replace_Znth_Same by dijkstra_bounds_cleanup; lia.
  - rewrite Znth_replace_Znth_Diff by dijkstra_bounds_cleanup; auto.
Qed.

Lemma dijkstra_init_dist_graph_state_model_initial :
  forall g vertex_count src visited_set dist_values,
    graph_has_size g vertex_count ->
    visited_set_empty visited_set ->
    dijkstra_init_dist vertex_count src dist_values ->
    graph_state_model g visited_set dist_values (initial_state src).
Proof.
  intros g vertex_count src visited_set dist_values Hsize Hempty Hinit.
  unfold graph_state_model.
  split.
  - pose proof Hinit as Hinit_dist.
    unfold graph_dist_model, dijkstra_init_dist in Hinit_dist.
    destruct Hinit_dist as (Hshape & Hsafe & Hcount & Hsrc & Hcells).
    do 2 (split; [eassumption |]).
    intros v Hvalid.
    pose proof Hsize as Hsize_copy.
    unfold graph_has_size in Hsize_copy.
    destruct Hsize_copy as (Hvertex_count & _).
    unfold vertex_valid, DijkstraGraph.vertex_valid in Hvalid.
    rewrite Hvertex_count in Hvalid.
    specialize (Hcells v Hvalid).
    unfold initial_state; simpl.
    rewrite Hcells.
    destruct (Z.eq_dec v src) as [Heq | Hne].
    + subst v.
      destruct (DijkstraGraph.vertex_eqdec src src) as [_ | Hcontra].
      * reflexivity.
      * exfalso; apply Hcontra; reflexivity.
    + destruct (DijkstraGraph.vertex_eqdec v src) as [Heq | _].
      * contradiction Hne.
      * reflexivity.
  - split.
    + intros v Hvalid; split; intro Hvisited;
        [exfalso; apply (Hempty v); exact Hvisited
        | unfold initial_state in Hvisited; simpl in Hvisited; contradiction].
    + unfold graph_state_invalid_default.
      intros v Hnot_valid.
      split.
      * unfold initial_state; simpl.
        destruct (Z.eq_dec v src) as [Heq | Hne].
        -- subst; exfalso; apply Hnot_valid.
           unfold dijkstra_init_dist in Hinit.
           unfold graph_has_size in Hsize.
           unfold vertex_valid, DijkstraGraph.vertex_valid; lia.
        -- destruct (DijkstraGraph.vertex_eqdec v src) as [Heq | _];
             [contradiction | reflexivity].
      * unfold initial_state; simpl; intros [].
Qed.

Lemma graph_state_model_to_graph_dist_model :
  forall g visited_set dist_values s,
    graph_state_model g visited_set dist_values s ->
    graph_dist_model g dist_values s.
Proof. unfold graph_state_model; tauto. Qed.

Lemma graph_state_model_visit_state :
  forall g visited_set visited_set' dist_values s u,
    vertex_valid g u ->
    visited_set_add visited_set u visited_set' ->
    graph_state_model g visited_set dist_values s ->
    graph_state_model g visited_set' dist_values (set_state_visited u s).
Proof.
  intros g visited_set visited_set' dist_values s u Hu Hadd Hmodel.
  destruct Hmodel as (Hdist & Hvisited & Hinvalid).
  unfold graph_state_model.
  split.
  - exact Hdist.
  - split.
    + intros v Hvalid.
      unfold set_state_visited; simpl.
      rewrite (Hadd v); sets_unfold.
      rewrite <- (Hvisited v Hvalid).
      split; intros [Hv | Heq];
        [left; exact Hv | right; symmetry; exact Heq
        | left; exact Hv | right; symmetry; exact Heq].
    + unfold graph_state_invalid_default in *.
      intros v Hnot_valid.
      specialize (Hinvalid v Hnot_valid) as (Hdist_none & Hnot_visited).
      unfold set_state_visited; simpl.
      split; [exact Hdist_none |].
      intros [Hvisited_v | ->]; [apply Hnot_visited | contradiction]; auto.
Qed.

Lemma graph_state_model_replace_Znth_set_state_distance :
  forall g vertex_count visited_set dist_values s v candidate,
    graph_has_size g vertex_count ->
    graph_state_model g visited_set dist_values s ->
    vertex_valid g v ->
    storage_index v ->
    0 <= candidate < DijkstraGraph.infinity ->
    graph_state_model g visited_set
      (replace_Znth v candidate dist_values)
      (set_state_distance v candidate s).
Proof.
  intros g vertex_count visited_set dist_values s v candidate
    Hsize Hmodel Hvalid Hstorage Hcandidate.
  destruct Hmodel as (Hdist & Hvisited & Hinvalid).
  unfold graph_state_model in *.
  split.
  - unfold graph_dist_model.
    destruct Hdist as (Hshape & Hsafe & Hcells).
    split.
    + unfold vector_shape in *; rewrite Zlength_replace_Znth; exact Hshape.
    + split.
      * eapply dist_values_safe_replace_Znth; eauto.
      * intros u Hu.
        unfold dist_cell, set_state_distance, state_distance_cell.
        simpl.
        destruct (Z.eq_dec u v) as [Heq | Hne].
        -- subst.
           rewrite Znth_replace_Znth_Same by dijkstra_bounds_cleanup.
           symmetry; apply distance_as_cell_cell_as_distance_safe; lia.
        -- rewrite Znth_replace_Znth_Diff by dijkstra_bounds_cleanup.
           destruct (Z.eq_dec u v) as [Hcontra | _]; [contradiction |].
           apply Hcells. exact Hu.
  - split.
    + intros u Hu; unfold set_state_distance; simpl; exact (Hvisited u Hu).
    + unfold graph_state_invalid_default in *.
      intros u Hnot_valid.
      specialize (Hinvalid u Hnot_valid) as (Hdist_none & Hnot_visited).
      unfold set_state_distance; simpl.
      split.
      * destruct (Z.eq_dec u v) as [-> | _]; [contradiction | exact Hdist_none].
      * exact Hnot_visited.
Qed.

Lemma hs_eval_assume_state :
  forall (P Q : state -> Prop),
    (forall s, P s -> Q s) ->
    P -@ assume Q -⥅ P ♯ tt.
Proof.
  unfold hs_eval, test.
  intros P Q HPQ s HP.
  exists s.
  split; auto.
Qed.

Ltac lfs_prog_nf H := repeat (prog_nf in H).

Ltac lfs_finish_equiv :=
  repeat (rewrite bind_assoc || rewrite ret_equiv || rewrite ret_equiv');
  reflexivity.

Definition vertex_valid_dec
    (g : DijkstraGraph.G) (v : Z) : {vertex_valid g v} + {~ vertex_valid g v}.
Proof.
  unfold vertex_valid, DijkstraGraph.vertex_valid.
  destruct (Z_le_dec 0 v) as [Hlo | Hlo].
  - destruct (Z_lt_dec v (DijkstraGraph.vertex_count g)) as [Hhi | Hhi].
    + left. lia.
    + right. lia.
  - right. lia.
Defined.

Lemma cell_as_distance_finite :
  forall x,
    0 <= x < DijkstraGraph.infinity ->
    cell_as_distance x = Some x.
Proof.
  intros x Hx.
  unfold cell_as_distance, DijkstraGraph.cell_as_distance.
  destruct (Z.eq_dec x DijkstraGraph.infinity) as [Heq | Hne].
  - subst. lia.
  - reflexivity.
Qed.

Definition dijkstra_array_state
    (g : DijkstraGraph.G) (visited_set : Z -> Prop)
    (dist_values : list Z) : state :=
  @mkSt Z
    (fun v => vertex_valid g v /\ visited_set v)
    (fun v =>
      if vertex_valid_dec g v
      then cell_as_distance (dist_cell dist_values v)
      else None).

Lemma dijkstra_array_state_dist_valid :
  forall g visited_set dist_values v,
    vertex_valid g v ->
    @dist Z (dijkstra_array_state g visited_set dist_values) v =
      cell_as_distance (dist_cell dist_values v).
Proof.
  intros g visited_set dist_values v Hvalid.
  unfold dijkstra_array_state.
  simpl.
  destruct (vertex_valid_dec g v) as [_ | Hinvalid].
  - reflexivity.
  - contradiction.
Qed.

Lemma dijkstra_array_state_visited_iff :
  forall g visited_set dist_values v,
    @visited Z (dijkstra_array_state g visited_set dist_values) v <->
    vertex_valid g v /\ visited_set v.
Proof. reflexivity. Qed.

Lemma dijkstra_array_state_dist_invalid :
  forall g visited_set dist_values v,
    ~ vertex_valid g v ->
    @dist Z (dijkstra_array_state g visited_set dist_values) v = None.
Proof.
  intros g visited_set dist_values v Hinvalid.
  unfold dijkstra_array_state; simpl.
  destruct (vertex_valid_dec g v); [contradiction | reflexivity].
Qed.

Lemma dijkstra_array_state_dist_replace_same :
  forall g vertex_count visited_set dist_values v candidate,
    graph_has_size g vertex_count ->
    vector_shape dist_values ->
    vertex_valid g v ->
    storage_index v ->
    0 <= candidate < DijkstraGraph.infinity ->
    @dist Z
      (dijkstra_array_state g visited_set
        (replace_Znth v candidate dist_values)) v =
      Some candidate.
Proof.
  intros g vertex_count visited_set dist_values v candidate
    Hsize Hshape Hvalid Hstorage Hcandidate.
  rewrite dijkstra_array_state_dist_valid by exact Hvalid.
  unfold dist_cell.
  rewrite Znth_replace_Znth_Same by dijkstra_bounds_cleanup.
  apply cell_as_distance_finite; exact Hcandidate.
Qed.

Lemma dijkstra_array_state_dist_replace_other :
  forall g vertex_count visited_set dist_values v u candidate,
    graph_has_size g vertex_count ->
    vector_shape dist_values ->
    storage_index v ->
    u <> v ->
    @dist Z
      (dijkstra_array_state g visited_set
        (replace_Znth v candidate dist_values)) u =
      @dist Z (dijkstra_array_state g visited_set dist_values) u.
Proof.
  intros g vertex_count visited_set dist_values v u candidate
    Hsize Hshape Hv_storage Hneq.
  destruct (vertex_valid_dec g u) as [Hu_valid | Hu_invalid].
  - pose proof
      (graph_has_size_vertex_valid_storage _ _ _ Hsize Hu_valid)
      as Hu_storage.
    rewrite !dijkstra_array_state_dist_valid by exact Hu_valid.
    unfold dist_cell.
    rewrite Znth_replace_Znth_Diff by dijkstra_bounds_cleanup.
    reflexivity.
  - rewrite !dijkstra_array_state_dist_invalid by exact Hu_invalid.
    reflexivity.
Qed.

Ltac dijkstra_min_epath_refl :=
  eapply (@min_value_weight_epath_refl DijkstraGraph.G DijkstraGraph.V
    DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance
    _ DijkstraGraph.PathData DijkstraGraph.path_instance
    DijkstraGraph.empty_path_instance DijkstraGraph.single_path_instance
    DijkstraGraph.concat_path_instance DijkstraGraph.destruct1n_path_instance
    DijkstraGraph.weight_instance); eauto.

Definition dijkstra_math_invariant
    (g : DijkstraGraph.G) (src : Z)
    (visited_set : Z -> Prop) (dist_values : list Z) : Prop :=
  dijkstra_visited_dist_final g src
    (dijkstra_array_state g visited_set dist_values) /\
  dijkstra_unvisited_dist_optimal g src
    (dijkstra_array_state g visited_set dist_values) /\
  dijkstra_visited_le_unvisited
    (dijkstra_array_state g visited_set dist_values).

Lemma dijkstra_valid_epath_non_neg :
  forall g u p v,
    nonnegative_edges g ->
    dijkstra_valid_epath g u p v ->
    Z_op_le (Some 0) (dijkstra_epath_weight g p).
Proof.
  intros g u p v Hnonneg Hvalid.
  revert u v Hvalid.
  induction p as [| e p IHp]; intros u v Hvalid.
  - rewrite (@epath_weight_nil
      DijkstraGraph.G DijkstraGraph.E g DijkstraGraph.weight_instance);
      simpl; lia.
  - apply (dijkstra_valid_epath_cons_inv g u e p v)
      in Hvalid as [mid [_ Hrest]].
    rewrite (@epath_weight_cons
      DijkstraGraph.G DijkstraGraph.E DijkstraGraph.weight_instance g e p).
    pose proof (Hnonneg e) as He_nonneg.
    pose proof (IHp mid v Hrest) as Hp_nonneg.
    destruct (dijkstra_weight g e);
      destruct (dijkstra_epath_weight g p); simpl in *; auto; lia.
Qed.

Lemma dijkstra_first_step_full_done_to_math :
  forall g src visited_set dist_values,
    DijkstraGraph.graph_wf g ->
    vertex_valid g src ->
    nonnegative_edges g ->
    dijkstra_first_step_invariant g src
      (fun e : DijkstraGraph.E =>
        exists v : DijkstraGraph.V,
          dijkstra_step_aux g e src v)
      (dijkstra_array_state g visited_set dist_values) ->
    dijkstra_math_invariant g src visited_set dist_values.
Proof.
  intros g src visited_set dist_values Hwf Hsrc Hnonneg Hfirst.
  unfold dijkstra_math_invariant in *.
  destruct Hfirst as [Heq [Hdist [Hinv Hex]]].
  split; [| split].
  - intros v Hv; rewrite Heq in Hv; sets_unfold in Hv.
    symmetry in Hv; subst v.
    rewrite Hdist; split.
    + unfold min_value_weight_epath,
        min_value_of_subset_with_default,
        min_value_of_subset, min_object_of_subset.
      left; split; [| simpl; auto].
      exists nil; split; [| rewrite epath_weight_nil; reflexivity].
      split;
      [ apply (@valid_epath_empty
          DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E
          DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance
          DijkstraGraph.PathData DijkstraGraph.path_instance
          DijkstraGraph.empty_path_instance)
      |].
      intros p Hp.
      rewrite (@epath_weight_nil
        DijkstraGraph.G DijkstraGraph.E g DijkstraGraph.weight_instance).
      eapply dijkstra_valid_epath_non_neg;
        [exact Hnonneg | exact Hp].
    + unfold min_value_weight_epath_in_vset,
        min_value_of_subset_with_default,
        min_value_of_subset, min_object_of_subset.
      left; split; [| simpl; auto].
      exists nil; split; [| rewrite epath_weight_nil; reflexivity].
      split.
      * split;
        [ apply (@valid_epath_empty
            DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E
            DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance
            DijkstraGraph.PathData DijkstraGraph.path_instance
            DijkstraGraph.empty_path_instance)
        |].
        intros p1 p2 u Hnil1 Hnil2 Heq_path _.
        destruct p1; destruct p2; simpl in Heq_path;
          try contradiction; discriminate.
      * intros p Hp.
        destruct Hp as [Hp _].
        rewrite (@epath_weight_nil
          DijkstraGraph.G DijkstraGraph.E g DijkstraGraph.weight_instance).
        eapply dijkstra_valid_epath_non_neg;
          [exact Hnonneg | exact Hp].
  - intros v Hv; rewrite Heq in Hv; sets_unfold in Hv.
    destruct (classic (forall e, ~ dijkstra_step_aux g e src v)).
      + pose proof Hex v ltac:(symmetry; auto)
        ltac:(intros e [_ _]; unfold not; intros Hstep;
          exact (H e Hstep)).
      right; split; auto.
      intros a Ha; exfalso.
      destruct Ha as [Hpath Hvalid].
      apply dijkstra_valid_epath_inv_n1 in Hpath
        as [[] | [p [u [e [Hcons [Hp Hstep]]]]]]; auto.
      destruct p; [apply dijkstra_valid_epath_nil_inv in Hp; subst;
        eapply H; eauto |].
      pose proof Hvalid (e0 :: p) (e :: nil) u
        ltac:(symmetry; apply nil_cons)
        ltac:(symmetry; apply nil_cons) Hcons Hp as Hu.
      rewrite Heq in Hu; sets_unfold in Hu.
      symmetry in Hu; subst u.
      eapply H; eauto.
    + apply not_all_ex_not in H.
      destruct H as [e He].
      apply NNPP in He.
      pose proof Hinv v e ltac:(symmetry; auto)
        ltac:(exists v; auto) He as Hdist_v.
      left; split; [| apply Z_op_le_none_r].
      exists (e :: nil); split.
      2: {
        unfold epath_weight; simpl; rewrite Z_op_plus_O_r.
        symmetry; exact Hdist_v.
      }
      split; [apply dijkstra_is_epath_through_vset_single; auto | intros q Hq].
      destruct Hq as [Hpath Hvalid].
      apply dijkstra_valid_epath_inv_n1 in Hpath
        as [[] | [p [u [a [Hcons [Hp Hstep]]]]]]; subst; auto.
      contradiction.
      destruct p; [apply dijkstra_valid_epath_nil_inv in Hp; subst |].
      assert (Ha_eq : a = e).
      {
        eapply (@no_multiple_edge
          DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E
          DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance
          DijkstraGraph.simple_graph_instance g a e u v);
          eauto.
      }
      subst a; apply Z_op_le_refl.
      pose proof Hvalid (e0 :: p) (a :: nil) u
        ltac:(symmetry; apply nil_cons)
        ltac:(symmetry; apply nil_cons) ltac:(auto) Hp as Hu.
      rewrite Heq in Hu; sets_unfold in Hu; subst.
      assert (Ha_eq : a = e).
      {
        eapply (@no_multiple_edge
          DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E
          DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance
          DijkstraGraph.simple_graph_instance g a e u v);
          eauto.
      }
      subst a; simpl.
      rewrite app_comm_cons, epath_weight_app_assoc.
      rewrite <- Z_op_plus_O_l at 1.
      eapply Z_op_plus_mono;
        [eapply dijkstra_valid_epath_non_neg;
          [exact Hnonneg | exact Hp]
        |apply Z_op_le_refl].
	  - intros u v Hu Hv.
	    rewrite Heq in Hu; sets_unfold in Hu.
	    symmetry in Hu; subst u.
	    replace (@dist Z (dijkstra_array_state g visited_set dist_values) src)
	      with (Some 0) by (symmetry; exact Hdist).
	    destruct (classic (v = src));
	      [subst;
	       replace (@dist Z (dijkstra_array_state g visited_set dist_values) src)
	         with (Some 0) by (symmetry; exact Hdist);
	       simpl; lia |].
	    destruct (classic (exists e, dijkstra_step_aux g e src v))
	      as [[e He] | Hno_edge].
	    + pose proof Hinv v e ltac:(symmetry; auto)
	        ltac:(exists v; auto) He as Hs2v.
	      replace (@dist Z (dijkstra_array_state g visited_set dist_values) v)
	        with (dijkstra_weight g e) by (symmetry; exact Hs2v).
	      apply Hnonneg.
	    + pose proof Hex v ltac:(symmetry; auto)
	        ltac:(unfold not; intros; eapply Hno_edge; eauto) as Hs2v.
	      replace (@dist Z (dijkstra_array_state g visited_set dist_values) v)
	        with (None : option Z) by (symmetry; exact Hs2v).
	      simpl; auto.
Qed.

Definition dijkstra_selected_min
    (g : DijkstraGraph.G)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (cur_vertex : Z) : Prop :=
  min_object_of_subset Z_op_le
    (fun v => @unvisited Z
      (dijkstra_array_state g visited_set dist_values) v)
    (@dist Z (dijkstra_array_state g visited_set dist_values))
    cur_vertex.

Definition dijkstra_after_visit_state
    (g : DijkstraGraph.G) (visited_set : Z -> Prop)
    (dist_values : list Z) (cur_vertex : Z) : state :=
  set_state_visited cur_vertex
    (dijkstra_array_state g visited_set dist_values).

Lemma dijkstra_after_visit_state_dist_valid :
  forall g visited_set dist_values cur_vertex v,
    vertex_valid g v ->
    @dist Z (dijkstra_after_visit_state
      g visited_set dist_values cur_vertex) v =
      cell_as_distance (dist_cell dist_values v).
Proof.
  intros g visited_set dist_values cur_vertex v Hvalid.
  unfold dijkstra_after_visit_state, set_state_visited.
  simpl.
  exact (dijkstra_array_state_dist_valid
    g visited_set dist_values v Hvalid).
Qed.

Definition dijkstra_edge_math_state
    (g : DijkstraGraph.G) (src : Z)
    (visited_before visited_after : Z -> Prop)
    (cur_vertex : Z) (base_dist_values : list Z)
    (done : DijkstraGraph.E -> Prop) (dist_values : list Z) : Prop :=
  visited_set_add visited_before cur_vertex visited_after /\
  dijkstra_math_invariant g src visited_before base_dist_values /\
  dijkstra_selected_min g visited_before base_dist_values cur_vertex /\
    dijkstra_relax_step_invariant g cur_vertex
    (dijkstra_after_visit_state
      g visited_before base_dist_values cur_vertex)
    done
    (dijkstra_array_state g visited_after dist_values).

Lemma dijkstra_relax_step_invariant_done_equiv :
  forall g cur_vertex s0 done1 done2 s,
    (forall e, done1 e <-> done2 e) ->
    dijkstra_relax_step_invariant g cur_vertex s0 done1 s ->
    dijkstra_relax_step_invariant g cur_vertex s0 done2 s.
Proof.
  intros g cur_vertex s0 done1 done2 s Hdone Hinv.
  pose proof
    (@Dijkstra.relax_step_invariant_proper
      DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E
      DijkstraGraph.graph_instance g DijkstraGraph.weight_instance
      cur_vertex s0)
    as Hproper.
  unfold Morphisms.Proper, Morphisms.respectful in Hproper.
  apply (proj1 (Hproper done1 done2 Hdone s s eq_refl)).
  exact Hinv.
Qed.

Lemma dijkstra_edge_math_state_full_done_to_math :
  forall g src visited_before visited_after cur_vertex
         base_dist_values done dist_values,
    DijkstraGraph.graph_wf g ->
    nonnegative_edges g ->
    (forall e,
      done e <->
      exists v,
        dijkstra_step_aux g e cur_vertex v) ->
    dijkstra_edge_math_state g src visited_before visited_after
      cur_vertex base_dist_values done dist_values ->
    dijkstra_math_invariant g src visited_after dist_values.
Proof.
  intros g src visited_before visited_after cur_vertex
    base_dist_values done dist_values Hwf Hnonneg Hdone Hmath.
  unfold dijkstra_edge_math_state, dijkstra_math_invariant in Hmath.
  destruct Hmath as
    (_ & (Hfinal & Hoptimal & Hcross) & Hselected & Hrelax).
  eapply (dijkstra_invariant_implies_final
    g Hwf src Hnonneg cur_vertex
    (dijkstra_array_state g visited_before base_dist_values)
    (dijkstra_after_visit_state
      g visited_before base_dist_values cur_vertex)); eauto.
  eapply dijkstra_relax_step_invariant_done_equiv; eauto.
Qed.

Lemma dijkstra_edge_math_state_done_equiv :
  forall g src visited_before visited_after cur_vertex
         base_dist_values done1 done2 dist_values,
    (forall e, done1 e <-> done2 e) ->
    dijkstra_edge_math_state g src visited_before visited_after
      cur_vertex base_dist_values done1 dist_values ->
    dijkstra_edge_math_state g src visited_before visited_after
      cur_vertex base_dist_values done2 dist_values.
Proof.
  unfold dijkstra_edge_math_state.
  firstorder eauto using dijkstra_relax_step_invariant_done_equiv.
Qed.

Lemma dijkstra_array_state_graph_state_model :
	forall g vertex_count visited_set dist_values,
	  graph_has_size g vertex_count ->
	  vector_shape dist_values ->
	  dist_values_safe dist_values ->
    graph_state_model g visited_set dist_values
      (dijkstra_array_state g visited_set dist_values).
Proof.
  intros g vertex_count visited_set dist_values Hsize Hshape Hsafe.
  unfold graph_state_model.
  split.
	  - unfold graph_dist_model.
	    do 2 (split; [eassumption |]).
	    intros v Hvalid.
    rewrite dijkstra_array_state_dist_valid by exact Hvalid.
    symmetry.
    apply distance_as_cell_cell_as_distance_safe.
    apply Hsafe.
    eapply graph_has_size_vertex_valid_storage; eauto.
  - split.
    + intros v Hvalid.
      rewrite dijkstra_array_state_visited_iff; tauto.
    + unfold graph_state_invalid_default.
      intros v Hinvalid.
      rewrite dijkstra_array_state_dist_invalid by exact Hinvalid.
      rewrite dijkstra_array_state_visited_iff.
      tauto.
Qed.

Lemma dijkstra_reachable_vertex_valid :
  forall g src v,
    vertex_valid g src ->
    dijkstra_reachable g src v ->
    vertex_valid g v.
Proof.
  intros g src v Hsrc Hreach.
  destruct (Z.eq_dec v src) as [-> | Hneq]; auto.
  destruct (@reachable_vvalid DijkstraGraph.G DijkstraGraph.V
    DijkstraGraph.E g DijkstraGraph.graph_instance
    DijkstraGraph.gvalid_instance DijkstraGraph.stepvalid_instance
    src v ltac:(lia) Hreach) as (_ & Hv); exact Hv.
Qed.

Lemma dijkstra_math_invariant_no_relax_to_old_visited :
  forall g vertex_count src visited_set dist_values cur_vertex neighbor edge,
    graph_has_size g vertex_count ->
    nonnegative_edges g ->
    vertex_valid g cur_vertex ->
    vertex_valid g neighbor ->
    dijkstra_math_invariant g src visited_set dist_values ->
    dijkstra_selected_min g visited_set dist_values cur_vertex ->
    visited_set neighbor ->
    dijkstra_step_aux g edge cur_vertex neighbor ->
    Z_op_le
      (cell_as_distance (dist_cell dist_values neighbor))
      (Z_op_plus
        (cell_as_distance (dist_cell dist_values cur_vertex))
        (dijkstra_weight g edge)).
Proof.
  intros g vertex_count src visited_set dist_values cur_vertex neighbor edge
    Hsize Hnonneg Hcur_valid Hneighbor_valid Hmath Hmin Hvisited Hstep.
  set (s := dijkstra_array_state g visited_set dist_values).
  destruct Hmath as (Hfinal & Hoptimal & _).
  assert (@visited Z s neighbor) as Hvisited_state.
  {
    unfold s.
    apply dijkstra_array_state_visited_iff; split; assumption.
  }
  assert (~ @visited Z s cur_vertex) as Hcur_unvisited.
  {
    unfold dijkstra_selected_min in Hmin.
    destruct Hmin as (Hcur_unvisited & _).
    exact Hcur_unvisited.
  }
  assert (@dist Z s neighbor =
    cell_as_distance (dist_cell dist_values neighbor)) as Hdist_neighbor.
  {
    unfold s.
    apply dijkstra_array_state_dist_valid; exact Hneighbor_valid.
  }
  assert (@dist Z s cur_vertex =
    cell_as_distance (dist_cell dist_values cur_vertex)) as Hdist_cur.
  {
    unfold s.
    apply dijkstra_array_state_dist_valid; exact Hcur_valid.
  }
  rewrite <- Hdist_neighbor.
  rewrite <- Hdist_cur.
  pose proof (Hfinal neighbor Hvisited_state) as (Hneighbor_final & _).
  pose proof (Hoptimal cur_vertex Hcur_unvisited) as Hcur_optimal.
  eapply (dijkstra_visited_keep
    g src cur_vertex neighbor (@visited Z s) edge (@dist Z s)); eauto.
Qed.

Lemma DijkstraGraph_step_aux_no_self :
  forall g e u,
    DijkstraGraph.graph_wf g ->
    dijkstra_step_aux g e u u ->
    False.
Proof.
  intros g e u (_ & Hno_loop) (_ & Hu & _ & w & Hloop).
  rewrite (Hno_loop u Hu) in Hloop.
  discriminate.
Qed.

Lemma dijkstra_same_edge_target :
  forall g edge cur_vertex v1 v2,
    dijkstra_step_aux g edge cur_vertex v1 ->
    dijkstra_step_aux g edge cur_vertex v2 ->
    v1 = v2.
Proof.
  intros g edge cur_vertex v1 v2 [Heq1 _] [Heq2 _].
  congruence.
Qed.

Lemma dijkstra_done_no_same_target :
  forall g done cur_vertex neighbor edge,
    (forall e,
      done e ->
      exists v,
        dijkstra_step_aux g e cur_vertex v) ->
    ~ done edge ->
    dijkstra_step_aux g edge cur_vertex neighbor ->
    forall e',
      done e' ->
      ~ dijkstra_step_aux g e' cur_vertex neighbor.
Proof.
  intros g done cur_vertex neighbor edge Hdone_subset Hnot_done
    Hedge e' Hdone_e' Hstep_e'.
  destruct (Hdone_subset e' Hdone_e') as (v' & Hstep_out).
  assert (v' = neighbor) by (eapply dijkstra_same_edge_target; eauto); subst.
  destruct Hstep_e' as (Heq_e' & _).
  destruct Hedge as (Heq_edge & _).
  subst; contradiction.
Qed.

Ltac dijkstra_add_edge_invariant
    edge neighbor Hdone_subset Hnot_done Hedge Hinv Hvisited_new
    Hdist_fixed_new Hdist_neighbor Hdist_other :=
  unfold Dijkstra.first_step_invariant, Dijkstra.relax_step_invariant in *;
  destruct Hinv as (Hvisited_old & Hdist_fixed_old & Hstep_old & Hcut_old);
  split; [rewrite Hvisited_new; exact Hvisited_old |];
  split;
  [ match type of Hdist_fixed_new with
    | @eq _ (@dist Z ?s_new ?fixed) _ =>
        match type of Hdist_fixed_old with
        | @eq _ _ ?rhs =>
            change (@dist Z s_new fixed = rhs);
            rewrite Hdist_fixed_new; exact Hdist_fixed_old
        end
    end
  |];
  split;
  [ intros v e Hneq Hdone_new Hstep_e;
    destruct Hdone_new as [Hdone_old | Heq_edge];
    [ assert (v <> neighbor) as Hneq_neighbor
        by (intro Hv; subst v;
            eapply dijkstra_done_no_same_target; eauto);
      rewrite Hdist_other by exact Hneq_neighbor;
      apply Hstep_old; auto
    | subst e;
      assert (v = neighbor) by (eapply dijkstra_same_edge_target; eauto);
      subst v; exact Hdist_neighbor ]
  | intros v Hneq Hno_done_new;
    assert (v <> neighbor) as Hneq_neighbor
      by (intro Hv; subst v; apply (Hno_done_new edge);
          [right; reflexivity | exact Hedge]);
    rewrite Hdist_other by exact Hneq_neighbor;
    apply Hcut_old; auto;
    intros e Hdone_old; apply Hno_done_new; left; exact Hdone_old ].

Lemma dijkstra_first_step_invariant_add_edge :
  forall g src done s_old s_new edge neighbor,
    (forall e,
      done e ->
      exists v,
        dijkstra_step_aux g e src v) ->
    ~ done edge ->
    dijkstra_step_aux g edge src neighbor ->
    neighbor <> src ->
    dijkstra_first_step_invariant g src done s_old ->
    @visited Z s_new == @visited Z s_old ->
    @dist Z s_new src = @dist Z s_old src ->
    @dist Z s_new neighbor = dijkstra_weight g edge ->
    (forall v,
      v <> neighbor ->
      @dist Z s_new v = @dist Z s_old v) ->
    dijkstra_first_step_invariant g src
      (fun e => done e \/ e = edge) s_new.
Proof.
  intros g src done s_old s_new edge neighbor
    Hdone_subset Hnot_done Hedge Hneighbor_ne_src Hinv Hvisited_new
    Hdist_src_new Hdist_neighbor Hdist_other.
  dijkstra_add_edge_invariant edge neighbor Hdone_subset Hnot_done Hedge Hinv
    Hvisited_new Hdist_src_new Hdist_neighbor Hdist_other.
Qed.

Lemma dijkstra_relax_step_invariant_add_edge :
  forall g cur_vertex s0 done s_old s_new edge neighbor,
    (forall e,
      done e ->
      exists v,
        dijkstra_step_aux g e cur_vertex v) ->
    ~ done edge ->
    dijkstra_step_aux g edge cur_vertex neighbor ->
    neighbor <> cur_vertex ->
    dijkstra_relax_step_invariant g cur_vertex s0 done s_old ->
    @visited Z s_new == @visited Z s_old ->
    @dist Z s_new cur_vertex = @dist Z s_old cur_vertex ->
    @dist Z s_new neighbor =
      Z_op_min (@dist Z s0 neighbor)
        (Z_op_plus (@dist Z s0 cur_vertex) (dijkstra_weight g edge)) ->
    (forall v,
      v <> neighbor ->
      @dist Z s_new v = @dist Z s_old v) ->
    dijkstra_relax_step_invariant g cur_vertex s0
      (fun e => done e \/ e = edge) s_new.
Proof.
  intros g cur_vertex s0 done s_old s_new edge neighbor
    Hdone_subset Hnot_done Hedge Hneighbor_ne_cur Hinv Hvisited_new
    Hdist_cur_new Hdist_neighbor Hdist_other.
  dijkstra_add_edge_invariant edge neighbor Hdone_subset Hnot_done Hedge Hinv
    Hvisited_new Hdist_cur_new Hdist_neighbor Hdist_other.
Qed.

Section EdgeMathRelaxProofs.

Context (g : DijkstraGraph.G)
        (vertex_count src : Z)
        (visited_before visited_after : Z -> Prop)
        (cur_vertex : Z)
        (base_dist_values : list Z)
        (done : DijkstraGraph.E -> Prop)
        (dist_values : list Z)
        (edge : DijkstraGraph.E)
        (neighbor edge_weight cur_distance candidate : Z).

Lemma dijkstra_edge_math_state_no_done_target_dist_base :
    (forall e,
      done e ->
      exists v,
        dijkstra_step_aux g e cur_vertex v) ->
    ~ done edge ->
    neighbor <> cur_vertex ->
    dijkstra_step_aux g edge cur_vertex neighbor ->
    dijkstra_edge_math_state g src visited_before visited_after
      cur_vertex base_dist_values done dist_values ->
    @dist Z (dijkstra_array_state g visited_after dist_values) neighbor =
      @dist Z
        (dijkstra_after_visit_state
          g visited_before base_dist_values cur_vertex) neighbor.
Proof.
  intros Hdone_subset Hnot_done Hneq Hedge Hmath.
  unfold dijkstra_edge_math_state in Hmath.
  destruct Hmath as (_ & _ & _ & Hrelax).
  unfold Dijkstra.relax_step_invariant in Hrelax.
  destruct Hrelax as (_ & _ & _ & Hcut).
  apply Hcut; auto.
  intros e' Hdone_e'.
  eapply dijkstra_done_no_same_target; eauto.
Qed.

Lemma dijkstra_after_visit_base_cell_eq :
    vertex_valid g neighbor ->
    @dist Z (dijkstra_array_state g visited_after dist_values) neighbor =
      @dist Z
        (dijkstra_after_visit_state
          g visited_before base_dist_values cur_vertex) neighbor ->
    cell_as_distance (dist_cell base_dist_values neighbor) =
      cell_as_distance (dist_cell dist_values neighbor).
Proof.
  intros Hvalid Hdist.
  rewrite dijkstra_after_visit_state_dist_valid in Hdist by exact Hvalid.
  rewrite dijkstra_array_state_dist_valid in Hdist by exact Hvalid.
  symmetry.
  exact Hdist.
Qed.

Lemma dijkstra_edge_math_state_relax_common :
    DijkstraGraph.graph_wf g ->
    (forall e,
      done e ->
      exists v,
        dijkstra_step_aux g e cur_vertex v) ->
    ~ done edge ->
    dijkstra_step_aux g edge cur_vertex neighbor ->
    dijkstra_edge_math_state g src visited_before visited_after
      cur_vertex base_dist_values done dist_values ->
    vertex_valid g cur_vertex /\
    neighbor <> cur_vertex /\
    @dist Z (dijkstra_array_state g visited_after dist_values) neighbor =
    @dist Z
      (dijkstra_after_visit_state
        g visited_before base_dist_values cur_vertex) neighbor.
Proof.
  intros Hwf Hdone_subset Hnot_done Hedge Hmath.
  assert (Hcur_valid : vertex_valid g cur_vertex)
    by (destruct Hedge as (_ & Hgraph_step); exact (proj1 Hgraph_step)).
  assert (Hneighbor_ne_cur : neighbor <> cur_vertex)
    by (intro Heq; subst neighbor; eapply DijkstraGraph_step_aux_no_self; eauto).
  do 2 (split; [eassumption |]).
  eapply dijkstra_edge_math_state_no_done_target_dist_base; eauto.
Qed.

Ltac start_edge_math_relax Hwf Hdone_subset Hnot_done Hedge Hmath :=
  pose proof
    (dijkstra_edge_math_state_relax_common
      Hwf Hdone_subset Hnot_done Hedge Hmath)
    as (Hcur_valid & Hneighbor_ne_cur & Hneighbor_base);
  unfold dijkstra_edge_math_state in *;
  destruct Hmath as (Hvisit_add & Hmath & Hselected & Hinv);
  do 3 (split; [eassumption |]);
  eapply dijkstra_relax_step_invariant_add_edge; eauto.

Lemma dijkstra_edge_math_state_relax_update :
	    graph_has_size g vertex_count ->
	    DijkstraGraph.graph_wf g ->
	    vector_shape dist_values ->
	    dist_values_safe dist_values ->
    vertex_valid g neighbor ->
    storage_index neighbor ->
    cur_distance = dist_cell base_dist_values cur_vertex ->
    0 <= cur_distance < DijkstraGraph.infinity ->
    0 <= candidate < DijkstraGraph.infinity ->
    candidate = cur_distance + edge_weight ->
    dijkstra_weight g edge = Some edge_weight ->
    candidate < dist_cell dist_values neighbor ->
    (forall e,
      done e ->
      exists v,
        dijkstra_step_aux g e cur_vertex v) ->
    ~ done edge ->
    dijkstra_step_aux g edge cur_vertex neighbor ->
    dijkstra_edge_math_state g src visited_before visited_after
      cur_vertex base_dist_values done dist_values ->
    dijkstra_edge_math_state g src visited_before visited_after
      cur_vertex base_dist_values
      (fun e => done e \/ e = edge)
      (replace_Znth neighbor candidate dist_values).
Proof.
  intros Hsize Hwf Hshape Hsafe Hneighbor_valid
    Hneighbor_storage Hcur_distance Hcur_finite Hcandidate_bounds
    Hcandidate_eq Hweight Hrelax Hdone_subset Hnot_done Hedge Hmath.
  start_edge_math_relax Hwf Hdone_subset Hnot_done Hedge Hmath.
  - reflexivity.
  - erewrite dijkstra_array_state_dist_replace_other
      by (eauto using graph_has_size_vertex_valid_storage; lia).
    reflexivity.
  - erewrite dijkstra_array_state_dist_replace_same by eauto.
    pose proof
      (dijkstra_after_visit_base_cell_eq
        Hneighbor_valid Hneighbor_base)
      as Hbase_neighbor_cell.
    rewrite !dijkstra_after_visit_state_dist_valid by assumption.
	    rewrite Hbase_neighbor_cell.
    rewrite <- Hcur_distance.
    rewrite (cell_as_distance_finite cur_distance Hcur_finite).
    change (DijkstraGraph.edge_weight g (fst edge) (snd edge))
      with (dijkstra_weight g edge).
    rewrite Hweight.
    simpl.
    replace (cur_distance + edge_weight) with candidate by lia.
    symmetry.
    unfold cell_as_distance, DijkstraGraph.cell_as_distance.
    destruct (Z.eq_dec (dist_cell dist_values neighbor)
      DijkstraGraph.infinity).
    + reflexivity.
    + simpl. f_equal. lia.
  - intros v Hneq_neighbor.
    erewrite dijkstra_array_state_dist_replace_other by eauto.
    reflexivity.
Qed.

Lemma dijkstra_edge_math_state_relax_skip :
	    graph_has_size g vertex_count ->
	    DijkstraGraph.graph_wf g ->
	    dist_values_safe dist_values ->
    vertex_valid g neighbor ->
    storage_index neighbor ->
    cur_distance = dist_cell base_dist_values cur_vertex ->
    0 <= cur_distance < DijkstraGraph.infinity ->
    0 <= candidate < DijkstraGraph.infinity ->
    candidate = cur_distance + edge_weight ->
    dijkstra_weight g edge = Some edge_weight ->
    dist_cell dist_values neighbor <= candidate ->
    (forall e,
      done e ->
      exists v,
        dijkstra_step_aux g e cur_vertex v) ->
    ~ done edge ->
    dijkstra_step_aux g edge cur_vertex neighbor ->
    dijkstra_edge_math_state g src visited_before visited_after
      cur_vertex base_dist_values done dist_values ->
    dijkstra_edge_math_state g src visited_before visited_after
      cur_vertex base_dist_values
      (fun e => done e \/ e = edge)
      dist_values.
Proof.
  intros Hsize Hwf Hsafe Hneighbor_valid
    Hneighbor_storage Hcur_distance Hcur_finite Hcandidate_bounds
    Hcandidate_eq Hweight Hskip Hdone_subset Hnot_done Hedge Hmath.
  start_edge_math_relax Hwf Hdone_subset Hnot_done Hedge Hmath.
  - reflexivity.
  - pose proof
      (dijkstra_after_visit_base_cell_eq
        Hneighbor_valid Hneighbor_base)
      as Hbase_neighbor_cell.
    replace (@dist Z
      (dijkstra_after_visit_state
        g visited_before base_dist_values cur_vertex) neighbor)
      with (@dist Z (dijkstra_array_state g visited_after dist_values)
        neighbor) by exact Hneighbor_base.
    rewrite dijkstra_array_state_dist_valid by exact Hneighbor_valid.
    replace (@dist Z
      (dijkstra_after_visit_state
        g visited_before base_dist_values cur_vertex) cur_vertex)
      with (Some cur_distance).
    2: {
      rewrite dijkstra_after_visit_state_dist_valid by exact Hcur_valid.
      rewrite <- Hcur_distance.
      symmetry.
      apply cell_as_distance_finite.
      exact Hcur_finite.
    }
    change (DijkstraGraph.edge_weight g (fst edge) (snd edge))
      with (dijkstra_weight g edge).
    rewrite Hweight.
    simpl.
    replace (cur_distance + edge_weight) with candidate by lia.
	    rewrite <- Hbase_neighbor_cell.
	    destruct (vertex_valid_dec g neighbor) as [_ | Hinvalid_neighbor];
	      [| contradiction].
	    symmetry; apply Z_op_le_min_l.
	    assert (Hbase_neighbor_eq :
	      dist_cell base_dist_values neighbor =
	      dist_cell dist_values neighbor).
	    {
	      unfold cell_as_distance, DijkstraGraph.cell_as_distance
	        in Hbase_neighbor_cell.
	      destruct (Z.eq_dec (dist_cell base_dist_values neighbor)
	        DijkstraGraph.infinity) as [Hbase_inf | Hbase_finite];
	      destruct (Z.eq_dec (dist_cell dist_values neighbor)
	        DijkstraGraph.infinity) as [Hdist_inf | Hdist_finite];
	      try congruence;
	      try solve [lia | inversion Hbase_neighbor_cell; lia].
	    }
	    unfold cell_as_distance, DijkstraGraph.cell_as_distance, Z_op_le.
	    destruct (Z.eq_dec (dist_cell base_dist_values neighbor)
	      DijkstraGraph.infinity) as [Hbase_inf | Hbase_finite].
	    + rewrite Hbase_neighbor_eq in Hbase_inf.
	      rewrite Hbase_inf in Hskip; lia.
	    + rewrite Hbase_neighbor_eq; lia.
Qed.

End EdgeMathRelaxProofs.

Lemma dist_cell_replace_Znth_same :
  forall values v candidate,
    vector_shape values ->
    storage_index v ->
    dist_cell (replace_Znth v candidate values) v = candidate.
Proof.
  intros values v candidate Hshape Hstorage.
  unfold dist_cell.
  rewrite Znth_replace_Znth_Same by dijkstra_bounds_cleanup.
  reflexivity.
Qed.

Lemma dist_cell_replace_Znth_diff :
  forall values v u candidate,
    vector_shape values ->
    storage_index v ->
    storage_index u ->
    u <> v ->
    dist_cell (replace_Znth v candidate values) u = dist_cell values u.
Proof.
  intros values v u candidate Hshape Hv Hu Hneq.
  unfold dist_cell.
  rewrite Znth_replace_Znth_Diff by dijkstra_bounds_cleanup.
  reflexivity.
Qed.

Lemma dist_cell_Znth_0 :
  forall values v,
    vector_shape values ->
    storage_index v ->
    dist_cell values v = Znth v values 0.
Proof.
  intros values v Hshape Hstorage.
  unfold dist_cell.
  apply Znth_indep; dijkstra_bounds_cleanup.
Qed.

Lemma forward_star_model_head_case_0 :
  forall g vertex_count edge_count head_values to_values
         weight_values next_values u,
    graph_has_size g vertex_count ->
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    0 <= u < vertex_count ->
    Znth u head_values 0 = -1 \/
      edge_index edge_count (Znth u head_values 0).
Proof.
  intros g vertex_count edge_count head_values to_values
    weight_values next_values u Hsize Hmodel Hu.
  destruct (forward_star_model_head_safe _ _ _ _ _ _ Hmodel)
    as (Hhead_len & Hhead_case).
  rewrite <- (Znth_indep _ _ (-1)) by dijkstra_bounds_cleanup.
  apply Hhead_case; dijkstra_bounds_cleanup.
Qed.

Lemma forward_star_model_edge_bounds :
  forall g edge_count head_values to_values weight_values next_values edge,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_index edge_count edge ->
    0 <= Znth edge to_values 0 < DijkstraGraph.vertex_count g /\
    storage_index (Znth edge to_values 0) /\
    0 <= Znth edge weight_values 0 <= DijkstraGraph.infinity /\
    (Znth edge next_values (-1) = -1 \/
      edge_index edge_count (Znth edge next_values (-1))).
Proof.
  intros g edge_count head_values to_values weight_values next_values
    edge Hmodel Hedge.
  destruct (forward_star_model_edge_safe _ _ _ _ _ _ Hmodel)
    as (_ & _ & _ & Hedges).
  apply Hedges.
  exact Hedge.
Qed.

Lemma dijkstra_skip_assume_to_dist_cell :
  forall g edge_count head_values to_values weight_values next_values
         visited_set dist_values s edge cur_distance,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    graph_state_model g visited_set dist_values s ->
    vertex_valid g (Znth edge to_values 0) ->
    edge_index edge_count edge ->
    0 <= cur_distance + Znth edge weight_values 0 <
      DijkstraGraph.infinity ->
    Znth edge weight_values 0 < 0 \/
      cur_distance > DijkstraGraph.infinity - Znth edge weight_values 0 \/
      cur_distance + Znth edge weight_values 0 >=
        state_distance_cell (Znth edge to_values 0) s ->
    dist_cell dist_values (Znth edge to_values 0) <=
      cur_distance + Znth edge weight_values 0.
Proof.
  intros g edge_count head_values to_values weight_values next_values
    visited_set dist_values s edge cur_distance Hmodel Hstate
    Hneighbor_valid Hedge_index Hcandidate_bounds Hskip.
  destruct Hskip as [Hneg | [Hoverflow | Hge]].
  - pose proof
      (forward_star_model_edge_bounds _ _ _ _ _ _ _ Hmodel Hedge_index)
      as (_ & _ & Hweight_bounds & _).
    lia.
  - lia.
  - erewrite graph_state_model_dist_cell in Hge by eauto.
    lia.
Qed.

Lemma forward_star_model_next_case_0 :
  forall g edge_count head_values to_values weight_values next_values edge,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_index edge_count edge ->
    Znth edge next_values 0 = -1 \/
      edge_index edge_count (Znth edge next_values 0).
Proof.
  intros g edge_count head_values to_values weight_values next_values
    edge Hmodel Hedge.
  destruct (forward_star_model_edge_bounds _ _ _ _ _ _ _ Hmodel Hedge)
    as (_ & _ & _ & Hnext).
  destruct (forward_star_model_edge_safe _ _ _ _ _ _ Hmodel)
    as (_ & _ & Hnext_len & _).
  rewrite <- (Znth_indep _ _ (-1)) by dijkstra_bounds_cleanup.
  exact Hnext.
Qed.

Definition forward_star_outgoing_edge_set
    (head_values to_values weight_values next_values : list Z)
    (u : Z) (e : DijkstraGraph.E) : Prop :=
  exists v w,
    e = (u, v) /\
    forward_star_edge head_values to_values weight_values next_values
      u v w.

Definition forward_star_suffix_index
    (next_values : list Z) (edge : Z) (idx : Z) : Prop :=
  edge <> -1 /\ next_chain next_values edge idx.

Definition forward_star_suffix_edge_set
    (to_values weight_values next_values : list Z)
    (u edge : Z) (e : DijkstraGraph.E) : Prop :=
  exists idx v w,
    forward_star_suffix_index next_values edge idx /\
    e = (u, v) /\
    0 <= idx < Zlength to_values /\
    Znth idx to_values 0 = v /\
    Znth idx weight_values 0 = w.

Definition forward_star_done_edge_set
    (head_values to_values weight_values next_values : list Z)
    (u edge : Z) (e : DijkstraGraph.E) : Prop :=
  forward_star_outgoing_edge_set
    head_values to_values weight_values next_values u e /\
  ~ forward_star_suffix_edge_set
    to_values weight_values next_values u edge e.

Lemma next_chain_minus_one_false :
  forall next_values idx,
    ~ next_chain next_values (-1) idx.
Proof.
  intros next_values idx Hchain.
  remember (-1) as start; induction Hchain; subst; lia.
Qed.

Lemma next_chain_tail_to_head :
  forall next_values edge idx,
    0 <= edge < Zlength next_values ->
    Znth edge next_values (-1) <> -1 ->
    next_chain next_values (Znth edge next_values (-1)) idx ->
    next_chain next_values edge idx.
Proof.
  eauto using next_chain.
Qed.

Lemma next_chain_trans :
  forall next_values start mid idx,
    next_chain next_values start mid ->
    next_chain next_values mid idx ->
    next_chain next_values start idx.
Proof.
  intros next_values start mid idx Hstart_mid Hmid_idx;
    induction Hstart_mid; eauto using next_chain.
Qed.

Lemma forward_star_suffix_edge_set_minus_one_false :
  forall to_values weight_values next_values u e,
    ~ forward_star_suffix_edge_set
        to_values weight_values next_values u (-1) e.
Proof.
  intros to_values weight_values next_values u e
    (idx & v & w & (_ & Hchain) & _).
  eapply next_chain_minus_one_false; eauto.
Qed.

Lemma forward_star_done_edge_set_minus_one_full :
  forall head_values to_values weight_values next_values u e,
    forward_star_done_edge_set
      head_values to_values weight_values next_values u (-1) e <->
    forward_star_outgoing_edge_set
      head_values to_values weight_values next_values u e.
Proof.
  intros head_values to_values weight_values next_values u e.
  unfold forward_star_done_edge_set; firstorder
    eauto using forward_star_suffix_edge_set_minus_one_false.
Qed.

Lemma forward_star_current_edge_in_suffix :
  forall to_values weight_values next_values u edge,
    0 <= edge < Zlength next_values ->
    0 <= edge < Zlength to_values ->
    forward_star_suffix_edge_set
      to_values weight_values next_values u edge
      (u, Znth edge to_values 0).
Proof.
  intros to_values weight_values next_values u edge Hedge_next Hedge_to.
  unfold forward_star_suffix_edge_set, forward_star_suffix_index.
  exists edge, (Znth edge to_values 0), (Znth edge weight_values 0).
  repeat split; eauto using next_chain; lia.
Qed.

Lemma forward_star_suffix_edge_set_tail_to_head_any :
  forall to_values weight_values next_values u edge e_abs,
    0 <= edge < Zlength next_values ->
    forward_star_suffix_edge_set
      to_values weight_values next_values u
      (Znth edge next_values (-1)) e_abs ->
    forward_star_suffix_edge_set
      to_values weight_values next_values u edge e_abs.
Proof.
  intros to_values weight_values next_values u edge e_abs
    Hedge_next Hsuffix.
  destruct (Z.eq_dec (Znth edge next_values (-1)) (-1))
    as [Hnext_nil | Hnext_not_nil].
  - exfalso; rewrite Hnext_nil in Hsuffix;
      eapply forward_star_suffix_edge_set_minus_one_false; eauto.
  - unfold forward_star_suffix_edge_set in *.
    destruct Hsuffix as
      (idx & v & w & Hsuffix_idx & He_abs & Hidx_to & Hto & Hweight).
    destruct Hsuffix_idx as (_ & Htail).
    exists idx, v, w.
    split.
    + split; [lia |].
      eapply next_chain_tail_to_head; eauto.
    + split; [exact He_abs |].
      split; [exact Hidx_to |].
      split; assumption.
Qed.

Lemma forward_star_done_edge_set_step_0 :
  forall head_values to_values weight_values next_values u edge e_abs,
    forward_star_chain_wf head_values to_values next_values ->
    storage_index u ->
    next_chain next_values (Znth u head_values (-1)) edge ->
    0 <= edge < Zlength next_values ->
    0 <= edge < Zlength to_values ->
    (forward_star_done_edge_set
      head_values to_values weight_values next_values u
      (Znth edge next_values 0) e_abs <->
     forward_star_done_edge_set
       head_values to_values weight_values next_values u edge e_abs \/
     e_abs = (u, Znth edge to_values 0)).
Proof.
  intros head_values to_values weight_values next_values u edge e_abs
    Hchain_wf Hu Hhead_edge Hedge_next Hedge_to.
  rewrite <- (Znth_indep _ _ (-1)) by assumption.
  unfold forward_star_done_edge_set.
  assert (Hcurrent_out :
    forward_star_outgoing_edge_set
      head_values to_values weight_values next_values u
      (u, Znth edge to_values 0)).
  {
    unfold forward_star_outgoing_edge_set, forward_star_edge.
    exists (Znth edge to_values 0), (Znth edge weight_values 0).
    split; [reflexivity |].
    split; [exact Hu |].
    exists edge.
    split; [exact Hhead_edge |].
    split; [exact Hedge_to |].
    split; reflexivity.
  }
  assert (Hcurrent_not_tail :
    ~ forward_star_suffix_edge_set
        to_values weight_values next_values u
        (Znth edge next_values (-1))
        (u, Znth edge to_values 0)).
  {
    intros Hsuffix.
    destruct Hchain_wf as (Hno_cycle & Hno_dup & _).
    destruct (Z.eq_dec (Znth edge next_values (-1)) (-1))
      as [Hnext_nil | Hnext_not_nil].
    - rewrite Hnext_nil in Hsuffix.
      eapply forward_star_suffix_edge_set_minus_one_false; eauto.
    - unfold forward_star_suffix_edge_set in Hsuffix.
      destruct Hsuffix as
        (idx & v & w & Hsuffix_idx & He_abs & Hidx_to & Hto & _).
      destruct Hsuffix_idx as (_ & Htail_idx).
      injection He_abs as Hv.
      assert (Hhead_idx :
        next_chain next_values (Znth u head_values (-1)) idx)
        by (eapply next_chain_trans;
            [exact Hhead_edge | eapply next_chain_tail_to_head; eauto]).
      assert (idx = edge)
        by (symmetry; eapply Hno_dup; eauto; congruence).
      subst.
      eapply (Hno_cycle edge Hedge_next Hnext_not_nil).
      exact Htail_idx.
  }
  split.
  - intros (Hout & Hnot_tail).
    destruct (classic
      (forward_star_suffix_edge_set
        to_values weight_values next_values u edge e_abs))
      as [Hsuffix_edge | Hnot_edge].
    + unfold forward_star_suffix_edge_set in Hsuffix_edge.
      destruct Hsuffix_edge as
        (idx & v & w & Hsuffix_idx & He_abs & Hidx_to & Hto & Hweight).
      unfold forward_star_suffix_index in Hsuffix_idx.
      destruct Hsuffix_idx as (Hedge_not_nil & Hchain).
      remember edge as start eqn:Hstart.
      remember idx as stop eqn:Hstop.
      induction Hchain as [e Hedge | cur e Hcur Hnext Htail IH].
      * assert (idx = edge) by congruence.
        subst idx.
        right.
        subst e_abs.
        rewrite <- Hto.
        reflexivity.
      * assert (edge = cur) by congruence.
        assert (idx = e) by congruence.
        subst edge idx.
        exfalso.
        apply Hnot_tail.
        unfold forward_star_suffix_edge_set, forward_star_suffix_index.
        exists e, v, w.
        split.
        -- split; assumption.
        -- split; [exact He_abs |].
           split; [exact Hidx_to |].
           split; assumption.
    + left. split; assumption.
  - intros [Hdone_edge | Hcurrent].
    + destruct Hdone_edge as (Hout & Hnot_edge).
      split; [exact Hout |].
      intro Htail; apply Hnot_edge;
        eapply forward_star_suffix_edge_set_tail_to_head_any; eauto.
    + subst e_abs.
      split; [exact Hcurrent_out | exact Hcurrent_not_tail].
Qed.

Lemma forward_star_edge_step_aux_and_weight :
  forall g edge_count head_values to_values weight_values next_values
         u v w,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    vertex_valid g u ->
    forward_star_edge head_values to_values weight_values next_values
      u v w ->
    dijkstra_step_aux g (u, v) u v /\
    dijkstra_weight g (u, v) = Some w.
Proof.
  intros g edge_count head_values to_values weight_values next_values
    u v w Hmodel Hu Hedge.
  assert (Hv : vertex_valid g v).
  {
    unfold forward_star_edge in Hedge.
    destruct Hedge as (_ & e & _ & Hedge_index_zlen & Hto & _).
    destruct (forward_star_model_edge_safe _ _ _ _ _ _ Hmodel)
      as (Hto_len & _ & _ & Hedges).
    assert (edge_index edge_count e) as Hedge_index.
    {
      unfold edge_index.
      rewrite <- Hto_len.
      exact Hedge_index_zlen.
    }
    specialize (Hedges e Hedge_index).
    destruct Hedges as (Hto_bounds & _).
    unfold vertex_valid, DijkstraGraph.vertex_valid.
    rewrite <- Hto.
    exact Hto_bounds.
  }
  assert (Hweight :
    DijkstraGraph.edge_weight g u v = Some w).
  {
    apply (proj2 (forward_star_model_edge_iff
      _ _ _ _ _ _ Hmodel u v w Hu Hv)).
    exact Hedge.
  }
  split.
  - simpl.
    split; [reflexivity |].
    unfold DijkstraGraph.graph_step.
    split; [exact Hu |].
    split; [exact Hv |].
    exists w. exact Hweight.
  - simpl. exact Hweight.
Qed.

Lemma forward_star_outgoing_edge_set_equiv_step_aux :
  forall g edge_count head_values to_values weight_values next_values u,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    vertex_valid g u ->
    forall e,
      (exists v,
        dijkstra_step_aux g e u v) <->
      forward_star_outgoing_edge_set
        head_values to_values weight_values next_values u e.
Proof.
  intros g edge_count head_values to_values weight_values next_values
    u Hmodel Hu e.
  split.
  - intros [v Hstep].
    simpl in Hstep.
    destruct Hstep as (Heq & Hgraph_step).
    subst e.
    unfold DijkstraGraph.graph_step in Hgraph_step.
    destruct Hgraph_step as (_ & Hv & w & Hweight).
    exists v, w.
    split; [reflexivity |].
    apply (proj1 (forward_star_model_edge_iff
      _ _ _ _ _ _ Hmodel u v w Hu Hv)).
    exact Hweight.
  - intros (v & w & Heq & Hedge).
    subst e.
    exists v.
    pose proof
      (forward_star_edge_step_aux_and_weight
        g edge_count head_values to_values weight_values next_values
        u v w Hmodel Hu Hedge) as (Hstep & _).
	    exact Hstep.
Qed.

Lemma forward_star_done_edge_set_minus_one_equiv_step_aux :
  forall g edge_count head_values to_values weight_values next_values u e,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    vertex_valid g u ->
    forward_star_done_edge_set
      head_values to_values weight_values next_values u (-1) e <->
    exists v,
      dijkstra_step_aux g e u v.
Proof.
  intros g edge_count head_values to_values weight_values next_values
    u e Hmodel Hu.
  rewrite forward_star_done_edge_set_minus_one_full.
  symmetry.
  eapply forward_star_outgoing_edge_set_equiv_step_aux; eauto.
Qed.

Lemma forward_star_done_edge_set_step_aux :
  forall g edge_count head_values to_values weight_values next_values u edge e,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    vertex_valid g u ->
    forward_star_done_edge_set
      head_values to_values weight_values next_values u edge e ->
    exists v,
      dijkstra_step_aux g e u v.
Proof.
  intros g edge_count head_values to_values weight_values next_values
    u edge e Hmodel Hu Hdone.
  apply (proj2 (forward_star_outgoing_edge_set_equiv_step_aux
    g edge_count head_values to_values weight_values next_values
    u Hmodel Hu e)).
  exact (proj1 Hdone).
Qed.

Lemma forward_star_model_edge_index_zlengths :
  forall g edge_count head_values to_values weight_values next_values edge,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_index edge_count edge ->
    0 <= edge < Zlength to_values /\
    0 <= edge < Zlength next_values.
Proof.
  intros g edge_count head_values to_values weight_values next_values edge
    Hmodel Hedge.
  unfold edge_index in Hedge.
  destruct (forward_star_model_edge_safe _ _ _ _ _ _ Hmodel)
    as (Hto_len & _ & Hnext_len & _); lia.
Qed.

Lemma forward_star_next_chain_edge_index :
  forall g edge_count head_values to_values weight_values next_values u edge,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    vertex_valid g u ->
    next_chain next_values (Znth u head_values (-1)) edge ->
    edge_index edge_count edge.
Proof.
  intros g edge_count head_values to_values weight_values next_values
    u edge Hmodel Hu Hchain.
  destruct Hmodel as (_ & Hsize & _ & _ & Hedge_safe & _ & _ & Hchain_wf).
  pose proof
    (graph_has_size_vertex_valid_storage _ _ _ Hsize Hu)
    as Hu_storage.
  destruct Hchain_wf as (_ & _ & Hchain_bound).
  destruct Hedge_safe as (_ & _ & Hnext_len & _).
  unfold edge_index.
  pose proof (Hchain_bound u edge Hu_storage
    ltac:(intro Hnil; rewrite Hnil in Hchain;
          eapply next_chain_minus_one_false; eauto)
    Hchain); lia.
Qed.

Lemma forward_star_current_edge_not_done :
  forall head_values to_values weight_values next_values u edge,
    0 <= edge < Zlength next_values ->
    0 <= edge < Zlength to_values ->
    ~ forward_star_done_edge_set
        head_values to_values weight_values next_values u edge
        (u, Znth edge to_values 0).
Proof.
  intros head_values to_values weight_values next_values u edge
    Hedge_next Hedge_to Hdone.
  destruct Hdone as (_ & Hnot_suffix).
  apply Hnot_suffix; apply forward_star_current_edge_in_suffix; auto.
Qed.

Lemma forward_star_current_edge_facts :
  forall g vertex_count edge_count head_values to_values weight_values
         next_values u edge,
    graph_has_size g vertex_count ->
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    vertex_valid g u ->
    next_chain next_values (Znth u head_values (-1)) edge ->
    edge_index edge_count edge ->
    forward_star_chain_wf head_values to_values next_values /\
    storage_index u /\
    0 <= edge < Zlength to_values /\
    0 <= edge < Zlength next_values /\
    vertex_valid g (Znth edge to_values 0) /\
    storage_index (Znth edge to_values 0) /\
    dijkstra_step_aux g
      (u, Znth edge to_values 0) u (Znth edge to_values 0) /\
    dijkstra_weight g
      (u, Znth edge to_values 0) = Some (Znth edge weight_values 0) /\
    Znth edge next_values 0 = Znth edge next_values (-1).
Proof.
  intros g vertex_count edge_count head_values to_values weight_values
    next_values u edge Hsize Hmodel Hu Hchain Hedge.
  pose proof (forward_star_model_chain_wf _ _ _ _ _ _ Hmodel) as Hchain_wf.
  destruct (forward_star_model_edge_index_zlengths _ _ _ _ _ _ _ Hmodel Hedge)
    as (Hedge_to & Hedge_next).
  pose proof
    (graph_has_size_vertex_valid_storage _ _ _ Hsize Hu)
    as Hu_storage.
  destruct (forward_star_model_edge_bounds _ _ _ _ _ _ _ Hmodel Hedge)
    as (Hto_bounds & Hto_storage & _ & _).
  assert (Hto_valid : vertex_valid g (Znth edge to_values 0))
    by dijkstra_bounds_cleanup.
  pose proof
    (forward_star_edge_step_aux_and_weight
      g edge_count head_values to_values weight_values next_values
      u (Znth edge to_values 0) (Znth edge weight_values 0)
      Hmodel Hu
      ltac:(unfold forward_star_edge; split; [exact Hu_storage |];
            exists edge; split; [exact Hchain |];
            split; [exact Hedge_to |]; split; reflexivity))
    as (Hstep & Hweight).
  assert (Hnext_eq : Znth edge next_values 0 = Znth edge next_values (-1))
    by (apply Znth_indep; exact Hedge_next).
  do 8 (split; [eassumption |]); eassumption.
Qed.

Lemma forward_star_done_edge_set_head_empty :
  forall g edge_count head_values to_values weight_values next_values u e_abs,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    vertex_valid g u ->
    ~ forward_star_done_edge_set
        head_values to_values weight_values next_values u
        (Znth u head_values 0) e_abs.
Proof.
  intros g edge_count head_values to_values weight_values next_values
    u e_abs Hmodel Hu Hdone.
  unfold forward_star_done_edge_set in Hdone.
  destruct Hdone as (Hout & Hnot_suffix).
  unfold forward_star_outgoing_edge_set in Hout.
  destruct Hout as (v & w & He_abs & Hedge).
  unfold forward_star_edge in Hedge.
  destruct Hedge as (Hu_storage & idx & Hchain & Hidx_to & Hto & Hweight).
  assert (Hhead_eq :
    Znth u head_values 0 = Znth u head_values (-1)).
  {
    apply Znth_indep.
    pose proof Hmodel as (_ & Hsize & _).
    destruct (forward_star_model_head_safe _ _ _ _ _ _ Hmodel)
      as (Hhead_len & _).
    unfold graph_has_size in Hsize.
    unfold vertex_valid, DijkstraGraph.vertex_valid in Hu.
    lia.
  }
  assert (Hhead_not_nil : Znth u head_values (-1) <> -1).
  {
    intro Hnil.
    rewrite Hnil in Hchain.
    eapply next_chain_minus_one_false; eauto.
  }
  apply Hnot_suffix.
  unfold forward_star_suffix_edge_set, forward_star_suffix_index.
  exists idx, v, w.
  split.
  - split.
    + rewrite Hhead_eq.
      exact Hhead_not_nil.
    + rewrite Hhead_eq.
      exact Hchain.
  - split; [exact He_abs |].
    split; [exact Hidx_to |].
    split; assumption.
Qed.

Lemma forward_star_done_edge_set_head_empty_equiv :
  forall g edge_count head_values to_values weight_values next_values u e_abs,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    vertex_valid g u ->
    forward_star_done_edge_set
      head_values to_values weight_values next_values u
      (Znth u head_values 0) e_abs <->
    False.
Proof.
  intros g edge_count head_values to_values weight_values next_values
    u e_abs Hmodel Hu.
  split.
  - eapply forward_star_done_edge_set_head_empty; eauto.
  - contradiction.
Qed.

Definition dijkstra_loop_math_bridge_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (queue_items : list (Z * Z)) : Prop :=
  dijkstra_loop_bridge_state g src visited_set dist_values queue_items /\
  visited_set_valid g visited_set /\
  dijkstra_math_invariant g src visited_set dist_values.

Lemma forward_star_head_0_nil_or_chain :
  forall g vertex_count edge_count head_values to_values weight_values
         next_values u,
    graph_has_size g vertex_count ->
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    vertex_valid g u ->
    Znth u head_values 0 = -1 \/
    next_chain next_values (Znth u head_values (-1))
      (Znth u head_values 0).
Proof.
  intros g vertex_count edge_count head_values to_values weight_values
    next_values u Hsize Hmodel Hu.
  pose proof
    (graph_has_size_vertex_valid_bounds
      g vertex_count u Hsize Hu) as (_ & Hu_bounds).
  pose proof
    (forward_star_model_head_case_0 _ _ _ _ _ _ _ _ Hsize Hmodel Hu_bounds)
    as Hhead_case.
  destruct Hhead_case as [Hnil | Hedge_index].
  - left. exact Hnil.
  - right.
    assert (Hhead_eq :
      Znth u head_values 0 = Znth u head_values (-1)).
    {
      apply Znth_indep.
      destruct (forward_star_model_head_safe _ _ _ _ _ _ Hmodel)
        as (Hhead_len & _).
      unfold graph_has_size in Hsize.
      lia.
    }
    rewrite Hhead_eq.
    apply next_chain_here.
    pose proof
      (forward_star_model_edge_index_zlengths
        _ _ _ _ _ _ _ Hmodel Hedge_index) as (_ & Hnext).
    rewrite Hhead_eq in Hnext.
    exact Hnext.
Qed.

Lemma forward_star_head_0_lower_bound :
  forall g vertex_count edge_count head_values to_values weight_values
         next_values u,
    graph_has_size g vertex_count ->
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    vertex_valid g u ->
    -1 <= Znth u head_values 0.
Proof.
  intros g vertex_count edge_count head_values to_values weight_values
    next_values u Hsize Hmodel Hu.
  pose proof
    (graph_has_size_vertex_valid_bounds
      g vertex_count u Hsize Hu) as (_ & Hu_bounds).
  pose proof
    (forward_star_model_head_case_0 _ _ _ _ _ _ _ _ Hsize Hmodel Hu_bounds)
    as Hhead_case.
  destruct Hhead_case as [Hnil | Hedge_index].
  - lia.
  - unfold edge_index in Hedge_index. lia.
Qed.

Lemma forward_star_next_0_lower_bound :
  forall g edge_count head_values to_values weight_values next_values edge,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_index edge_count edge ->
    -1 <= Znth edge next_values 0.
Proof.
  intros g edge_count head_values to_values weight_values next_values
    edge Hmodel Hedge_index.
  pose proof
    (forward_star_model_next_case_0 _ _ _ _ _ _ _ Hmodel Hedge_index)
    as Hnext_case.
  destruct Hnext_case as [Hnil | Hnext_index].
  - lia.
  - unfold edge_index in Hnext_index. lia.
Qed.

Lemma forward_star_next_0_nil_or_chain :
  forall g edge_count head_values to_values weight_values next_values u edge,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    next_chain next_values (Znth u head_values (-1)) edge ->
    edge_index edge_count edge ->
    Znth edge next_values 0 = -1 \/
    next_chain next_values (Znth u head_values (-1))
      (Znth edge next_values 0).
Proof.
  intros g edge_count head_values to_values weight_values next_values
    u edge Hmodel Hhead_edge Hedge_index.
  pose proof
    (forward_star_model_next_case_0 _ _ _ _ _ _ _ Hmodel Hedge_index)
    as Hnext_case.
  destruct Hnext_case as [Hnil | Hnext_index].
  - left. exact Hnil.
  - right.
    pose proof
      (forward_star_model_edge_index_zlengths
        _ _ _ _ _ _ _ Hmodel Hedge_index) as (_ & Hedge_next).
    assert (Hnext_eq :
      Znth edge next_values 0 = Znth edge next_values (-1)).
    {
      apply Znth_indep. exact Hedge_next.
    }
    rewrite Hnext_eq.
    eapply next_chain_trans; [exact Hhead_edge |].
    apply next_chain_next.
    + exact Hedge_next.
    + rewrite <- Hnext_eq.
      intro Hnil.
      rewrite Hnil in Hnext_index.
      unfold edge_index in Hnext_index. lia.
    + apply next_chain_here.
      pose proof
        (forward_star_model_edge_index_zlengths
          _ _ _ _ _ _ _ Hmodel Hnext_index) as (_ & Hnext_bound).
      rewrite Hnext_eq in Hnext_bound.
      exact Hnext_bound.
Qed.

Definition dijkstra_loop_math_model
    (g : DijkstraGraph.G) (src : Z)
    (queue_items : list (Z * Z)) (s : state) : Prop :=
  exists visited_set dist_values,
    graph_state_model g visited_set dist_values s /\
    dijkstra_loop_math_bridge_state
      g src visited_set dist_values queue_items.

Definition source_visited_set (src : Z) : Z -> Prop :=
  fun v => v = src.

Definition dijkstra_first_step_math_state
    (g : DijkstraGraph.G) (src : Z)
    (done : DijkstraGraph.E -> Prop)
    (dist_values : list Z) : Prop :=
  dijkstra_first_step_invariant g src done
    (dijkstra_array_state g (source_visited_set src) dist_values).

Lemma dijkstra_first_step_math_state_done_equiv :
  forall g src done1 done2 dist_values,
    (forall e, done1 e <-> done2 e) ->
    dijkstra_first_step_math_state g src done1 dist_values ->
    dijkstra_first_step_math_state g src done2 dist_values.
Proof.
  intros g src done1 done2 dist_values Hdone Hfirst.
  unfold dijkstra_first_step_math_state in *.
  pose proof
    (@Dijkstra.step_invariant_proper
      DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E
      DijkstraGraph.graph_instance g DijkstraGraph.weight_instance src)
    as Hproper.
  unfold Morphisms.Proper, Morphisms.respectful in Hproper.
  apply (proj1 (Hproper done1 done2 Hdone _ _ eq_refl)).
  exact Hfirst.
Qed.

Lemma initial_first_step_math_state_empty :
  forall g vertex_count src,
    graph_has_size g vertex_count ->
    vertex_valid g src ->
    dijkstra_first_step_math_state g src
      (fun _ : DijkstraGraph.E => False)
      (initial_dist_values src).
Proof.
  intros g vertex_count src Hsize Hsrc.
  pose proof
    (graph_has_size_vertex_valid_bounds
      g vertex_count src Hsize Hsrc) as (Hcount & Hsrc_bounds).
  pose proof
    (graph_has_size_vertex_valid_storage g vertex_count src Hsize Hsrc)
    as Hstorage_src.
  unfold dijkstra_first_step_math_state, Dijkstra.first_step_invariant.
  split.
  - intros v; rewrite dijkstra_array_state_visited_iff.
    unfold source_visited_set; sets_unfold.
    split.
    + intros (_ & Heq). symmetry. exact Heq.
    + intros Heq; subst v; split; [exact Hsrc | reflexivity].
  - split.
    + rewrite dijkstra_array_state_dist_valid by exact Hsrc.
      rewrite initial_dist_values_cell by exact Hstorage_src.
      destruct (Z.eq_dec src src) as [_ | Hcontra].
      * apply cell_as_distance_finite.
        unfold DijkstraGraph.infinity; lia.
      * contradiction Hcontra; reflexivity.
    + split.
      * intros v e _ Hfalse _. contradiction.
      * intros v Hneq_src _.
        destruct (vertex_valid_dec g v) as [Hvalid | Hinvalid].
        -- rewrite dijkstra_array_state_dist_valid by exact Hvalid.
           pose proof
             (graph_has_size_vertex_valid_storage
               g vertex_count v Hsize Hvalid) as Hv_storage.
           rewrite initial_dist_values_cell
             by (exact Hstorage_src || exact Hv_storage).
           destruct (Z.eq_dec v src) as [Heq | _].
           ++ contradiction.
           ++ unfold cell_as_distance, DijkstraGraph.cell_as_distance.
              destruct (Z.eq_dec DijkstraGraph.infinity
                DijkstraGraph.infinity) as [_ | Hcontra];
                [reflexivity | contradiction Hcontra; reflexivity].
        -- apply dijkstra_array_state_dist_invalid; exact Hinvalid.
Qed.

Lemma visited_set_add_cons :
  forall visited_set u,
    visited_set_add visited_set u (fun v => visited_set v \/ v = u).
Proof. unfold visited_set_add; tauto. Qed.

Lemma dijkstra_valid_epath_weight_some :
  forall (g : DijkstraGraph.G) (u : DijkstraGraph.V)
         (p : list DijkstraGraph.E) (v : DijkstraGraph.V),
    dijkstra_valid_epath g u p v ->
    exists w, dijkstra_epath_weight g p = Some w.
Proof.
  intros g u p v Hvalid.
  revert u v Hvalid.
  induction p as [| e p IHp]; intros u v Hvalid.
  - exists 0; rewrite epath_weight_nil; reflexivity.
  - apply (dijkstra_valid_epath_cons_inv g u e p v)
      in Hvalid as [mid [Hstep Hrest]].
    simpl in Hstep.
    destruct Hstep as (Heq & _ & _ & edge_weight & Hedge_weight).
    subst e.
    destruct (IHp mid v Hrest) as (rest_weight & Hrest_weight).
    rewrite epath_weight_cons.
    simpl; rewrite Hedge_weight, Hrest_weight.
    exists (edge_weight + rest_weight); reflexivity.
Qed.

Lemma min_value_weight_epath_in_vset_finite_path_not_none :
  forall (g : DijkstraGraph.G) u v S z p w,
    dijkstra_is_epath_through_vset g u p v S ->
    dijkstra_epath_weight g p = Some w ->
    dijkstra_min_epath_in_vset g u v S z ->
    z <> None.
Proof.
  intros g u v S z p w Hpath Hweight Hmin Hnone.
  subst z.
  unfold min_value_weight_epath_in_vset,
    min_value_of_subset_with_default,
    min_value_of_subset, min_object_of_subset in Hmin.
  destruct Hmin as [[Hmin _] | [Hall _]].
  - destruct Hmin as (p_min & (Hp_min & Hle_min) & Hweight_min).
    specialize (Hle_min p Hpath).
    rewrite Hweight_min, Hweight in Hle_min; exact Hle_min.
  - specialize (Hall p Hpath).
    rewrite Hweight in Hall; exact Hall.
Qed.

Lemma dijkstra_loop_math_model_nil_to_shortest :
  forall g vertex_count src dist_out s,
    graph_has_size g vertex_count ->
    vertex_valid g src ->
    graph_dist_model g dist_out s ->
    dijkstra_loop_math_model g src nil s ->
    dijkstra_shortest_dist g src dist_out.
Proof.
  intros g vertex_count src dist_out s Hsize Hsrc Hdist_out Hloop.
  unfold dijkstra_loop_math_model in Hloop.
  destruct Hloop as
    (visited_set & dist_values & Hstate & Hbridge_math).
  assert (Hreachable_visited :
    forall v, dijkstra_reachable g src v -> visited_set v).
  {
    intros v Hreach.
    destruct (classic (visited_set v)) as [Hvisited | Hunvisited].
    - exact Hvisited.
    - exfalso.
      pose proof Hbridge_math as Hbridge_reach.
      unfold dijkstra_loop_math_bridge_state,
        dijkstra_loop_bridge_state in Hbridge_reach.
      destruct Hbridge_reach as
        ((Hloop_state & Hrefines) & Hvisited_valid & Hmath).
      destruct Hrefines as
        (Hcovers & _Hexact & _Hlower & _Hfinite & _Hnodup).
      pose proof (dijkstra_reachable_valid_epath g src v Hreach)
        as (p & Hvalid_path).
      assert (Hwf : DijkstraGraph.graph_wf g)
        by (unfold dijkstra_loop_state in Hloop_state; tauto).
      pose proof
        (dijkstra_is_epath_through_vset_greedy_cut
          g Hwf src p v visited_set Hvalid_path Hunvisited)
        as (frontier & prefix & suffix &
            Hprefix & Hfrontier_unvisited & _Hsuffix & _Hpath_eq).
      destruct Hprefix as (Hprefix_valid & Hprefix_prop).
      assert (Hfrontier_reach : dijkstra_reachable g src frontier)
        by (eapply dijkstra_valid_epath_reachable; exact Hprefix_valid).
      assert (Hfrontier_valid : vertex_valid g frontier)
        by (eapply dijkstra_reachable_vertex_valid; eauto).
      assert (Hprefix_state :
        dijkstra_is_epath_through_vset
          g src prefix frontier
          (@visited Z
            (dijkstra_array_state g visited_set dist_values))).
      {
        eapply dijkstra_is_epath_through_vset_subset.
        - exact (conj Hprefix_valid Hprefix_prop).
        - intros x Hx.
          apply dijkstra_array_state_visited_iff.
          split.
          + apply Hvisited_valid. exact Hx.
          + exact Hx.
      }
      assert (Hfrontier_unvisited_state :
        ~ @visited Z
            (dijkstra_array_state g visited_set dist_values) frontier)
        by (intro Hvisited_state;
            rewrite dijkstra_array_state_visited_iff in Hvisited_state; tauto).
      unfold dijkstra_math_invariant in Hmath.
      destruct Hmath as (_Hfinal & Hoptimal & _Hcross).
      pose proof (Hoptimal frontier Hfrontier_unvisited_state)
        as Hfrontier_min.
      pose proof
        (dijkstra_valid_epath_weight_some
          g src prefix frontier Hprefix_valid)
        as (prefix_weight & Hprefix_weight).
      assert (Hdist_not_none :
        @dist Z (dijkstra_array_state g visited_set dist_values)
          frontier <> None).
      { eapply min_value_weight_epath_in_vset_finite_path_not_none; eauto. }
      rewrite dijkstra_array_state_dist_valid in Hdist_not_none
        by exact Hfrontier_valid.
      pose proof
        (graph_has_size_vertex_valid_storage _ _ _ Hsize Hfrontier_valid)
        as Hfrontier_storage.
      destruct Hloop_state as (_ & _ & _ & _ & Hsafe & _).
      assert (Hfrontier_finite :
        dist_cell dist_values frontier < DijkstraGraph.infinity).
      {
        unfold cell_as_distance, DijkstraGraph.cell_as_distance
          in Hdist_not_none.
        destruct (Z.eq_dec (dist_cell dist_values frontier)
          DijkstraGraph.infinity) as [Heq_inf | Hneq_inf].
        - contradiction Hdist_not_none.
          reflexivity.
        - pose proof (Hsafe frontier Hfrontier_storage); lia.
      }
      pose proof
        (Hcovers frontier Hfrontier_valid
          Hfrontier_unvisited Hfrontier_finite) as Hin.
      simpl in Hin.
      contradiction.
  }
  destruct Hbridge_math as (_Hbridge & _Hvisited_valid & Hmath).
  destruct Hstate as (Hdist_internal & _Hvisited_model & _Hinvalid).
  destruct Hdist_out as (Hshape_out & Hsafe_out & Hcells_out).
  assert (Hcells :
    forall v,
      vertex_valid g v ->
      dist_cell dist_values v = dist_cell dist_out v).
  {
    intros v Hvalid.
    destruct Hdist_internal as
      (_Hshape_internal & _Hsafe_internal & Hcells_internal).
    rewrite (Hcells_internal v Hvalid), (Hcells_out v Hvalid); reflexivity.
  }
  exists (dijkstra_array_state g visited_set dist_out).
  split.
  - apply graph_state_model_to_graph_dist_model
      with (visited_set := visited_set).
    apply dijkstra_array_state_graph_state_model
      with (vertex_count := vertex_count).
    + exact Hsize.
    + exact Hshape_out.
    + exact Hsafe_out.
  - unfold distance_correct in *; intros v Hreach.
    assert (Hdist :
      @dist Z (dijkstra_array_state g visited_set dist_out) v =
      @dist Z (dijkstra_array_state g visited_set dist_values) v).
    {
      destruct (vertex_valid_dec g v) as [Hvalid | Hinvalid].
      - rewrite !dijkstra_array_state_dist_valid by exact Hvalid.
        rewrite <- Hcells by exact Hvalid; reflexivity.
      - rewrite !dijkstra_array_state_dist_invalid by exact Hinvalid; reflexivity.
    }
    change (dijkstra_min_epath g src v
      (@dist Z (dijkstra_array_state g visited_set dist_out) v)).
    rewrite Hdist.
    destruct Hmath as (Hfinal & _ & _).
    apply Hfinal.
    apply dijkstra_array_state_visited_iff;
      split; eauto using dijkstra_reachable_vertex_valid.
Qed.

End DijkstraLinkedForwardStar.
