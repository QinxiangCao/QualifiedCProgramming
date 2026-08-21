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
Require Import Logic.LogicGenerator.demo932.Interface.
From SimpleC.EE.LLM_bench.Algorithms.Dijkstra Require Export concrete_graphs.

Import ListNotations.
Import SetsNotation.
Import MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope monad.

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

Notation dijkstra_step_aux := (@step_aux DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance).
Notation dijkstra_weight := (@weight DijkstraGraph.G DijkstraGraph.E DijkstraGraph.weight_instance).
Notation dijkstra_valid_epath := (@valid_epath DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance).
Notation dijkstra_epath_weight := (@epath_weight DijkstraGraph.G DijkstraGraph.E DijkstraGraph.weight_instance).
Notation dijkstra_is_epath_through_vset := (@is_epath_through_vset DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance).
Notation dijkstra_reachable := (@reachable DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance).
Notation dijkstra_min_epath := (@min_value_weight_epath DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.weight_instance).
Notation dijkstra_min_epath_in_vset := (@min_value_weight_epath_in_vset DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance DijkstraGraph.PathData DijkstraGraph.path_instance DijkstraGraph.weight_instance).

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

Definition dijkstra_nonnegative_edges (g : DijkstraGraph.G) : Prop :=
  forall e,
    Z_op_le (Some 0)
      (dijkstra_weight g e).

Definition dijkstra_no_overflow
    (g : DijkstraGraph.G) (src : Z) : Prop :=
  forall u v du w,
    vertex_valid g u ->
    vertex_valid g v ->
    dijkstra_min_epath g src u (Some du) ->
    DijkstraGraph.edge_weight g u v = Some w ->
    0 <= du + w < DijkstraGraph.infinity.

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

Definition priority_queue_model
    (vertices distances : list Z) (size : Z)
    (items : list (Z * Z)) : Prop :=
  Zlength vertices = max_priority_queue_size /\
  Zlength distances = max_priority_queue_size /\
  0 <= size <= Zlength vertices /\
  Zlength items = size /\
  (forall i,
    0 <= i < size ->
    Znth i items (0, 0) =
      (Znth i distances DijkstraGraph.infinity, Znth i vertices 0) /\
    storage_index (snd (Znth i items (0, 0))) /\
    0 <= fst (Znth i items (0, 0)) <= DijkstraGraph.infinity) /\
  priority_queue_ordered items.

Lemma priority_queue_model_size_bounds :
  forall vertices distances size items,
    priority_queue_model vertices distances size items ->
    0 <= size <= max_priority_queue_size /\
    Zlength items = size.
Proof.
  intros vertices distances size items Hmodel.
  unfold priority_queue_model, max_priority_queue_size in *.
  dijkstra_cleanup.
Qed.

Lemma priority_queue_model_ordered :
  forall vertices distances size items,
    priority_queue_model vertices distances size items ->
    priority_queue_ordered items.
Proof. unfold priority_queue_model; tauto. Qed.

Fixpoint priority_queue_insert
    (item : Z * Z) (items : list (Z * Z)) : list (Z * Z) :=
  match items with
  | nil => item :: nil
  | item0 :: items_tail =>
      if Z.leb (fst item) (fst item0)
      then item :: items
      else item0 :: priority_queue_insert item items_tail
  end.

Definition priority_queue_push_result
    (items items_out : list (Z * Z)) (vertex distance : Z) : Prop :=
  items_out = priority_queue_insert (distance, vertex) items.

Lemma priority_queue_push_result_nil_inv :
  forall items vertex distance,
    priority_queue_push_result nil items vertex distance ->
    items = (distance, vertex) :: nil.
Proof. auto. Qed.

Lemma priority_queue_push_result_exists :
  forall items vertex distance,
    exists items_out,
      priority_queue_push_result items items_out vertex distance.
Proof. intros; eexists; reflexivity. Qed.

Definition priority_queue_pop_result
    (items items_out : list (Z * Z)) (vertex distance : Z) : Prop :=
  items <> nil /\
  items = (distance, vertex) :: items_out /\
  priority_queue_ordered items.

Lemma priority_queue_pop_result_cons :
  forall items items_out vertex distance,
    priority_queue_pop_result items items_out vertex distance ->
    items = (distance, vertex) :: items_out.
Proof.
  intros items items_out vertex distance Hpop.
  unfold priority_queue_pop_result in Hpop.
  tauto.
Qed.

Ltac dijkstra_pop_cons :=
  match goal with
  | H : priority_queue_pop_result ?items ?items_out ?vertex ?distance |- _ =>
      pose proof
        (priority_queue_pop_result_cons
          items items_out vertex distance H);
      subst items; simpl in *
  end.

Lemma priority_queue_pop_result_exists :
  forall vertices distances items,
    priority_queue_model vertices distances (Zlength items) items ->
    Zlength items <> 0 ->
    exists items_out vertex distance,
      priority_queue_pop_result items items_out vertex distance.
Proof.
  intros vertices distances items Hmodel Hnonempty.
  destruct items as [| item items_tail].
  - rewrite Zlength_nil in Hnonempty; contradiction.
  - destruct item as [distance vertex].
    exists items_tail, vertex, distance.
    unfold priority_queue_pop_result.
    split; [discriminate | split; [reflexivity |]].
    eapply priority_queue_model_ordered; exact Hmodel.
Qed.

Lemma priority_queue_pop_result_bounds :
  forall vertices distances items items_out vertex distance,
    priority_queue_model vertices distances (Zlength items) items ->
    priority_queue_pop_result items items_out vertex distance ->
    storage_index vertex /\
    0 <= vertex < DijkstraGraph.max_vertices /\
    0 <= distance <= DijkstraGraph.infinity.
Proof.
  intros vertices distances items items_out vertex distance Hmodel Hpop.
  dijkstra_pop_cons.
  unfold priority_queue_model in Hmodel.
  destruct Hmodel as (_ & _ & _ & _ & Hitems & _).
  pose proof (Hitems 0) as Hbounds.
  pose proof (Zlength_nonneg items_out).
  specialize (Hbounds ltac:(rewrite Zlength_cons; lia)).
  simpl in Hbounds; unfold storage_index in *; lia.
Qed.

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

Lemma priority_queue_insert_in_inv :
  forall item items item0,
    In item0 (priority_queue_insert item items) ->
    item0 = item \/ In item0 items.
Proof.
  intros item items.
  induction items as [| item1 items_tail IH]; simpl; intros item0 Hin.
  - destruct Hin as [<- | []]; auto.
  - destruct (Z.leb (fst item) (fst item1)); simpl in *.
    + destruct Hin as [<- | Hin]; auto.
    + destruct Hin as [<- | Hin].
      * right; auto.
      * destruct (IH item0 Hin); auto.
Qed.

Lemma priority_queue_insert_in_old :
  forall item items item0,
    In item0 items ->
    In item0 (priority_queue_insert item items).
Proof.
  intros item items.
  induction items as [| item1 items_tail IH]; simpl; intros item0 Hin.
  - contradiction.
  - destruct (Z.leb (fst item) (fst item1)); simpl in *; intuition.
Qed.

Lemma priority_queue_insert_in_new :
  forall item items,
    In item (priority_queue_insert item items).
Proof.
  intros item items.
  induction items as [| item1 items_tail IH].
  - simpl; auto.
  - simpl.
    destruct (Z.leb (fst item) (fst item1)).
    + simpl; auto.
    + simpl; auto.
Qed.

Lemma priority_queue_insert_nodup :
  forall item items,
    NoDup items ->
    ~ In item items ->
    NoDup (priority_queue_insert item items).
Proof.
  intros item items.
  induction items as [| item1 items_tail IH]; intros Hnodup Hnotin.
  - simpl. constructor; [tauto | constructor].
  - simpl.
    inversion Hnodup as [| ? ? Hitem1_notin_tail Htail_nodup]; subst.
    destruct (Z.leb (fst item) (fst item1)).
    + constructor.
      * exact Hnotin.
      * exact Hnodup.
    + constructor.
      * intro Hin.
        destruct (priority_queue_insert_in_inv item items_tail item1 Hin)
          as [Heq | Hin_tail].
        -- subst item1.
           apply Hnotin. simpl. left. reflexivity.
        -- apply Hitem1_notin_tail. exact Hin_tail.
      * apply IH.
        -- exact Htail_nodup.
        -- intro Hin_tail.
           apply Hnotin. simpl. right. exact Hin_tail.
Qed.

Definition priority_queue_vertices_valid
    (g : DijkstraGraph.G) (items : list (Z * Z)) : Prop :=
  forall item,
    In item items ->
    vertex_valid g (snd item).

Lemma priority_queue_push_result_vertices_valid :
  forall g items items_out vertex distance,
    priority_queue_vertices_valid g items ->
    vertex_valid g vertex ->
    priority_queue_push_result items items_out vertex distance ->
    priority_queue_vertices_valid g items_out.
Proof.
  intros g items items_out vertex distance Hvalid Hvertex Hpush.
  unfold priority_queue_push_result in Hpush.
  subst items_out.
  unfold priority_queue_vertices_valid in *.
  intros item Hin.
  destruct (priority_queue_insert_in_inv _ _ _ Hin) as [Hitem | Hin_items].
  - subst item; exact Hvertex.
  - exact (Hvalid item Hin_items).
Qed.

Lemma priority_queue_push_result_nil_vertices_valid :
  forall g items vertex distance,
    vertex_valid g vertex ->
    priority_queue_push_result nil items vertex distance ->
    priority_queue_vertices_valid g items.
Proof.
  intros g items vertex distance Hvertex Hpush.
  pose proof (priority_queue_push_result_nil_inv items vertex distance Hpush)
    as Hitems.
  subst items.
  unfold priority_queue_vertices_valid.
  intros item Hin.
  simpl in Hin; destruct Hin as [Hitem | []]; subst; exact Hvertex.
Qed.

Lemma priority_queue_insert_ordered :
  forall item items,
    priority_queue_ordered items ->
    priority_queue_ordered (priority_queue_insert item items).
Proof.
  intros item items.
  induction items as [| item1 items_tail IH]; intros Hordered.
  - simpl. tauto.
  - simpl in *.
    destruct Hordered as (Hhead & Htail).
    destruct (Z.leb (fst item) (fst item1)) eqn:Hle.
    + apply Z.leb_le in Hle.
      split.
      * intros item0 Hin.
        simpl in Hin; destruct Hin as [Heq | Hin_tail];
          [subst item0 | specialize (Hhead item0 Hin_tail)]; lia.
      * split; assumption.
    + apply Z.leb_gt in Hle.
      split.
      * intros item0 Hin.
        destruct (priority_queue_insert_in_inv item items_tail item0 Hin)
          as [Heq | Hin_tail]; [subst item0; lia | auto].
      * apply IH. exact Htail.
Qed.

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

Definition priority_queue_pop_choice
    (items : list (Z * Z))
    : program state ((list (Z * Z) * Z) * Z) :=
  get (fun _ result =>
    priority_queue_pop_result
      items
      (fst (fst result))
      (snd (fst result))
      (snd result)).

Definition priority_queue_push_choice
    (items : list (Z * Z)) (vertex distance : Z)
    : program state (list (Z * Z)) :=
  get (fun _ items_out =>
    priority_queue_push_result items items_out vertex distance).

Definition dijkstra_lfs_edge_body
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance : Z)
    (acc : Z * list (Z * Z))
    : program state (CntOrBrk (Z * list (Z * Z)) (list (Z * Z))) :=
  let edge := fst acc in
  let queue_items := snd acc in
  choice
    (assume (fun _ => edge = -1);;
     ret (by_break queue_items))
    (assume (fun _ => edge <> -1);;
     let neighbor := Znth edge to_values 0 in
     let edge_weight := Znth edge weight_values 0 in
     let candidate := cur_distance + edge_weight in
     let next_edge := Znth edge next_values 0 in
     choice
       (assume (fun s =>
          0 <= edge_weight /\
          cur_distance <= DijkstraGraph.infinity - edge_weight /\
          candidate < state_distance_cell neighbor s);;
        update' (set_state_distance neighbor candidate);;
        queue_items_after <-
          priority_queue_push_choice queue_items neighbor candidate;;
        ret (by_continue (next_edge, queue_items_after)))
       (assume (fun s =>
          edge_weight < 0 \/
          cur_distance > DijkstraGraph.infinity - edge_weight \/
          candidate >= state_distance_cell neighbor s);;
        ret (by_continue (next_edge, queue_items)))).

Ltac dijkstra_edge_body_hoare :=
  unfold dijkstra_lfs_edge_body;
  apply Hoare_choice;
  [ apply Hoare_assume_bind;
    apply Hoare_ret';
    intros s [Hedge_nil Hpre];
    cbn [fst snd] in Hedge_nil
  | apply Hoare_assume_bind;
    apply Hoare_choice;
    [ apply Hoare_assume_bind;
      eapply Hoare_bind;
      [ apply Hoare_update
      | intros [];
        eapply Hoare_bind;
        [ apply Hoare_get
        | intros queue_items_after;
          apply Hoare_ret';
          intros s Hpost;
          destruct Hpost as (Hpush & s0 & Hset & Hpre);
          destruct Hpre as (Hrelax_assume & Hedge_not_nil & Hpre);
          cbn [fst snd] in Hpush, Hrelax_assume, Hedge_not_nil;
          subst s ] ]
    | apply Hoare_assume_bind;
      apply Hoare_ret';
      intros s [Hskip [Hedge_not_nil Hpre]];
      cbn [fst snd] in Hskip, Hedge_not_nil ] ].

Definition dijkstra_lfs_edge_loop
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance edge : Z)
    (queue_items : list (Z * Z))
    : program state (list (Z * Z)) :=
  repeat_break
    (dijkstra_lfs_edge_body
      head_values to_values weight_values next_values
      cur_vertex cur_distance)
    (edge, queue_items).

Definition dijkstra_lfs_loop_body
    (head_values to_values weight_values next_values : list Z)
    (queue_items : list (Z * Z))
    : program state (CntOrBrk (list (Z * Z)) unit) :=
  choice
    (assume (fun _ => queue_items = nil);;
     ret (by_break tt))
    (assume (fun _ => queue_items <> nil);;
     pop_result <- priority_queue_pop_choice queue_items;;
     let queue_items_after := fst (fst pop_result) in
     let cur_vertex := snd (fst pop_result) in
     let cur_distance := snd pop_result in
     choice
      (assume (fun s =>
         cur_distance = state_distance_cell cur_vertex s);;
        update' (set_state_visited cur_vertex);;
        queue_items_after_edges <-
          dijkstra_lfs_edge_loop
            head_values to_values weight_values next_values
            cur_vertex cur_distance
            (Znth cur_vertex head_values 0)
            queue_items_after;;
        ret (by_continue queue_items_after_edges))
       (assume (fun s =>
          cur_distance <> state_distance_cell cur_vertex s);;
        ret (by_continue queue_items_after))).

Ltac dijkstra_loop_body_hoare :=
  unfold dijkstra_lfs_loop_body;
  match goal with
  | |- Hoare _ _ ?Post =>
      apply Hoare_choice;
      [ apply Hoare_assume_bind;
        apply Hoare_ret';
        intros s [Hempty Hpre]
      | apply Hoare_assume_bind;
        eapply Hoare_bind;
        [ apply Hoare_get
        | intros [[queue_items_after cur_vertex] cur_distance];
          cbn [fst snd];
          apply Hoare_choice;
          [ apply Hoare_assume_bind;
            eapply Hoare_bind;
            [ apply Hoare_update
            | intros [];
              eapply Hoare_bind
                with (Q := fun queue_items_after_edges s =>
                  Post (by_continue queue_items_after_edges) s);
              [ idtac
              | intros queue_items_after_edges;
                apply Hoare_ret';
                intros s Hloop;
                exact Hloop ] ]
          | apply Hoare_assume_bind;
            apply Hoare_ret';
            intros s [Hneq_dist Hpre];
            destruct Hpre as (Hpop & Hpre);
            destruct Hpre as (Hnonempty & Hpre) ] ] ]
  end.

Definition dijkstra_lfs_loop
    (head_values to_values weight_values next_values : list Z)
    (queue_items : list (Z * Z)) : program state unit :=
  repeat_break
    (dijkstra_lfs_loop_body
      head_values to_values weight_values next_values)
    queue_items.

Definition dijkstra_lfs_program
    (src : Z)
    (head_values to_values weight_values next_values : list Z)
    : program state unit :=
  dijkstra_lfs_loop head_values to_values weight_values next_values
    ((0, src) :: nil).

Definition dijkstra_lfs_edge_loop_after_body_cont
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance : Z)
    (step_result : CntOrBrk (Z * list (Z * Z)) (list (Z * Z)))
    : program state unit :=
  queue_items_after <-
    match step_result with
    | by_continue edge_state =>
        repeat_break
          (dijkstra_lfs_edge_body
            head_values to_values weight_values next_values
            cur_vertex cur_distance)
          edge_state
    | by_break queue_items_done => ret queue_items_done
    end;;
  dijkstra_lfs_loop
    head_values to_values weight_values next_values
    queue_items_after.

Definition dijkstra_lfs_edge_loop_cont
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance edge : Z)
    (queue_items : list (Z * Z)) : program state unit :=
  queue_items_after <-
    dijkstra_lfs_edge_loop
      head_values to_values weight_values next_values
      cur_vertex cur_distance edge queue_items;;
  dijkstra_lfs_loop
    head_values to_values weight_values next_values
    queue_items_after.

Definition dijkstra_lfs_after_pop_cont
    (head_values to_values weight_values next_values : list Z)
    (queue_items_after : list (Z * Z))
    (cur_vertex cur_distance : Z) : program state unit :=
  step_result <-
    choice
      (assume (fun s =>
         cur_distance = state_distance_cell cur_vertex s);;
       update' (set_state_visited cur_vertex);;
       queue_items_after_edges <-
         dijkstra_lfs_edge_loop
           head_values to_values weight_values next_values
           cur_vertex cur_distance
           (Znth cur_vertex head_values 0)
           queue_items_after;;
       ret (by_continue queue_items_after_edges))
      (assume (fun s =>
         cur_distance <> state_distance_cell cur_vertex s);;
       ret (by_continue queue_items_after));;
  match step_result with
  | by_continue queue_items_next =>
      dijkstra_lfs_loop
        head_values to_values weight_values next_values
        queue_items_next
  | by_break done => ret done
  end.

Definition dijkstra_loop_refines
    (g : DijkstraGraph.G) (src : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (queue_items : list (Z * Z)) (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (dijkstra_lfs_loop head_values to_values weight_values next_values
      queue_items)
    X.

Definition dijkstra_after_pop_refines
    (g : DijkstraGraph.G) (src : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (queue_items_after : list (Z * Z))
    (cur_vertex cur_distance : Z) (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (dijkstra_lfs_after_pop_cont head_values to_values weight_values
      next_values queue_items_after cur_vertex cur_distance)
    X.

Definition dijkstra_edge_loop_refines
    (g : DijkstraGraph.G) (src cur_vertex cur_distance edge : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (queue_items : list (Z * Z)) (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (dijkstra_lfs_edge_loop_cont head_values to_values weight_values
      next_values cur_vertex cur_distance edge queue_items)
    X.

Definition dijkstra_lfs_initial_refines
    (g : DijkstraGraph.G) (src : Z)
    (head_values to_values weight_values next_values : list Z)
    (X : unit -> state -> Prop) : Prop :=
  safeExec (eq (initial_state src))
    (dijkstra_lfs_program
      src head_values to_values weight_values next_values)
    X.

Definition dijkstra_after_relax_refines
    (g : DijkstraGraph.G) (src cur_vertex cur_distance edge
       neighbor candidate : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (queue_items : list (Z * Z)) (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (queue_items_after <-
       priority_queue_push_choice queue_items neighbor candidate;;
     dijkstra_lfs_edge_loop_cont head_values to_values weight_values
       next_values cur_vertex cur_distance
       (Znth edge next_values 0) queue_items_after)
    X.

Lemma dijkstra_lfs_edge_loop_cont_unfold :
  forall head_values to_values weight_values next_values
         cur_vertex cur_distance edge queue_items,
    Sets.equiv
      (dijkstra_lfs_edge_loop_cont
        head_values to_values weight_values next_values
        cur_vertex cur_distance edge queue_items)
      (step_result <-
        dijkstra_lfs_edge_body
          head_values to_values weight_values next_values
          cur_vertex cur_distance (edge, queue_items);;
       dijkstra_lfs_edge_loop_after_body_cont
        head_values to_values weight_values next_values
        cur_vertex cur_distance step_result).
Proof.
  intros; unfold dijkstra_lfs_edge_loop_cont, dijkstra_lfs_edge_loop,
    dijkstra_lfs_edge_loop_after_body_cont.
  rewrite (repeat_break_unfold (dijkstra_lfs_edge_body head_values
    to_values weight_values next_values cur_vertex cur_distance)
    (edge, queue_items)), bind_assoc; reflexivity.
Qed.

Ltac lfs_prog_nf H := repeat (prog_nf in H).

Ltac lfs_finish_equiv :=
  repeat (rewrite bind_assoc || rewrite ret_equiv || rewrite ret_equiv');
  reflexivity.

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

Lemma dijkstra_lfs_initial_to_loop_refines :
  forall g vertex_count src head_values to_values weight_values next_values
         visited_set dist_values queue_items X,
    graph_has_size g vertex_count ->
    visited_set_empty visited_set ->
    dijkstra_init_dist vertex_count src dist_values ->
    priority_queue_push_result nil queue_items src 0 ->
    dijkstra_lfs_initial_refines
      g src head_values to_values weight_values next_values X ->
    dijkstra_loop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values queue_items X.
Proof.
  intros g vertex_count src head_values to_values weight_values next_values
    visited_set dist_values queue_items X Hsize Hempty Hinit Hpush Hrefines.
  unfold dijkstra_lfs_initial_refines in Hrefines.
  unfold dijkstra_lfs_program in Hrefines.
  unfold dijkstra_loop_refines.
  pose proof
    (priority_queue_push_result_nil_inv queue_items src 0 Hpush)
    as Hqueue.
  subst queue_items.
  eapply safeExec_conseq.
  - exact Hrefines.
  - intros s Hs.
    subst s.
    apply dijkstra_init_dist_graph_state_model_initial
      with (vertex_count := vertex_count); auto.
Qed.

Lemma dijkstra_loop_refines_empty_to_return :
  forall g src head_values to_values weight_values next_values
         visited_set dist_values queue_items X,
    queue_items = nil ->
    dijkstra_loop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values queue_items X ->
    safeExec (graph_state_model g visited_set dist_values) (return tt) X.
Proof.
  intros g src head_values to_values weight_values next_values
    visited_set dist_values queue_items X Hempty Hrefines.
  subst queue_items.
  unfold dijkstra_loop_refines in Hrefines.
  unfold dijkstra_lfs_loop in Hrefines.
  eapply safeExec_proequiv in Hrefines.
  2: { apply repeat_break_unfold. }
  unfold dijkstra_lfs_loop_body in Hrefines.
  eapply safeExec_bind_reta with (a := by_break tt) in Hrefines.
  - simpl in Hrefines.
    exact Hrefines.
  - intros Xbody Hbody.
    apply safeExec_choice_l in Hbody.
    eapply safeExec_testst_bind in Hbody.
    + exact Hbody.
    + intros s _.
      reflexivity.
Qed.

Lemma dijkstra_loop_refines_pop :
  forall g src head_values to_values weight_values next_values
         visited_set dist_values queue_items queue_items_after cur_vertex
         cur_distance X,
    priority_queue_pop_result queue_items queue_items_after
      cur_vertex cur_distance ->
    dijkstra_loop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values queue_items X ->
    dijkstra_after_pop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values queue_items_after cur_vertex cur_distance X.
Proof.
  intros g src head_values to_values weight_values next_values
    visited_set dist_values queue_items queue_items_after cur_vertex cur_distance X
    Hpop Hrefines.
  assert (Hnotnil : queue_items <> nil).
  {
    unfold priority_queue_pop_result in Hpop.
    tauto.
  }
  unfold dijkstra_loop_refines in Hrefines.
  unfold dijkstra_after_pop_refines.
  unfold dijkstra_lfs_loop in Hrefines.
  eapply safeExec_proequiv in Hrefines.
  2: { apply repeat_break_unfold. }
  unfold dijkstra_lfs_loop_body in Hrefines.
  lfs_prog_nf Hrefines.
  apply safeExec_choice_r in Hrefines.
  lfs_prog_nf Hrefines.
  eapply safeExec_testst_bind in Hrefines.
  2: { intros s _. exact Hnotnil. }
  lfs_prog_nf Hrefines.
  unfold priority_queue_pop_choice in Hrefines.
  lfs_prog_nf Hrefines.
  eapply safeExec_get_bind with
    (a := ((queue_items_after, cur_vertex), cur_distance)) in Hrefines.
  2: { intros s _. exact Hpop. }
  cbn in Hrefines.
  lfs_prog_nf Hrefines.
  unfold dijkstra_lfs_after_pop_cont.
  unfold dijkstra_lfs_loop.
  unfold dijkstra_lfs_loop_body.
  unfold priority_queue_pop_choice.
  cbn.
  eapply safeExec_proequiv.
  2: { exact Hrefines. }
  symmetry.
  rewrite bind_choice_equiv.
  repeat rewrite bind_assoc; reflexivity.
Qed.

Lemma dijkstra_after_pop_refines_equal_to_edge_loop :
  forall g src head_values to_values weight_values next_values
         visited_set visited_set' dist_values queue_items_after
         cur_vertex cur_distance X,
    vertex_valid g cur_vertex ->
    visited_set_add visited_set cur_vertex visited_set' ->
    dist_cell dist_values cur_vertex = cur_distance ->
    dijkstra_after_pop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values queue_items_after cur_vertex cur_distance X ->
    dijkstra_edge_loop_refines
      g src cur_vertex cur_distance (Znth cur_vertex head_values 0)
      head_values to_values weight_values next_values
      visited_set' dist_values queue_items_after X.
Proof.
  intros g src head_values to_values weight_values next_values
    visited_set visited_set' dist_values queue_items_after
    cur_vertex cur_distance X Hvalid Hvisit_add Hdist Hrefines.
  unfold dijkstra_after_pop_refines in Hrefines.
  unfold dijkstra_lfs_after_pop_cont in Hrefines.
  lfs_prog_nf Hrefines.
  apply safeExec_choice_l in Hrefines.
  lfs_prog_nf Hrefines.
  eapply safeExec_testst_bind in Hrefines.
  2: {
    intros s Hmodel.
    erewrite graph_state_model_dist_cell by eauto.
    symmetry.
    exact Hdist.
  }
  lfs_prog_nf Hrefines.
  apply safeExec_update'_bind in Hrefines.
  lfs_prog_nf Hrefines.
  unfold dijkstra_edge_loop_refines.
  unfold dijkstra_lfs_edge_loop_cont.
  unfold dijkstra_lfs_loop.
  eapply safeExec_conseq.
  - eapply safeExec_proequiv.
    2: { exact Hrefines. }
    lfs_finish_equiv.
  - intros s (s0 & Hs & Hmodel).
    subst s.
    apply graph_state_model_visit_state with (visited_set := visited_set);
      auto.
Qed.

Lemma dijkstra_after_pop_refines_not_equal_to_loop :
  forall g src head_values to_values weight_values next_values
         visited_set dist_values queue_items_after cur_vertex cur_distance X,
    vertex_valid g cur_vertex ->
    cur_distance <> dist_cell dist_values cur_vertex ->
    dijkstra_after_pop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values queue_items_after cur_vertex cur_distance X ->
    dijkstra_loop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values queue_items_after X.
Proof.
  intros g src head_values to_values weight_values next_values
    visited_set dist_values queue_items_after cur_vertex cur_distance X
    Hvalid Hdist_neq Hrefines.
  unfold dijkstra_after_pop_refines in Hrefines.
  unfold dijkstra_lfs_after_pop_cont in Hrefines.
  lfs_prog_nf Hrefines.
  apply safeExec_choice_r in Hrefines.
  lfs_prog_nf Hrefines.
  eapply safeExec_testst_bind in Hrefines.
  2: {
    intros s Hmodel.
    erewrite graph_state_model_dist_cell by eauto.
    exact Hdist_neq.
  }
  unfold dijkstra_loop_refines.
  eapply safeExec_proequiv.
  2: { exact Hrefines. }
  lfs_finish_equiv.
Qed.

Lemma dijkstra_after_relax_refines_push_to_edge_loop :
  forall g src cur_vertex cur_distance edge neighbor candidate
         head_values to_values weight_values next_values visited_set dist_values
         queue_items push_items_after X,
    priority_queue_push_result queue_items push_items_after
      neighbor candidate ->
    dijkstra_after_relax_refines
      g src cur_vertex cur_distance edge neighbor candidate
      head_values to_values weight_values next_values
      visited_set dist_values queue_items X ->
    dijkstra_edge_loop_refines
      g src cur_vertex cur_distance (Znth edge next_values 0)
      head_values to_values weight_values next_values
      visited_set dist_values push_items_after X.
Proof.
  intros g src cur_vertex cur_distance edge neighbor candidate
    head_values to_values weight_values next_values visited_set dist_values
    queue_items push_items_after X Hpush Hrefines.
  unfold dijkstra_after_relax_refines in Hrefines.
  unfold priority_queue_push_choice in Hrefines.
  eapply safeExec_get_bind with (a := push_items_after) in Hrefines.
  2: { intros s _. exact Hpush. }
  unfold dijkstra_edge_loop_refines.
  exact Hrefines.
Qed.

Lemma dijkstra_edge_loop_refines_relax_to_after_relax :
  forall g vertex_count src cur_vertex cur_distance edge neighbor
         edge_weight candidate
         head_values to_values weight_values next_values visited_set dist_values
         queue_items X,
    graph_has_size g vertex_count ->
    edge <> -1 ->
    neighbor = Znth edge to_values 0 ->
    edge_weight = Znth edge weight_values 0 ->
    candidate = cur_distance + edge_weight ->
    vertex_valid g neighbor ->
    storage_index neighbor ->
    0 <= candidate < DijkstraGraph.infinity ->
    0 <= edge_weight ->
    cur_distance <= DijkstraGraph.infinity - edge_weight ->
    candidate < dist_cell dist_values neighbor ->
    dijkstra_edge_loop_refines
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values queue_items X ->
    dijkstra_after_relax_refines
      g src cur_vertex cur_distance edge neighbor candidate
      head_values to_values weight_values next_values
      visited_set (replace_Znth neighbor candidate dist_values) queue_items X.
Proof.
  intros g vertex_count src cur_vertex cur_distance edge neighbor
    edge_weight candidate head_values to_values weight_values next_values
    visited_set dist_values queue_items X Hsize Hedge_not_nil Hneighbor Hweight
    Hcandidate Hvalid Hstorage Hcandidate_bounds Hweight_nonneg
    Hoverflow Hrelax Hrefines.
  subst neighbor edge_weight candidate.
  unfold dijkstra_edge_loop_refines in Hrefines.
  eapply safeExec_proequiv in Hrefines.
  2: {
    apply dijkstra_lfs_edge_loop_cont_unfold.
  }
  unfold dijkstra_lfs_edge_body in Hrefines.
  lfs_prog_nf Hrefines.
  apply safeExec_choice_r in Hrefines.
  lfs_prog_nf Hrefines.
  eapply safeExec_testst_bind in Hrefines.
  2: {
    intros s _.
    exact Hedge_not_nil.
  }
  lfs_prog_nf Hrefines.
  apply safeExec_choice_l in Hrefines.
  lfs_prog_nf Hrefines.
  eapply safeExec_testst_bind in Hrefines.
  2: {
    intros s Hmodel.
    do 2 (split; [eassumption |]).
    erewrite graph_state_model_dist_cell by eauto.
    exact Hrelax.
  }
  lfs_prog_nf Hrefines.
  apply safeExec_update'_bind in Hrefines.
  lfs_prog_nf Hrefines.
  unfold dijkstra_lfs_edge_loop_after_body_cont in Hrefines.
  change (safeExec
    (fun s : state =>
       exists s0 : state,
         s = set_state_distance (Znth edge to_values 0)
               (cur_distance + Znth edge weight_values 0) s0 /\
         graph_state_model g visited_set dist_values s0)
    (queue_items_after <-
       priority_queue_push_choice queue_items (Znth edge to_values 0)
         (cur_distance + Znth edge weight_values 0);;
     dijkstra_lfs_edge_loop_cont head_values to_values weight_values
       next_values cur_vertex cur_distance (Znth edge next_values 0)
       queue_items_after)
    X) in Hrefines.
  unfold dijkstra_after_relax_refines.
  eapply safeExec_conseq.
  - exact Hrefines.
  - intros s (s0 & Hs & Hmodel).
    subst s.
    eapply graph_state_model_replace_Znth_set_state_distance; eauto.
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

Lemma dijkstra_edge_loop_refines_after_body :
  forall g src cur_vertex cur_distance edge
         head_values to_values weight_values next_values
         visited_set dist_values queue_items X result Q,
    graph_state_model g visited_set dist_values -@
      dijkstra_lfs_edge_body
        head_values to_values weight_values next_values
        cur_vertex cur_distance (edge, queue_items)
      -⥅ Q ♯ result ->
    dijkstra_edge_loop_refines
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values queue_items X ->
    safeExec Q
      (dijkstra_lfs_edge_loop_after_body_cont
        head_values to_values weight_values next_values
        cur_vertex cur_distance result)
      X.
Proof.
  intros g src cur_vertex cur_distance edge
    head_values to_values weight_values next_values
    visited_set dist_values queue_items X result Q Hbody Hrefines.
  unfold dijkstra_edge_loop_refines in Hrefines.
  eapply highstepbind_derive; eauto.
  eapply safeExec_proequiv.
  - apply dijkstra_lfs_edge_loop_cont_unfold.
  - exact Hrefines.
Qed.

Lemma dijkstra_edge_loop_refines_no_relax_to_next :
  forall g src cur_vertex cur_distance edge neighbor edge_weight
         head_values to_values weight_values next_values visited_set dist_values
         queue_items X,
    edge <> -1 ->
    neighbor = Znth edge to_values 0 ->
    edge_weight = Znth edge weight_values 0 ->
    vertex_valid g neighbor ->
    (edge_weight < 0 \/
      cur_distance > DijkstraGraph.infinity - edge_weight \/
      cur_distance + edge_weight >= dist_cell dist_values neighbor) ->
    dijkstra_edge_loop_refines
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values queue_items X ->
    dijkstra_edge_loop_refines
      g src cur_vertex cur_distance (Znth edge next_values 0)
      head_values to_values weight_values next_values
      visited_set dist_values queue_items X.
Proof.
  intros g src cur_vertex cur_distance edge neighbor edge_weight
    head_values to_values weight_values next_values visited_set dist_values
    queue_items X Hedge_not_nil Hneighbor Hweight Hvalid Hskip Hrefines.
  subst neighbor edge_weight.
  assert (Hbody_step :
    graph_state_model g visited_set dist_values -@
      dijkstra_lfs_edge_body
        head_values to_values weight_values next_values
        cur_vertex cur_distance (edge, queue_items)
      -⥅ graph_state_model g visited_set dist_values
      ♯ by_continue (Znth edge next_values 0, queue_items)).
  {
    unfold dijkstra_lfs_edge_body.
    apply hsevalchoice_right_derive.
    eapply hsevalbind_derive'.
    + apply hs_eval_assume_state.
      intros s _.
      exact Hedge_not_nil.
    + apply hsevalchoice_right_derive.
      eapply hsevalbind_derive'.
      * apply hs_eval_assume_state.
        intros s Hmodel.
        destruct Hskip as [Hskip | [Hskip | Hskip]].
        -- left. exact Hskip.
        -- right. left. exact Hskip.
        -- right. right.
           erewrite graph_state_model_dist_cell by eauto.
           exact Hskip.
      * apply highret_eval2.
  }
  unfold dijkstra_edge_loop_refines, dijkstra_lfs_edge_loop_cont,
    dijkstra_lfs_edge_loop.
  change (safeExec (graph_state_model g visited_set dist_values)
    (dijkstra_lfs_edge_loop_after_body_cont head_values to_values
      weight_values next_values cur_vertex cur_distance
      (by_continue (Znth edge next_values 0, queue_items))) X).
  eapply dijkstra_edge_loop_refines_after_body; eauto.
Qed.

Lemma dijkstra_edge_loop_refines_break_to_loop :
  forall g src cur_vertex cur_distance edge
         head_values to_values weight_values next_values visited_set dist_values
         queue_items X,
    edge = -1 ->
    dijkstra_edge_loop_refines
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values queue_items X ->
    dijkstra_loop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values queue_items X.
Proof.
  intros g src cur_vertex cur_distance edge
    head_values to_values weight_values next_values visited_set dist_values
    queue_items X Hedge_nil Hrefines.
  assert (Hbody_step :
    graph_state_model g visited_set dist_values -@
      dijkstra_lfs_edge_body
        head_values to_values weight_values next_values
        cur_vertex cur_distance (edge, queue_items)
      -⥅ graph_state_model g visited_set dist_values
      ♯ by_break queue_items).
  {
    unfold dijkstra_lfs_edge_body.
    apply hsevalchoice_left_derive.
    eapply hsevalbind_derive'.
    + apply hs_eval_assume_state.
      intros s _.
      exact Hedge_nil.
    + apply highret_eval2.
  }
  unfold dijkstra_loop_refines.
  eapply safeExec_proequiv.
  2: { eapply dijkstra_edge_loop_refines_after_body; eauto. }
  unfold dijkstra_lfs_edge_loop_after_body_cont.
  rewrite ret_equiv.
  reflexivity.
Qed.

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
    dijkstra_nonnegative_edges g ->
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
    dijkstra_nonnegative_edges g ->
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
    dijkstra_nonnegative_edges g ->
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
    dijkstra_nonnegative_edges g ->
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

Definition dijkstra_loop_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z)
    (queue_items : list (Z * Z)) : Prop :=
  DijkstraGraph.graph_wf g /\
  vertex_valid g src /\
	  dijkstra_nonnegative_edges g /\
	  vector_shape dist_values /\
	  dist_values_safe dist_values /\
	  priority_queue_ordered queue_items /\
	  priority_queue_vertices_valid g queue_items.

Definition dijkstra_edge_loop_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (cur_vertex cur_distance edge : Z)
    (dist_values : list Z) (queue_items : list (Z * Z)) : Prop :=
  dijkstra_loop_state g src visited_set dist_values queue_items /\
  vertex_valid g cur_vertex /\
  dist_cell dist_values cur_vertex = cur_distance /\
  (-1 <= edge).

Definition dijkstra_loop_bridge_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (queue_items : list (Z * Z)) : Prop :=
  dijkstra_loop_state g src visited_set dist_values queue_items /\
  priority_queue_refines_unvisited_dist g visited_set dist_values queue_items.

Definition dijkstra_after_pop_bridge_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (queue_items_after : list (Z * Z))
    (cur_vertex cur_distance : Z) : Prop :=
  dijkstra_loop_state g src visited_set dist_values queue_items_after /\
  priority_queue_pop_result
    ((cur_distance, cur_vertex) :: queue_items_after)
    queue_items_after cur_vertex cur_distance /\
  priority_queue_refines_unvisited_dist g visited_set dist_values
    ((cur_distance, cur_vertex) :: queue_items_after).

Definition dijkstra_edge_loop_bridge_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (cur_vertex cur_distance edge : Z)
    (dist_values : list Z) (queue_items : list (Z * Z)) : Prop :=
  dijkstra_edge_loop_state g src visited_set cur_vertex cur_distance edge
    dist_values queue_items /\
  priority_queue_refines_unvisited_dist g visited_set dist_values queue_items.

Lemma dijkstra_init_dist_loop_state :
  forall g vertex_count src visited_set dist_values queue_vertices queue_distances
         queue_size queue_items edge_count head_values to_values
         weight_values next_values,
    graph_has_size g vertex_count ->
    vertex_valid g src ->
    dijkstra_nonnegative_edges g ->
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    dijkstra_init_dist vertex_count src dist_values ->
    priority_queue_model queue_vertices queue_distances queue_size queue_items ->
    priority_queue_vertices_valid g queue_items ->
    dijkstra_loop_state g src visited_set dist_values queue_items.
Proof.
  intros g vertex_count src visited_set dist_values queue_vertices queue_distances
    queue_size queue_items edge_count head_values to_values
    weight_values next_values Hsize Hsrc Hnonneg Hgraph Hinit Hqueue
    Hqueue_valid.
  unfold dijkstra_loop_state.
  destruct Hgraph as (? & _).
  destruct Hinit as (? & ? & _).
  do 5 (split; [eassumption |]).
  split; eauto using priority_queue_model_ordered.
Qed.

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

Ltac priority_queue_insert_item_cases candidate neighbor items d v Hin :=
  destruct (priority_queue_insert_in_inv
    (candidate, neighbor) items (d, v) Hin) as [Hnew | Hold];
  [inversion Hnew; subst d v |].

Lemma priority_queue_refines_unvisited_dist_relax_push :
  forall g vertex_count visited_set dist_values items items_out
         neighbor candidate,
    graph_has_size g vertex_count ->
    vector_shape dist_values ->
	    storage_index neighbor ->
	    ~ visited_set neighbor ->
	    candidate < dist_cell dist_values neighbor ->
	    candidate < DijkstraGraph.infinity ->
	    priority_queue_vertices_valid g items ->
	    priority_queue_refines_unvisited_dist g visited_set dist_values items ->
	    priority_queue_push_result items items_out neighbor candidate ->
    priority_queue_refines_unvisited_dist g visited_set
      (replace_Znth neighbor candidate dist_values) items_out.
Proof.
	  intros g vertex_count visited_set dist_values items items_out
	    neighbor candidate Hsize Hshape Hneighbor_storage Hneighbor_unvisited
	    Hstrict Hcandidate_finite Hvertices_valid Hrefines Hpush.
	  destruct Hrefines as
	    (Hcovers & Hfresh & Hlower & Hitems_finite & Hnodup).
  unfold priority_queue_push_result in Hpush.
  subst items_out.
  unfold priority_queue_refines_unvisited_dist.
  split.
  - intros v Hvalid Hunvisited Hfinite.
    destruct (Z.eq_dec v neighbor) as [Heq | Hneq].
    + subst v.
      erewrite dist_cell_replace_Znth_same by eauto.
      apply priority_queue_insert_in_new.
		    + pose proof
		        (graph_has_size_vertex_valid_storage _ _ _ Hsize Hvalid)
		        as Hv_storage.
      erewrite dist_cell_replace_Znth_diff in Hfinite |- * by eauto.
      apply priority_queue_insert_in_old.
      apply Hcovers; auto.
  - split.
    + intros d v Hin Hdist_new.
      priority_queue_insert_item_cases candidate neighbor items d v Hin.
      * exact Hneighbor_unvisited.
      * destruct (Z.eq_dec v neighbor) as [Heq | Hneq].
        -- subst v.
           erewrite dist_cell_replace_Znth_same in Hdist_new by eauto.
           subst d.
           pose proof (Hlower candidate neighbor Hold) as Hlower_old.
           lia.
        -- pose proof
             (graph_has_size_vertex_valid_storage _ _ _ Hsize
               (Hvertices_valid (d, v) Hold)) as Hv_storage.
           erewrite dist_cell_replace_Znth_diff in Hdist_new by eauto.
           apply (Hfresh d v); auto.
	    + split.
      * intros d v Hin.
	      priority_queue_insert_item_cases candidate neighbor items d v Hin.
	      -- erewrite dist_cell_replace_Znth_same by eauto.
	         lia.
	      -- destruct (Z.eq_dec v neighbor) as [Heq | Hneq].
	         ++ subst v.
	            erewrite dist_cell_replace_Znth_same by eauto.
	            pose proof (Hlower d neighbor Hold) as Hlower_old.
	            lia.
	         ++ pose proof
                (graph_has_size_vertex_valid_storage _ _ _ Hsize
                  (Hvertices_valid (d, v) Hold)) as Hv_storage.
	            erewrite dist_cell_replace_Znth_diff by eauto.
	            apply Hlower. exact Hold.
	      * split.
	        -- intros d v Hin.
	           priority_queue_insert_item_cases candidate neighbor items d v Hin.
	           ++ exact Hcandidate_finite.
	           ++ apply (Hitems_finite d v). exact Hold.
	        -- apply priority_queue_insert_nodup; [exact Hnodup |].
	           intro Hin.
	           pose proof (Hlower candidate neighbor Hin) as Hlower_item.
	           lia.
Qed.

Lemma priority_queue_pop_result_vertex_valid :
  forall g src visited_set dist_values items items_out vertex distance,
    dijkstra_loop_state g src visited_set dist_values items ->
    priority_queue_pop_result items items_out vertex distance ->
    vertex_valid g vertex.
Proof.
  intros g src visited_set dist_values items items_out vertex distance
    Hloop Hpop.
  dijkstra_pop_cons.
  unfold dijkstra_loop_state, priority_queue_vertices_valid in Hloop.
  destruct Hloop as (_ & _ & _ & _ & _ & _ & Hqueue_valid).
  specialize (Hqueue_valid (distance, vertex) ltac:(simpl; auto)).
  simpl in Hqueue_valid.
  exact Hqueue_valid.
Qed.

Lemma dijkstra_loop_state_pop :
  forall g src visited_set dist_values items items_out vertex distance
         queue_vertices queue_distances,
    dijkstra_loop_state g src visited_set dist_values items ->
    priority_queue_pop_result items items_out vertex distance ->
    priority_queue_model queue_vertices queue_distances
      (Zlength items_out) items_out ->
    dijkstra_loop_state g src visited_set dist_values items_out.
Proof.
  intros g src visited_set dist_values items items_out vertex distance
    queue_vertices queue_distances Hloop Hpop Hqueue.
  unfold dijkstra_loop_state in *.
  destruct Hloop as (Hwf & Hsrc & Hnonneg & Hshape & Hsafe & _ & Hvalid).
  do 5 (split; [assumption |]).
  split; [eauto using priority_queue_model_ordered |].
  unfold priority_queue_vertices_valid in *.
  intros item Hin.
  apply Hvalid.
  pose proof (priority_queue_pop_result_cons
    items items_out vertex distance Hpop) as Hitems.
  subst items; simpl; auto.
Qed.

Lemma dijkstra_loop_state_push :
  forall g src visited_set dist_values items items_out vertex distance
         queue_vertices queue_distances,
    dijkstra_loop_state g src visited_set dist_values items ->
    vertex_valid g vertex ->
    priority_queue_push_result items items_out vertex distance ->
    priority_queue_model queue_vertices queue_distances
      (Zlength items_out) items_out ->
    dijkstra_loop_state g src visited_set dist_values items_out.
Proof.
  intros g src visited_set dist_values items items_out vertex distance
    queue_vertices queue_distances Hloop Hvertex Hpush Hqueue.
  unfold dijkstra_loop_state in *.
  destruct Hloop as (Hwf & Hsrc & Hnonneg & Hshape & Hsafe & _ & Hvalid).
  do 5 (split; [assumption |]).
  split; eauto using priority_queue_model_ordered,
    priority_queue_push_result_vertices_valid.
Qed.

Lemma dijkstra_loop_bridge_state_pop_result :
  forall g src visited_set dist_values items items_out vertex distance,
    dijkstra_loop_bridge_state g src visited_set dist_values items ->
    priority_queue_pop_result items items_out vertex distance ->
    dijkstra_after_pop_bridge_state
      g src visited_set dist_values items_out vertex distance.
Proof.
  intros g src visited_set dist_values items items_out vertex distance
    Hbridge Hpop.
  pose proof
    (priority_queue_pop_result_cons
      items items_out vertex distance Hpop) as Hitems.
  subst items.
  unfold dijkstra_loop_bridge_state, dijkstra_after_pop_bridge_state in *.
  destruct Hbridge as (Hloop & Hrefines).
  split.
  - unfold dijkstra_loop_state in *.
    destruct Hloop as
      (Hwf & Hsrc & Hnonneg & Hshape & Hsafe & Hordered & Hvalid).
    do 5 (split; [assumption |]).
    split.
    + simpl in Hordered; tauto.
    + unfold priority_queue_vertices_valid in *.
      intros item Hin; apply Hvalid; simpl; auto.
  - split; assumption.
Qed.

Lemma dijkstra_after_pop_bridge_state_stale_to_loop_bridge :
  forall g src visited_set dist_values queue_items_after
         cur_vertex cur_distance,
    dijkstra_after_pop_bridge_state
      g src visited_set dist_values queue_items_after cur_vertex cur_distance ->
    cur_distance <> dist_cell dist_values cur_vertex ->
    dijkstra_loop_bridge_state
      g src visited_set dist_values queue_items_after.
Proof.
  intros g src visited_set dist_values queue_items_after
    cur_vertex cur_distance Hbridge Hstale.
  unfold dijkstra_after_pop_bridge_state in Hbridge.
  destruct Hbridge as (Hloop & Hpop & Hrefines).
  unfold dijkstra_loop_bridge_state.
  split; [exact Hloop |].
  destruct Hrefines as (Hcovers & Hfresh & Hlower & Hfinite & Hnodup).
  unfold priority_queue_refines_unvisited_dist.
  split.
  - intros v Hvalid Hunvisited Hfinite_v.
    pose proof (Hcovers v Hvalid Hunvisited Hfinite_v) as Hin.
    simpl in Hin.
    destruct Hin as [Hhead | Htail].
    + inversion Hhead; subst. contradiction.
    + exact Htail.
  - split.
    + intros d v Hin Hdist.
      eapply Hfresh; eauto; simpl; auto.
    + split.
      * intros d v Hin; apply (Hlower d v); simpl; auto.
      * split.
        -- intros d v Hin; apply (Hfinite d v); simpl; auto.
        -- inversion Hnodup; auto.
Qed.

Lemma dijkstra_after_pop_bridge_state_equal_to_edge_bridge :
  forall g src visited_set visited_set' dist_values queue_items_after
         cur_vertex cur_distance edge,
    vertex_valid g cur_vertex ->
    visited_set_add visited_set cur_vertex visited_set' ->
    dist_cell dist_values cur_vertex = cur_distance ->
    -1 <= edge ->
    dijkstra_after_pop_bridge_state
      g src visited_set dist_values queue_items_after cur_vertex cur_distance ->
    dijkstra_edge_loop_bridge_state
      g src visited_set' cur_vertex cur_distance edge
      dist_values queue_items_after.
Proof.
  intros g src visited_set visited_set' dist_values queue_items_after
    cur_vertex cur_distance edge Hvalid Hvisit_add Hdist Hedge_nonneg
    Hbridge.
  unfold dijkstra_after_pop_bridge_state in Hbridge.
  destruct Hbridge as (Hloop & Hpop & Hrefines).
  unfold dijkstra_edge_loop_bridge_state.
  split.
  - unfold dijkstra_edge_loop_state.
    do 3 (split; [eassumption |]); eassumption.
  - destruct Hrefines as (Hcovers & Hfresh & Hlower & Hfinite & Hnodup).
    assert (Hhead_notin_tail :
      ~ In (cur_distance, cur_vertex) queue_items_after).
    {
      inversion Hnodup as [| head tail Hnotin_tail Htail_nodup]; subst.
      exact Hnotin_tail.
    }
    unfold priority_queue_refines_unvisited_dist.
    split.
    + intros v Hvalid_v Hunvisited' Hfinite_v.
      assert (~ visited_set v) as Hunvisited.
      {
        intro Hvisited.
        apply Hunvisited'.
        unfold visited_set_add in Hvisit_add.
        apply Hvisit_add; left; exact Hvisited.
      }
      pose proof (Hcovers v Hvalid_v Hunvisited Hfinite_v) as Hin.
      simpl in Hin.
      destruct Hin as [Hhead | Htail].
      * inversion Hhead; subst v.
        exfalso.
        apply Hunvisited'.
        unfold visited_set_add in Hvisit_add.
        apply Hvisit_add; right; reflexivity.
      * exact Htail.
    + split.
      * intros d v Hin_tail Hd.
        assert (~ visited_set v) as Hnot_old.
        {
          apply (Hfresh d v).
          - simpl. right. exact Hin_tail.
          - exact Hd.
        }
        intro Hvisited_new.
        unfold visited_set_add in Hvisit_add.
        apply Hvisit_add in Hvisited_new.
        destruct Hvisited_new as [Hvisited_old | Heq].
        -- apply Hnot_old. exact Hvisited_old.
        -- subst v.
           apply Hhead_notin_tail.
           rewrite Hdist in Hd.
           subst d.
           exact Hin_tail.
      * split.
        -- intros d v Hin; apply (Hlower d v); simpl; auto.
        -- split.
           ++ intros d v Hin; apply (Hfinite d v); simpl; auto.
           ++ inversion Hnodup; auto.
Qed.

Lemma dijkstra_edge_loop_to_loop_state :
  forall g src visited_set cur_vertex cur_distance edge dist_values queue_items,
    dijkstra_edge_loop_state g src visited_set cur_vertex cur_distance edge
      dist_values queue_items ->
    dijkstra_loop_state g src visited_set dist_values queue_items.
Proof. unfold dijkstra_edge_loop_state; tauto. Qed.

Lemma dijkstra_edge_loop_next :
  forall g src visited_set cur_vertex cur_distance edge next_edge dist_values queue_items,
    dijkstra_edge_loop_state g src visited_set cur_vertex cur_distance edge
      dist_values queue_items ->
    -1 <= next_edge ->
    dijkstra_edge_loop_state g src visited_set cur_vertex cur_distance next_edge
      dist_values queue_items.
Proof.
  unfold dijkstra_edge_loop_state in *; dijkstra_cleanup; repeat split; eauto.
Qed.

Lemma dijkstra_edge_loop_state_relax_update :
  forall g vertex_count src visited_set cur_vertex cur_distance edge
         neighbor edge_weight candidate dist_values queue_items,
    graph_has_size g vertex_count ->
    vertex_valid g neighbor ->
    storage_index neighbor ->
    0 <= candidate < DijkstraGraph.infinity ->
    0 <= edge_weight ->
    candidate = cur_distance + edge_weight ->
    candidate < dist_cell dist_values neighbor ->
    dijkstra_edge_loop_state g src visited_set cur_vertex cur_distance edge
      dist_values queue_items ->
    dijkstra_edge_loop_state g src visited_set cur_vertex cur_distance edge
      (replace_Znth neighbor candidate dist_values) queue_items.
Proof.
  intros g vertex_count src visited_set cur_vertex cur_distance edge
    neighbor edge_weight candidate dist_values queue_items
    Hsize Hneighbor_valid Hneighbor_storage Hcandidate_bounds
    Hweight_nonneg Hcandidate Hrelax Hedge.
  unfold dijkstra_edge_loop_state in *.
  destruct Hedge as (Hloop & Hcur_valid & Hcur_dist & Hedge_nonneg).
  assert (Hshape_loop : vector_shape dist_values)
    by (unfold dijkstra_loop_state in Hloop; tauto).
  assert (Hneighbor_ne_cur : neighbor <> cur_vertex)
    by (intro Hsame; subst neighbor;
        rewrite Hcur_dist in Hrelax; subst candidate; lia).
  split.
  - unfold dijkstra_loop_state in *.
    destruct Hloop as
      (Hwf & Hsrc & Hnonneg & Hshape & Hsafe & Hordered & Hqueue_valid).
    do 3 (split; [assumption |]).
    split.
    + unfold vector_shape in *.
      rewrite Zlength_replace_Znth.
      exact Hshape.
    + split.
      * eapply dist_values_safe_replace_Znth; eauto.
      * split; assumption.
  - split; [exact Hcur_valid |].
    split.
    + rewrite dist_cell_replace_Znth_diff
        by (eauto using graph_has_size_vertex_valid_storage; lia).
      exact Hcur_dist.
	    + exact Hedge_nonneg.
Qed.

Lemma dijkstra_edge_loop_bridge_next :
  forall g src visited_set cur_vertex cur_distance edge next_edge
         dist_values queue_items,
    dijkstra_edge_loop_bridge_state
      g src visited_set cur_vertex cur_distance edge
      dist_values queue_items ->
    -1 <= next_edge ->
    dijkstra_edge_loop_bridge_state
      g src visited_set cur_vertex cur_distance next_edge
      dist_values queue_items.
Proof.
	  intros g src visited_set cur_vertex cur_distance edge next_edge
	    dist_values queue_items Hbridge Hnext.
	  unfold dijkstra_edge_loop_bridge_state in *.
	  dijkstra_cleanup; eauto using dijkstra_edge_loop_next.
Qed.

Lemma dijkstra_edge_loop_bridge_to_loop_bridge :
  forall g src visited_set cur_vertex cur_distance edge
         dist_values queue_items,
    dijkstra_edge_loop_bridge_state
      g src visited_set cur_vertex cur_distance edge
      dist_values queue_items ->
    dijkstra_loop_bridge_state
      g src visited_set dist_values queue_items.
Proof.
  intros g src visited_set cur_vertex cur_distance edge
    dist_values queue_items Hbridge.
  unfold dijkstra_edge_loop_bridge_state, dijkstra_loop_bridge_state in *.
  dijkstra_cleanup; eauto using dijkstra_edge_loop_to_loop_state.
Qed.

Lemma dijkstra_edge_loop_bridge_relax_update_push_result :
  forall g vertex_count src visited_set cur_vertex cur_distance edge
         next_edge neighbor edge_weight candidate dist_values
         queue_items queue_items_after,
    graph_has_size g vertex_count ->
    vertex_valid g neighbor ->
    storage_index neighbor ->
    ~ visited_set neighbor ->
    0 <= candidate < DijkstraGraph.infinity ->
    0 <= edge_weight ->
    candidate = cur_distance + edge_weight ->
    candidate < dist_cell dist_values neighbor ->
    -1 <= next_edge ->
    priority_queue_push_result queue_items queue_items_after
      neighbor candidate ->
    dijkstra_edge_loop_bridge_state
      g src visited_set cur_vertex cur_distance edge
      dist_values queue_items ->
    dijkstra_edge_loop_bridge_state
      g src visited_set cur_vertex cur_distance next_edge
      (replace_Znth neighbor candidate dist_values) queue_items_after.
Proof.
  intros g vertex_count src visited_set cur_vertex cur_distance edge
    next_edge neighbor edge_weight candidate dist_values
    queue_items queue_items_after Hsize Hneighbor_valid Hneighbor_storage
    Hneighbor_unvisited Hcandidate_bounds Hweight_nonneg Hcandidate_eq
    Hrelax Hnext Hpush Hbridge.
  unfold dijkstra_edge_loop_bridge_state in Hbridge.
  destruct Hbridge as (Hedge & Hrefines).
  assert (Hshape_old : vector_shape dist_values)
    by (unfold dijkstra_edge_loop_state, dijkstra_loop_state in Hedge; tauto).
  assert (Hvertices_valid : priority_queue_vertices_valid g queue_items)
    by (unfold dijkstra_edge_loop_state, dijkstra_loop_state in Hedge; tauto).
  assert (Hupdated_edge :
    dijkstra_edge_loop_state g src visited_set cur_vertex cur_distance edge
      (replace_Znth neighbor candidate dist_values) queue_items).
  {
    eapply dijkstra_edge_loop_state_relax_update; eauto.
  }
  destruct Hupdated_edge as
    (Hloop_updated & Hcur_valid & Hcur_dist & _).
  unfold dijkstra_edge_loop_bridge_state.
  split.
  - unfold dijkstra_edge_loop_state.
    split.
    + unfold dijkstra_loop_state in *.
      destruct Hloop_updated as
        (Hwf & Hsrc & Hnonneg & Hshape & Hsafe & Hordered & Hvalid).
      do 5 (split; [assumption |]).
      split.
      * unfold priority_queue_push_result in Hpush; subst;
          auto using priority_queue_insert_ordered.
      * eauto using priority_queue_push_result_vertices_valid.
    + do 2 (split; [eassumption |]).
      exact Hnext.
  - eapply priority_queue_refines_unvisited_dist_relax_push.
    + exact Hsize.
    + exact Hshape_old.
    + exact Hneighbor_storage.
    + exact Hneighbor_unvisited.
    + exact Hrelax.
    + lia.
    + exact Hvertices_valid.
    + exact Hrefines.
    + exact Hpush.
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

Definition dijkstra_edge_loop_math_bridge_state
    (g : DijkstraGraph.G) (src : Z)
    (visited_before visited_after : Z -> Prop)
    (cur_vertex cur_distance edge : Z)
    (base_dist_values dist_values : list Z) (queue_items : list (Z * Z))
    (head_values to_values weight_values next_values : list Z) : Prop :=
  dijkstra_edge_loop_bridge_state
    g src visited_after cur_vertex cur_distance edge dist_values queue_items /\
  visited_set_valid g visited_before /\
  visited_set_add visited_before cur_vertex visited_after /\
  cur_distance = dist_cell base_dist_values cur_vertex /\
  (edge = -1 \/ next_chain next_values (Znth cur_vertex head_values (-1)) edge) /\
  dijkstra_edge_math_state g src visited_before visited_after
    cur_vertex base_dist_values
    (forward_star_done_edge_set
      head_values to_values weight_values next_values cur_vertex edge)
    dist_values.

Ltac pose_dijkstra_edge_loop_current_facts
    edge_count cur_vertex edge head_values next_values
    Hsize Hmodel Hedge_not_nil Hbridge :=
  let Hbridge0 := fresh "Hbridge" in
  let Hedge_bridge0 := fresh "Hedge_bridge" in
  let Hedge_state0 := fresh "Hedge_state" in
  let Hedge_chain0 := fresh "Hedge_chain" in
  pose proof Hbridge as Hbridge0;
  unfold dijkstra_edge_loop_math_bridge_state in Hbridge0;
  destruct Hbridge0 as
    (Hedge_bridge0 & _ & _ & _ & Hedge_chain0 & _);
  unfold dijkstra_edge_loop_bridge_state in Hedge_bridge0;
  destruct Hedge_bridge0 as (Hedge_state0 & _);
  unfold dijkstra_edge_loop_state in Hedge_state0;
  destruct Hedge_state0 as (_ & Hcur_valid & _);
  assert (Hhead_edge :
    next_chain next_values (Znth cur_vertex head_values (-1)) edge)
    by (destruct Hedge_chain0 as [Hedge_nil | Hchain];
        [contradiction | exact Hchain]);
  assert (Hedge_index : edge_index edge_count edge)
    by (eapply forward_star_next_chain_edge_index; eauto);
  pose proof
    (forward_star_current_edge_facts
      _ _ _ _ _ _ _ _ _ Hsize Hmodel Hcur_valid
      Hhead_edge Hedge_index)
    as (_ & Hcur_storage & Hedge_to & Hedge_next & Hneighbor_valid
        & Hneighbor_storage & Hstep & Hweight & Hnext_eq).

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

Definition dijkstra_edge_loop_math_model
    (g : DijkstraGraph.G) (src : Z)
    (visited_before visited_after : Z -> Prop)
    (cur_vertex cur_distance edge : Z)
    (base_dist_values : list Z) (queue_items : list (Z * Z))
    (head_values to_values weight_values next_values : list Z)
    (s : state) : Prop :=
  exists dist_values,
    graph_state_model g visited_after dist_values s /\
    0 <= cur_distance < DijkstraGraph.infinity /\
    dijkstra_edge_loop_math_bridge_state
      g src visited_before visited_after cur_vertex cur_distance edge
      base_dist_values dist_values queue_items
      head_values to_values weight_values next_values.

Definition source_visited_set (src : Z) : Z -> Prop :=
  fun v => v = src.

Definition dijkstra_first_step_math_state
    (g : DijkstraGraph.G) (src : Z)
    (done : DijkstraGraph.E -> Prop)
    (dist_values : list Z) : Prop :=
  dijkstra_first_step_invariant g src done
    (dijkstra_array_state g (source_visited_set src) dist_values).

Definition dijkstra_first_edge_loop_math_bridge_state
    (g : DijkstraGraph.G) (src edge : Z)
    (dist_values : list Z) (queue_items : list (Z * Z))
    (head_values to_values weight_values next_values : list Z) : Prop :=
  dijkstra_edge_loop_bridge_state
    g src (source_visited_set src) src 0 edge dist_values queue_items /\
  (edge = -1 \/ next_chain next_values (Znth src head_values (-1)) edge) /\
  dijkstra_first_step_math_state
    g src
    (forward_star_done_edge_set
      head_values to_values weight_values next_values src edge)
    dist_values.

Definition dijkstra_first_edge_loop_math_model
    (g : DijkstraGraph.G) (src edge : Z)
    (queue_items : list (Z * Z))
    (head_values to_values weight_values next_values : list Z)
    (s : state) : Prop :=
  exists dist_values,
    graph_state_model g (source_visited_set src) dist_values s /\
    dijkstra_first_edge_loop_math_bridge_state
      g src edge dist_values queue_items
      head_values to_values weight_values next_values.

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

Section FirstStepProofs.

Context (g : DijkstraGraph.G)
        (vertex_count edge_count src : Z)
        (head_values to_values weight_values next_values : list Z).

Hypothesis Hsize : graph_has_size g vertex_count.
Hypothesis Hsrc : vertex_valid g src.
Hypothesis Hnonneg : dijkstra_nonnegative_edges g.
Hypothesis Hmodel :
  forward_star_model g edge_count
    head_values to_values weight_values next_values.
Hypothesis Hno_overflow : dijkstra_no_overflow g src.

Lemma initial_first_edge_loop_math_model :
    dijkstra_first_edge_loop_math_model
      g src (Znth src head_values 0) nil
      head_values to_values weight_values next_values
      (set_state_visited src (initial_state src)).
Proof.
  pose proof
    (graph_has_size_vertex_valid_bounds
      g vertex_count src Hsize Hsrc) as (Hcount & Hsrc_bounds).
		  pose proof
		    (graph_has_size_vertex_valid_storage _ _ _ Hsize Hsrc)
		    as Hstorage_src.
  pose proof
    (initial_dist_values_init vertex_count src Hcount Hsrc_bounds)
    as (_ & _ & _ & _ & Hinit_cells).
  unfold dijkstra_first_edge_loop_math_model.
  exists (initial_dist_values src).
  split.
  - eapply graph_state_model_visit_state
      with (visited_set := fun _ : Z => False).
    + exact Hsrc.
    + unfold visited_set_add, source_visited_set; tauto.
    + eapply dijkstra_init_dist_graph_state_model_initial.
      * exact Hsize.
      * unfold visited_set_empty; tauto.
      * apply initial_dist_values_init; auto.
  - unfold dijkstra_first_edge_loop_math_bridge_state.
    split.
    + unfold dijkstra_edge_loop_bridge_state.
      split.
      * unfold dijkstra_edge_loop_state.
        split.
        -- unfold dijkstra_loop_state.
           split; [eapply forward_star_model_graph_wf; exact Hmodel |].
           split; [exact Hsrc |].
           split; [exact Hnonneg |].
           split.
           ++ apply initial_dist_values_shape.
              exact Hstorage_src.
	           ++ split.
		              ** apply initial_dist_values_safe.
		                 exact Hstorage_src.
		              ** split.
	                 --- simpl. exact I.
	                 --- unfold priority_queue_vertices_valid.
	                     intros item Hin.
	                     contradiction.
        -- split; [exact Hsrc |].
           split.
           ++ rewrite (Hinit_cells src Hsrc_bounds).
              destruct (Z.eq_dec src src) as [_ | Hcontra].
              ** reflexivity.
              ** contradiction Hcontra. reflexivity.
	           ++ eapply forward_star_head_0_lower_bound; eauto.
		      * unfold priority_queue_refines_unvisited_dist.
		        split.
            -- intros v Hvalid Hunvisited Hfinite.
               pose proof
                 (graph_has_size_vertex_valid_storage _ _ _ Hsize Hvalid)
                 as Hv_storage.
               rewrite initial_dist_values_cell in Hfinite by auto.
               unfold source_visited_set in Hunvisited.
               destruct (Z.eq_dec v src) as [Heq | _];
                 [subst v; contradiction Hunvisited; reflexivity | lia].
            -- repeat split; simpl; try contradiction; constructor.
    + split.
      * eapply forward_star_head_0_nil_or_chain; eauto.
      * eapply (dijkstra_first_step_math_state_done_equiv
          g src
          (fun _ : DijkstraGraph.E => False)
          (forward_star_done_edge_set
            head_values to_values weight_values next_values src
            (Znth src head_values 0))
          (initial_dist_values src)).
        -- intros e_abs.
           symmetry.
           eapply forward_star_done_edge_set_head_empty_equiv; eauto.
        -- eapply initial_first_step_math_state_empty; eauto.
Qed.

End FirstStepProofs.

Section LoopMathProofs.

Context (g : DijkstraGraph.G)
        (vertex_count edge_count src : Z)
        (head_values to_values weight_values next_values : list Z).

Hypothesis Hsize : graph_has_size g vertex_count.
Hypothesis Hsrc : vertex_valid g src.
Hypothesis Hnonneg : dijkstra_nonnegative_edges g.
Hypothesis Hmodel :
  forward_star_model g edge_count
    head_values to_values weight_values next_values.
Hypothesis Hno_overflow : dijkstra_no_overflow g src.

Local Notation done_edges :=
  (forward_star_done_edge_set
    head_values to_values weight_values next_values).

Ltac pose_first_edge_current_facts edge dist_values queue_items
    Hedge_not_nil Hbridge :=
  let Hbridge_facts := fresh "Hbridge_facts" in
  let Hedge_bridge_facts := fresh "Hedge_bridge_facts" in
  pose proof Hbridge as Hbridge_facts;
  unfold dijkstra_first_edge_loop_math_bridge_state in Hbridge_facts;
  destruct Hbridge_facts as
    (Hedge_bridge_facts & [? | Hhead_edge] & _);
    [contradiction |];
  assert (Hsrc_valid : vertex_valid g src)
    by (unfold dijkstra_edge_loop_bridge_state,
          dijkstra_edge_loop_state in Hedge_bridge_facts; tauto);
  assert (Hedge_index : edge_index edge_count edge)
    by (eapply forward_star_next_chain_edge_index; eauto);
  pose proof
    (forward_star_current_edge_facts
      _ _ _ _ _ _ _ _ _ Hsize Hmodel Hsrc_valid
      Hhead_edge Hedge_index)
    as (Hchain_wf & Hsrc_storage & Hedge_to & Hedge_next
        & Hneighbor_valid & Hneighbor_storage
        & Hcurrent_step & Hcurrent_weight & Hnext_eq).

Ltac solve_first_edge_candidate_bounds
    edge Hsrc_valid Hneighbor_valid Hcurrent_weight :=
  simpl in Hcurrent_weight;
  apply (Hno_overflow src (Znth edge to_values 0) 0
    (Znth edge weight_values 0));
  [exact Hsrc_valid | exact Hneighbor_valid | dijkstra_min_epath_refl
  | exact Hcurrent_weight].

Ltac solve_forward_star_done_step :=
  intros e_abs; symmetry;
  apply forward_star_done_edge_set_step_0; auto;
  try (eapply forward_star_model_chain_wf; eauto).

Ltac first_edge_done_equiv edge dist_values :=
  eapply (dijkstra_first_step_math_state_done_equiv
    g src
    (fun e_abs =>
      done_edges src edge e_abs \/
      e_abs = (src, Znth edge to_values 0))
    (done_edges src (Znth edge next_values 0))
    dist_values);
  [ solve_forward_star_done_step
  | unfold dijkstra_first_step_math_state in * ].

Ltac solve_forward_star_done_subset :=
  intros e_abs Hdone;
  eapply forward_star_done_edge_set_step_aux; eauto.

Ltac solve_current_edge_add_side_condition :=
  solve [ solve_forward_star_done_subset
        | apply forward_star_current_edge_not_done; auto
        | reflexivity ].

Ltac finish_edge_math_done lemma :=
  cbn [fst snd];
  eapply dijkstra_edge_math_state_done_equiv;
  [ solve_forward_star_done_step
  | eapply lemma; eauto;
    [ eapply forward_star_model_graph_wf; eauto
    | solve_forward_star_done_subset
    | apply forward_star_current_edge_not_done; auto ] ].

Ltac solve_edge_loop_candidate_bounds
    visited_before cur_vertex cur_distance edge base_dist_values
    Hbridge Hcur_finite Hcur_valid Hneighbor_valid Hweight :=
  let Hbridge0 := fresh "Hbridge" in
  let Hcur_base0 := fresh "Hcur_base" in
  let Hmath_edge0 := fresh "Hmath_edge" in
  let Hmath_before0 := fresh "Hmath_before" in
  let Hselected0 := fresh "Hselected" in
  let Hoptimal0 := fresh "Hoptimal" in
  let Hshortest0 := fresh "Hshortest" in
  pose proof Hbridge as Hbridge0;
  unfold dijkstra_edge_loop_math_bridge_state in Hbridge0;
  destruct Hbridge0 as (_ & _ & _ & Hcur_base0 & _ & Hmath_edge0);
  unfold dijkstra_edge_math_state in Hmath_edge0;
  destruct Hmath_edge0 as (_ & Hmath_before0 & Hselected0 & _);
  unfold dijkstra_math_invariant in Hmath_before0;
  destruct Hmath_before0 as (_ & Hoptimal0 & _);
  pose proof (dijkstra_greedy_choice_correct
      g ltac:(eapply forward_star_model_graph_wf; eauto)
      src Hnonneg cur_vertex
      (@visited Z
        (dijkstra_array_state g visited_before base_dist_values))
      (@dist Z
        (dijkstra_array_state g visited_before base_dist_values))
      Hoptimal0
      Hselected0) as Hshortest0;
  replace (@dist Z
    (dijkstra_array_state g visited_before base_dist_values)
    cur_vertex) with (Some cur_distance) in Hshortest0;
  [| rewrite dijkstra_array_state_dist_valid by exact Hcur_valid;
     rewrite <- Hcur_base0; symmetry;
     apply cell_as_distance_finite; exact Hcur_finite ];
  simpl in Hweight;
  apply (Hno_overflow cur_vertex (Znth edge to_values 0)
    cur_distance (Znth edge weight_values 0));
  [exact Hcur_valid | exact Hneighbor_valid | exact Hshortest0
  | exact Hweight].

Ltac solve_edge_loop_relax_neighbor_unvisited
    visited_before visited_after cur_vertex cur_distance edge
    base_dist_values dist_values
    Hbridge Hcur_valid Hneighbor_valid Hstep Hweight Hcur_finite Hrelax :=
  let Hvisited_after0 := fresh "Hvisited_after" in
  intro Hvisited_after0;
  let Hbridge0 := fresh "Hbridge" in
  let Hedge_bridge0 := fresh "Hedge_bridge" in
  let Hedge_state0 := fresh "Hedge_state" in
  let Hvisit_add0 := fresh "Hvisit_add" in
  let Hcur_base0 := fresh "Hcur_base" in
  let Hmath0 := fresh "Hmath" in
  let Hcur_dist0 := fresh "Hcur_dist" in
  pose proof Hbridge as Hbridge0;
  unfold dijkstra_edge_loop_math_bridge_state in Hbridge0;
  destruct Hbridge0 as
    (Hedge_bridge0 & _ & Hvisit_add0 & Hcur_base0 & _ & Hmath0);
  unfold dijkstra_edge_loop_bridge_state in Hedge_bridge0;
  destruct Hedge_bridge0 as (Hedge_state0 & _);
  unfold dijkstra_edge_loop_state in Hedge_state0;
  destruct Hedge_state0 as (_ & _ & Hcur_dist0 & _);
  apply Hvisit_add0 in Hvisited_after0;
  let Hvisited_before0 := fresh "Hvisited_before" in
  let Hneighbor_cur0 := fresh "Hneighbor_cur" in
  destruct Hvisited_after0 as [Hvisited_before0 | Hneighbor_cur0];
  [ let Hneighbor_ne_cur := fresh "Hneighbor_ne_cur" in
    let Hdone_subset := fresh "Hdone_subset" in
    let Hdist_base := fresh "Hdist_base" in
    let Hmath_before := fresh "Hmath_before" in
    let Hselected := fresh "Hselected" in
    let Hold_le_candidate := fresh "Hold_le_candidate" in
    assert (Hneighbor_ne_cur : Znth edge to_values 0 <> cur_vertex)
      by (intro Hsame; subst;
          eapply DijkstraGraph_step_aux_no_self;
          eauto using forward_star_model_graph_wf);
    pose proof
      (fun e_abs Hdone =>
        forward_star_done_edge_set_step_aux
          g edge_count head_values to_values weight_values next_values
          cur_vertex edge e_abs Hmodel Hcur_valid Hdone) as Hdone_subset;
    pose proof
      (dijkstra_edge_math_state_no_done_target_dist_base
        g src visited_before visited_after cur_vertex base_dist_values
        (done_edges cur_vertex edge)
        dist_values (cur_vertex, Znth edge to_values 0)
        (Znth edge to_values 0)
        Hdone_subset
        ltac:(apply forward_star_current_edge_not_done; auto)
        Hneighbor_ne_cur Hstep Hmath0) as Hdist_base;
    rewrite dijkstra_array_state_dist_valid in Hdist_base
      by exact Hneighbor_valid;
    unfold dijkstra_after_visit_state, set_state_visited,
      dijkstra_array_state in Hdist_base;
    simpl in Hdist_base;
    destruct (vertex_valid_dec g (Znth edge to_values 0))
      as [_ | Hinvalid_neighbor]; [| contradiction];
    unfold dijkstra_edge_math_state in Hmath0;
    destruct Hmath0 as (_ & Hmath_before & Hselected & _);
    pose proof
      (dijkstra_math_invariant_no_relax_to_old_visited
        g vertex_count src visited_before base_dist_values
        cur_vertex (Znth edge to_values 0)
        (cur_vertex, Znth edge to_values 0)
        Hsize Hnonneg Hcur_valid Hneighbor_valid Hmath_before
        Hselected Hvisited_before0 Hstep) as Hold_le_candidate;
    rewrite <- Hcur_base0 in Hold_le_candidate;
    rewrite (cell_as_distance_finite cur_distance) in Hold_le_candidate
      by exact Hcur_finite;
    rewrite Hweight in Hold_le_candidate;
    simpl in Hold_le_candidate;
    rewrite <- Hdist_base in Hold_le_candidate;
    unfold cell_as_distance, DijkstraGraph.cell_as_distance, Z_op_le
      in Hold_le_candidate;
    destruct (Z.eq_dec
      (dist_cell dist_values (Znth edge to_values 0))
      DijkstraGraph.infinity);
    [contradiction | lia]
  | rewrite Hneighbor_cur0 in Hrelax;
    rewrite Hcur_dist0 in Hrelax;
    lia ].

Lemma dijkstra_lfs_first_edge_body_math_step :
  forall edge queue_items,
    Hoare
      (dijkstra_first_edge_loop_math_model
        g src edge queue_items
        head_values to_values weight_values next_values)
      (dijkstra_lfs_edge_body
        head_values to_values weight_values next_values
        src 0 (edge, queue_items))
      (fun result s =>
        match result with
        | by_continue acc =>
            dijkstra_first_edge_loop_math_model
              g src (fst acc) (snd acc)
              head_values to_values weight_values next_values s
        | by_break queue_items_done =>
            dijkstra_loop_math_model g src queue_items_done s
        end).
Proof.
  intros edge queue_items.
  dijkstra_edge_body_hoare.
  - 
    subst edge.
    unfold dijkstra_first_edge_loop_math_model in Hpre.
    destruct Hpre as (dist_values & Hstate & Hbridge).
    assert (Hsrc_valid : vertex_valid g src)
      by (unfold dijkstra_first_edge_loop_math_bridge_state,
          dijkstra_edge_loop_bridge_state,
          dijkstra_edge_loop_state in Hbridge; tauto).
    unfold dijkstra_loop_math_model.
    exists (source_visited_set src), dist_values.
    split; [exact Hstate |].
    unfold dijkstra_first_edge_loop_math_bridge_state in Hbridge.
    destruct Hbridge as (Hedge_bridge & _ & Hfirst).
    unfold dijkstra_loop_math_bridge_state.
    split.
    + eapply dijkstra_edge_loop_bridge_to_loop_bridge; eauto.
    + split.
      * unfold visited_set_valid, source_visited_set.
        intros v Hv; subst; exact Hsrc_valid.
      * eapply dijkstra_first_step_full_done_to_math.
        -- eapply forward_star_model_graph_wf; eauto.
        -- exact Hsrc_valid.
        -- exact Hnonneg.
        -- eapply dijkstra_first_step_math_state_done_equiv.
           ++ intros e_abs.
              eapply forward_star_done_edge_set_minus_one_equiv_step_aux;
                eauto.
        ++ exact Hfirst.
  - 
    destruct Hrelax_assume as (Hweight_nonneg & _ & Hrelax_state).
    unfold dijkstra_first_edge_loop_math_model in Hpre.
    destruct Hpre as (dist_values & Hstate & Hbridge).
    pose_first_edge_current_facts edge dist_values queue_items
      Hedge_not_nil Hbridge.
    unfold dijkstra_first_edge_loop_math_bridge_state in Hbridge.
    destruct Hbridge as (Hedge_bridge & Hedge_chain & Hfirst).
    assert (Hcandidate_bounds :
      0 <= 0 + Znth edge weight_values 0 < DijkstraGraph.infinity)
      by (solve_first_edge_candidate_bounds
        edge Hsrc_valid Hneighbor_valid Hcurrent_weight).
    erewrite graph_state_model_dist_cell in Hrelax_state by eauto.
    pose proof Hstate as ((Hshape & Hsafe & _) & _).
    assert (Hneighbor_unvisited :
      ~ source_visited_set src (Znth edge to_values 0)).
    {
      unfold source_visited_set; intro Hsame; subst.
      unfold dijkstra_edge_loop_bridge_state,
        dijkstra_edge_loop_state in Hedge_bridge.
      destruct Hedge_bridge as ((_ & _ & Hsrc_dist & _) & _).
      rewrite Hsrc_dist in Hrelax_state; lia.
    }
    unfold dijkstra_first_edge_loop_math_model.
    exists (replace_Znth (Znth edge to_values 0)
             (0 + Znth edge weight_values 0) dist_values).
    split.
    + eapply graph_state_model_replace_Znth_set_state_distance; eauto.
    + unfold dijkstra_first_edge_loop_math_bridge_state.
      split.
      * eapply dijkstra_edge_loop_bridge_relax_update_push_result;
          eauto using forward_star_next_0_lower_bound; reflexivity.
      * split.
        -- eapply forward_star_next_0_nil_or_chain; eauto.
        -- first_edge_done_equiv edge
             (replace_Znth (Znth edge to_values 0)
               (0 + Znth edge weight_values 0) dist_values).
              eapply dijkstra_first_step_invariant_add_edge;
                eauto;
                try solve_current_edge_add_side_condition.
              ** erewrite dijkstra_array_state_dist_replace_other
                   by (eauto; lia).
                 reflexivity.
              ** erewrite dijkstra_array_state_dist_replace_same by eauto.
                 rewrite Hcurrent_weight.
                 replace (0 + Znth edge weight_values 0)
                   with (Znth edge weight_values 0) by lia.
                 reflexivity.
              ** intros v Hneq_neighbor.
                 erewrite dijkstra_array_state_dist_replace_other by eauto.
                 reflexivity.
  - 
    unfold dijkstra_first_edge_loop_math_model in Hpre.
    destruct Hpre as (dist_values & Hstate & Hbridge).
    pose_first_edge_current_facts edge dist_values queue_items
      Hedge_not_nil Hbridge.
    unfold dijkstra_first_edge_loop_math_bridge_state in Hbridge.
    destruct Hbridge as (Hedge_bridge & Hedge_chain & Hfirst).
    assert (Hcandidate_bounds :
      0 <= 0 + Znth edge weight_values 0 < DijkstraGraph.infinity)
      by (solve_first_edge_candidate_bounds
        edge Hsrc_valid Hneighbor_valid Hcurrent_weight).
      assert (Hskip_cell :
        dist_cell dist_values (Znth edge to_values 0) <=
          0 + Znth edge weight_values 0)
      by (eapply dijkstra_skip_assume_to_dist_cell; eauto).
      unfold dijkstra_first_edge_loop_math_model.
      exists dist_values.
      split; [exact Hstate |].
	      unfold dijkstra_first_edge_loop_math_bridge_state.
	      split.
	      * eapply dijkstra_edge_loop_bridge_next;
          eauto using forward_star_next_0_lower_bound.
	      * split.
		        -- eapply forward_star_next_0_nil_or_chain; eauto.
	        -- first_edge_done_equiv edge dist_values.
                pose proof Hfirst as Hfirst_cut.
                unfold Dijkstra.first_step_invariant in Hfirst_cut.
                destruct Hfirst_cut as (_ & _ & _ & Hcut).
                assert (Hneighbor_ne_src : Znth edge to_values 0 <> src)
                  by (intro Heq; subst;
                      eapply DijkstraGraph_step_aux_no_self;
                      eauto using forward_star_model_graph_wf).
                eapply dijkstra_first_step_invariant_add_edge;
                  eauto;
                  try solve_current_edge_add_side_condition.
                ** exfalso.
                   assert (Hno_old :
                     forall e_abs,
                       done_edges src edge e_abs ->
                       ~ dijkstra_step_aux g e_abs src (Znth edge to_values 0)).
                   { eapply dijkstra_done_no_same_target; eauto.
                     - solve_forward_star_done_subset.
                     - apply forward_star_current_edge_not_done; auto. }
                   pose proof
                     (Hcut (Znth edge to_values 0) Hneighbor_ne_src Hno_old)
                     as Hdist_none.
                   rewrite dijkstra_array_state_dist_valid in Hdist_none
                     by exact Hneighbor_valid.
                   unfold cell_as_distance, DijkstraGraph.cell_as_distance
                     in Hdist_none.
                   destruct (Z.eq_dec
                     (dist_cell dist_values (Znth edge to_values 0))
                     DijkstraGraph.infinity); [lia | discriminate].
Qed.

Lemma dijkstra_lfs_edge_body_math_step :
  forall visited_before visited_after
         cur_vertex cur_distance edge base_dist_values queue_items,
    Hoare
      (dijkstra_edge_loop_math_model
        g src visited_before visited_after cur_vertex cur_distance edge
        base_dist_values queue_items
        head_values to_values weight_values next_values)
      (dijkstra_lfs_edge_body
        head_values to_values weight_values next_values
        cur_vertex cur_distance (edge, queue_items))
      (fun result s =>
        match result with
        | by_continue acc =>
            dijkstra_edge_loop_math_model
              g src visited_before visited_after cur_vertex cur_distance
              (fst acc) base_dist_values (snd acc)
              head_values to_values weight_values next_values s
        | by_break queue_items_done =>
            dijkstra_loop_math_model g src queue_items_done s
        end).
Proof.
  intros visited_before visited_after cur_vertex cur_distance edge
    base_dist_values queue_items.
  dijkstra_edge_body_hoare.
  - 
    unfold dijkstra_edge_loop_math_model in Hpre.
    destruct Hpre as (dist_values & Hstate & Hcur_finite & Hbridge).
    unfold dijkstra_loop_math_model.
    exists visited_after, dist_values.
    split; [exact Hstate |].
    subst edge.
    unfold dijkstra_edge_loop_math_bridge_state in Hbridge.
    destruct Hbridge as
      (Hedge_bridge & Hvisited_valid & Hvisit_add & _ & _ & Hmath_edge).
    assert (Hcur_valid : vertex_valid g cur_vertex).
    {
      unfold dijkstra_edge_loop_bridge_state in Hedge_bridge.
      destruct Hedge_bridge as (Hedge_state & _).
      unfold dijkstra_edge_loop_state in Hedge_state.
      tauto.
    }
    unfold dijkstra_loop_math_bridge_state.
    split.
    + eapply dijkstra_edge_loop_bridge_to_loop_bridge; eauto.
    + split.
      * unfold visited_set_valid in *.
        intros v Hv_after.
        unfold visited_set_add in Hvisit_add.
        destruct (proj1 (Hvisit_add v) Hv_after) as [Hv_before | ->].
        -- apply Hvisited_valid; exact Hv_before.
        -- exact Hcur_valid.
      * eapply dijkstra_edge_math_state_full_done_to_math; eauto.
        -- eapply forward_star_model_graph_wf; eauto.
        -- intros e.
           eapply forward_star_done_edge_set_minus_one_equiv_step_aux;
             eauto.
  - 
    destruct Hrelax_assume as (Hweight_nonneg & _ & Hrelax_state).
    unfold dijkstra_edge_loop_math_model in Hpre.
    destruct Hpre as (dist_values & Hstate & Hcur_finite & Hbridge).
    pose_dijkstra_edge_loop_current_facts
      edge_count cur_vertex edge head_values next_values
      Hsize Hmodel Hedge_not_nil Hbridge.
    assert (Hcandidate_bounds :
      0 <= cur_distance + Znth edge weight_values 0 <
        DijkstraGraph.infinity)
      by (solve_edge_loop_candidate_bounds
        visited_before cur_vertex cur_distance edge base_dist_values
        Hbridge Hcur_finite Hcur_valid Hneighbor_valid Hweight).
    erewrite graph_state_model_dist_cell in Hrelax_state by eauto.
    pose proof Hstate as ((Hshape & Hsafe & _) & _).
    assert (Hneighbor_unvisited :
      ~ visited_after (Znth edge to_values 0))
      by (solve_edge_loop_relax_neighbor_unvisited
        visited_before visited_after cur_vertex cur_distance edge
        base_dist_values dist_values Hbridge Hcur_valid Hneighbor_valid
        Hstep Hweight Hcur_finite Hrelax_state).
    unfold dijkstra_edge_loop_math_model.
    exists (replace_Znth (Znth edge to_values 0)
             (cur_distance + Znth edge weight_values 0) dist_values).
    split.
    + eapply graph_state_model_replace_Znth_set_state_distance; eauto.
    + split.
      * exact Hcur_finite.
      * unfold dijkstra_edge_loop_math_bridge_state in Hbridge.
        destruct Hbridge as
          (Hedge_bridge & Hvisited_valid & Hvisit_add
           & Hcur_base & _ & Hmath).
        unfold dijkstra_edge_loop_math_bridge_state.
        split.
        -- eapply dijkstra_edge_loop_bridge_relax_update_push_result;
             eauto.
           eapply forward_star_next_0_lower_bound; eauto.
        -- do 3 (split; [eassumption |]).
           split.
           ++ eapply forward_star_next_0_nil_or_chain; eauto.
           ++ finish_edge_math_done dijkstra_edge_math_state_relax_update.
  - 
    unfold dijkstra_edge_loop_math_model in Hpre.
    destruct Hpre as (dist_values & Hstate & Hcur_finite & Hbridge).
    pose_dijkstra_edge_loop_current_facts
      edge_count cur_vertex edge head_values next_values
      Hsize Hmodel Hedge_not_nil Hbridge.
    pose proof Hstate as ((_ & Hsafe & _) & _).
    assert (Hcandidate_bounds :
      0 <= cur_distance + Znth edge weight_values 0 <
        DijkstraGraph.infinity)
      by (solve_edge_loop_candidate_bounds
        visited_before cur_vertex cur_distance edge base_dist_values
        Hbridge Hcur_finite Hcur_valid Hneighbor_valid Hweight).
    assert (Hskip_cell :
      dist_cell dist_values (Znth edge to_values 0) <=
        cur_distance + Znth edge weight_values 0)
      by (eapply dijkstra_skip_assume_to_dist_cell; eauto).
    unfold dijkstra_edge_loop_math_model.
    exists dist_values.
    split; [exact Hstate |].
    split; [exact Hcur_finite |].
    unfold dijkstra_edge_loop_math_bridge_state in Hbridge.
    destruct Hbridge as
      (Hedge_bridge & Hvisited_valid & Hvisit_add & Hcur_base
       & _ & Hmath).
    unfold dijkstra_edge_loop_math_bridge_state.
    split.
    + eapply dijkstra_edge_loop_bridge_next; eauto.
      eapply forward_star_next_0_lower_bound; eauto.
    + do 3 (split; [eassumption |]).
      split.
      * eapply forward_star_next_0_nil_or_chain; eauto.
      * finish_edge_math_done dijkstra_edge_math_state_relax_skip.
Qed.

Lemma dijkstra_loop_bridge_pop_selected_min :
  forall visited_set dist_values queue_items queue_items_after
         cur_vertex cur_distance,
    dijkstra_loop_bridge_state g src visited_set dist_values queue_items ->
    priority_queue_pop_result queue_items queue_items_after
      cur_vertex cur_distance ->
    cur_distance = dist_cell dist_values cur_vertex ->
    0 <= cur_distance < DijkstraGraph.infinity ->
    dijkstra_selected_min g visited_set dist_values cur_vertex.
Proof.
  intros visited_set dist_values queue_items queue_items_after
    cur_vertex cur_distance Hbridge Hpop Hcur_dist Hcur_finite.
  unfold dijkstra_selected_min.
  destruct Hbridge as (Hloop_state & Hrefines).
  assert (Hcur_valid : vertex_valid g cur_vertex)
    by (eapply priority_queue_pop_result_vertex_valid; eauto).
  pose proof
    (dijkstra_array_state_graph_state_model
      g vertex_count visited_set dist_values Hsize
      ltac:(unfold dijkstra_loop_state in Hloop_state; tauto)
      ltac:(unfold dijkstra_loop_state in Hloop_state; tauto))
    as ((_ & Hsafe_array & Hdist_cells) & Hvisited_model & Hinvalid).
  destruct Hrefines as (Hcovers & Hfresh & Hlower & _ & _).
  assert (Hcur_unvisited_set : ~ visited_set cur_vertex).
  {
    apply (Hfresh cur_distance cur_vertex).
    - dijkstra_pop_cons; simpl; auto.
    - exact Hcur_dist.
  }
  split.
  - intro Hvisited_state.
    apply Hcur_unvisited_set.
    apply (proj2 (Hvisited_model cur_vertex Hcur_valid)).
    exact Hvisited_state.
  - intros v Hunvisited.
    destruct (classic (vertex_valid g v)) as [Hvalid | Hnot_valid].
    + pose proof (Hdist_cells v Hvalid) as Hcell_v.
      assert (~ visited_set v) as Hunvisited_set.
      {
        intro Hvisited_set.
        apply Hunvisited.
        apply (proj1 (Hvisited_model v Hvalid)).
        exact Hvisited_set.
      }
      assert (cur_distance <= dist_cell dist_values v) as Hcell_le.
      {
        destruct (Z_lt_ge_dec (dist_cell dist_values v)
          DijkstraGraph.infinity) as [Hfinite_v | Hinf].
        - pose proof (Hcovers v Hvalid Hunvisited_set Hfinite_v) as Hin.
          unfold priority_queue_pop_result in Hpop.
          destruct Hpop as (_ & Hitems & Hordered_pop).
          subst queue_items.
          simpl in Hin.
          destruct Hin as [Heq | Hin_tail].
          + inversion Heq; subst; lia.
          + simpl in Hordered_pop.
            destruct Hordered_pop as (Hhead & _).
            specialize (Hhead (dist_cell dist_values v, v) Hin_tail).
            simpl in Hhead. exact Hhead.
        - pose proof
            (graph_has_size_vertex_valid_storage
              g vertex_count v Hsize Hvalid) as Hv_storage.
          pose proof (Hsafe_array v Hv_storage); lia.
      }
      rewrite dijkstra_array_state_dist_valid by exact Hcur_valid.
      rewrite <- Hcur_dist.
      destruct (@dist Z (dijkstra_array_state g visited_set
        dist_values) v) as [dv |] eqn:Hdist_v.
      * simpl in Hcell_v. subst dv.
        rewrite (cell_as_distance_finite cur_distance)
          by exact Hcur_finite.
        simpl. exact Hcell_le.
      * rewrite (cell_as_distance_finite cur_distance)
          by exact Hcur_finite.
        simpl. exact I.
    + pose proof (Hinvalid v Hnot_valid) as (Hdist_v & _).
      rewrite dijkstra_array_state_dist_valid by exact Hcur_valid.
      rewrite <- Hcur_dist, Hdist_v.
      rewrite (cell_as_distance_finite cur_distance)
        by exact Hcur_finite.
      simpl. exact I.
Qed.

Lemma visited_set_add_cons :
  forall visited_set u,
    visited_set_add visited_set u (fun v => visited_set v \/ v = u).
Proof. unfold visited_set_add; tauto. Qed.

Lemma dijkstra_lfs_edge_loop_after_pop_equal_math :
  forall queue_items queue_items_after cur_vertex cur_distance,
    Hoare
      (fun s =>
        exists visited_before dist_values s_before,
          s = set_state_visited cur_vertex s_before /\
          cur_distance = state_distance_cell cur_vertex s_before /\
          priority_queue_pop_result
            queue_items queue_items_after cur_vertex cur_distance /\
          graph_state_model g visited_before dist_values s_before /\
          dijkstra_loop_math_bridge_state
            g src visited_before dist_values queue_items)
      (dijkstra_lfs_edge_loop
        head_values to_values weight_values next_values
        cur_vertex cur_distance (Znth cur_vertex head_values 0)
        queue_items_after)
      (fun queue_items_done s =>
        dijkstra_loop_math_model g src queue_items_done s).
Proof.
  intros queue_items queue_items_after cur_vertex cur_distance.
  apply Hoare_pre_ex.
  intros visited_before.
  apply Hoare_pre_ex.
  intros dist_values.
  apply Hoare_pre_ex.
  intros s_before.
  eapply Hoare_conseq_pre.
  2: {
    unfold dijkstra_lfs_edge_loop.
    eapply Hoare_repeat_break with
      (P := fun acc =>
        dijkstra_edge_loop_math_model
          g src visited_before (fun v => visited_before v \/ v = cur_vertex)
          cur_vertex cur_distance (fst acc) dist_values (snd acc)
          head_values to_values weight_values next_values).
    intros [edge0 queue_items0].
    cbn [fst snd].
    eapply dijkstra_lfs_edge_body_math_step; eauto.
  }
  intros s Hpre.
  destruct Hpre as
    (Hvisit & Heq_dist & Hpop & Hstate & Hmath_bridge).
  subst s.
  unfold dijkstra_loop_math_bridge_state in Hmath_bridge.
  destruct Hmath_bridge as
    (Hloop_bridge & Hvisited_valid & Hmath).
  unfold dijkstra_loop_bridge_state in Hloop_bridge.
  destruct Hloop_bridge as (Hloop_state & Hrefines).
  pose proof Hrefines as (_ & _ & _ & Hfinite & _).
  assert (Hcur_valid : vertex_valid g cur_vertex).
  {
    eapply priority_queue_pop_result_vertex_valid; eauto.
  }
  assert (Hcur_dist :
    cur_distance = dist_cell dist_values cur_vertex).
  {
    erewrite graph_state_model_dist_cell in Heq_dist by eauto.
    exact Heq_dist.
  }
  assert (Hcur_finite :
    0 <= cur_distance < DijkstraGraph.infinity).
  {
    split.
    - rewrite Hcur_dist.
	      pose proof Hstate as ((Hshape & Hsafe & _) & _).
      apply Hsafe.
	      eapply graph_has_size_vertex_valid_storage; eauto.
	    - apply (Hfinite cur_distance cur_vertex).
      dijkstra_pop_cons; simpl; auto.
  }
  unfold dijkstra_edge_loop_math_model.
  exists dist_values.
  split.
  - apply graph_state_model_visit_state
      with (visited_set := visited_before);
      auto using visited_set_add_cons.
  - split; [exact Hcur_finite |].
    unfold dijkstra_edge_loop_math_bridge_state.
    split.
    + eapply dijkstra_after_pop_bridge_state_equal_to_edge_bridge.
      * exact Hcur_valid.
      * apply visited_set_add_cons.
      * symmetry. exact Hcur_dist.
	      * eapply forward_star_head_0_lower_bound; eauto.
      * eapply dijkstra_loop_bridge_state_pop_result; eauto.
        unfold dijkstra_loop_bridge_state.
        exact (conj Hloop_state Hrefines).
    + split; [exact Hvisited_valid |].
      split; [apply visited_set_add_cons |].
      split; [exact Hcur_dist |].
      split.
	      * eapply forward_star_head_0_nil_or_chain; eauto.
      * assert (Hselected :
          dijkstra_selected_min g visited_before dist_values cur_vertex).
        {
          eapply dijkstra_loop_bridge_pop_selected_min; eauto.
          exact (conj Hloop_state Hrefines).
        }
        eapply (dijkstra_edge_math_state_done_equiv
          g src visited_before
          (fun v => visited_before v \/ v = cur_vertex)
          cur_vertex dist_values
          (fun _ : DijkstraGraph.E => False)
          (done_edges cur_vertex (Znth cur_vertex head_values 0))
          dist_values).
        -- intros e_abs.
           symmetry.
           eapply forward_star_done_edge_set_head_empty_equiv; eauto.
        -- unfold dijkstra_edge_math_state, Dijkstra.relax_step_invariant.
           split; [apply visited_set_add_cons |].
           split; [exact Hmath |].
           split; [exact Hselected |].
           split.
           ++ unfold dijkstra_after_visit_state, set_state_visited,
                dijkstra_array_state; simpl; sets_unfold.
              intro v; split.
              ** intros [Hvalid_after Hvisited_after].
                 destruct Hvisited_after as [Hvisited_before | Heq].
                 --- left; split; [apply Hvisited_valid |]; exact Hvisited_before.
                 --- right; symmetry; exact Heq.
              ** intros [[Hvalid_before Hvisited_before] | Heq]; subst.
                 --- split; [exact Hvalid_before | left; exact Hvisited_before].
                 --- split; [exact Hcur_valid | right; reflexivity].
           ++ split; [reflexivity |].
              split.
              ** intros v e _ Hfalse _. contradiction.
              ** intros v _ _.
                 unfold dijkstra_after_visit_state, set_state_visited,
                   dijkstra_array_state; simpl.
                 destruct (vertex_valid_dec g v); reflexivity.
Qed.

Lemma dijkstra_lfs_loop_body_math_step :
  forall queue_items,
    Hoare
      (dijkstra_loop_math_model g src queue_items)
      (dijkstra_lfs_loop_body
        head_values to_values weight_values next_values queue_items)
      (fun result s =>
        match result with
        | by_continue queue_items_next =>
            dijkstra_loop_math_model g src queue_items_next s
        | by_break _ =>
            dijkstra_loop_math_model g src nil s
        end).
Proof.
  intros queue_items.
  dijkstra_loop_body_hoare.
  - 
    subst queue_items.
    exact Hpre.
  - 
    eapply Hoare_conseq_pre.
    2: {
      apply (dijkstra_lfs_edge_loop_after_pop_equal_math
        queue_items queue_items_after cur_vertex cur_distance).
    }
    intros s Hpost.
    destruct Hpost as (s0 & Hvisit & Heq_dist & Hpop & _Hnonempty & Hpre).
    unfold dijkstra_loop_math_model in Hpre.
    destruct Hpre as
      (visited_before & dist_values & Hstate & Hmath_bridge).
    exists visited_before, dist_values, s0.
    do 4 (split; [eassumption |]); eassumption.
  - 
    unfold dijkstra_loop_math_model in Hpre.
    destruct Hpre as
      (visited_set & dist_values & Hstate & Hmath_bridge).
    unfold dijkstra_loop_math_bridge_state in Hmath_bridge.
    destruct Hmath_bridge as
      (Hloop_bridge & Hvisited_valid & Hmath).
	    unfold dijkstra_loop_bridge_state in Hloop_bridge.
	    destruct Hloop_bridge as (Hloop_state & Hrefines).
    assert (Hcur_valid : vertex_valid g cur_vertex).
    {
      eapply priority_queue_pop_result_vertex_valid; eauto.
    }
    assert (Hstale :
      cur_distance <> dist_cell dist_values cur_vertex).
    {
      intro Heq.
      apply Hneq_dist.
      erewrite graph_state_model_dist_cell by eauto.
      exact Heq.
    }
    unfold dijkstra_loop_math_model.
    exists visited_set, dist_values.
    split; [exact Hstate |].
    unfold dijkstra_loop_math_bridge_state.
    split.
    + eapply dijkstra_after_pop_bridge_state_stale_to_loop_bridge; eauto.
      eapply dijkstra_loop_bridge_state_pop_result; eauto.
      unfold dijkstra_loop_bridge_state.
      exact (conj Hloop_state Hrefines).
    + split; assumption.
Qed.

Ltac invert_initial_pop src queue_items_after cur_vertex cur_distance Hpop :=
  pose proof (priority_queue_pop_result_cons
    ((0, src) :: nil) queue_items_after cur_vertex cur_distance Hpop)
    as Hitems;
  inversion Hitems; subst cur_distance cur_vertex queue_items_after.

Lemma dijkstra_lfs_initial_loop_body_math_step :
    Hoare
      (eq (initial_state src))
      (dijkstra_lfs_loop_body
        head_values to_values weight_values next_values
        ((0, src) :: nil))
      (fun result s =>
        match result with
        | by_continue queue_items_next =>
            dijkstra_loop_math_model g src queue_items_next s
        | by_break _ => False
        end).
Proof.
  dijkstra_loop_body_hoare.
  - 
    discriminate Hempty.
  - 
    apply Hoare_state_intro.
    intros s Hpost.
    destruct Hpost as (s0 & Hvisit & Heq_dist & Hpop & _Hnonempty & Hinitial).
    subst s0.
    invert_initial_pop src queue_items_after cur_vertex cur_distance Hpop.
    subst s.
    eapply Hoare_conseq_pre.
    2: {
      unfold dijkstra_lfs_edge_loop.
      eapply Hoare_repeat_break with
        (P := fun acc =>
          dijkstra_first_edge_loop_math_model
            g src (fst acc) (snd acc)
            head_values to_values weight_values next_values).
      intros [edge0 queue_items0]; cbn [fst snd].
      eapply dijkstra_lfs_first_edge_body_math_step; eauto.
    }
    intros s Hcurrent.
    subst s.
    apply (initial_first_edge_loop_math_model
      g vertex_count edge_count src
      head_values to_values weight_values next_values
      Hsize Hsrc Hnonneg Hmodel).
  - 
    subst s.
    invert_initial_pop src queue_items_after cur_vertex cur_distance Hpop.
    exfalso.
    apply Hneq_dist.
    symmetry.
    apply initial_state_source_distance_cell.
Qed.

End LoopMathProofs.

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

Lemma dijkstra_lfs_program_correct :
  forall g vertex_count edge_count src
         head_values to_values weight_values next_values dist_values,
    graph_has_size g vertex_count ->
    vertex_valid g src ->
    dijkstra_nonnegative_edges g ->
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    dijkstra_no_overflow g src ->
    safeExec (graph_dist_model g dist_values)
      (return tt)
      (result_state (eq (initial_state src))
        (dijkstra_lfs_program
          src head_values to_values weight_values next_values)) ->
    dijkstra_shortest_dist g src dist_values.
Proof.
  intros g vertex_count edge_count src head_values to_values
    weight_values next_values dist_values Hsize Hsrc Hnonneg Hmodel
    Hno_overflow Hsafe.
  apply safeExec_ret in Hsafe as (s & Hstate & Hresult).
  unfold result_state in Hresult; sets_unfold in Hresult.
  destruct Hresult as (s_initial & Hinitial & Hrun_lfs).
  subst s_initial.
  assert (Hhoare :
    Hoare
      (eq (initial_state src))
      (dijkstra_lfs_program
        src head_values to_values weight_values next_values)
      (fun _ s => dijkstra_loop_math_model g src nil s)).
  {
    unfold dijkstra_lfs_program, dijkstra_lfs_loop.
    eapply Hoare_proequiv.
    - symmetry.
      apply (repeat_break_unfold
        (dijkstra_lfs_loop_body
          head_values to_values weight_values next_values)).
    - eapply Hoare_bind
        with (Q := fun result s =>
          match result with
          | by_continue queue_items_next =>
              dijkstra_loop_math_model g src queue_items_next s
          | by_break _ => False
          end).
      + apply (dijkstra_lfs_initial_loop_body_math_step
          g vertex_count edge_count src
          head_values to_values weight_values next_values
          Hsize Hsrc Hnonneg Hmodel Hno_overflow).
      + intros [queue_items_next | []].
        * unfold dijkstra_lfs_loop.
          eapply Hoare_repeat_break with
            (P := dijkstra_loop_math_model g src).
          intros queue_items0.
          eapply (dijkstra_lfs_loop_body_math_step
            g vertex_count edge_count src
            head_values to_values weight_values next_values
            Hsize Hnonneg Hmodel Hno_overflow); eauto.
        * unfold Hoare; contradiction.
  }
  eapply dijkstra_loop_math_model_nil_to_shortest; eauto.
  exact (Hhoare (initial_state src) tt s eq_refl Hrun_lfs).
Qed.

End DijkstraLinkedForwardStar.
