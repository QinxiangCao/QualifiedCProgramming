Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.ClassicalDescription.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass.
From GraphLib Require Import Zweight.
From GraphLib Require Import dijkstra.
From GraphLib Require Import epath.
From MaxMinLib Require Import Interface.
Require Import Algorithms.Dijkstra.Dijkstra.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib Require Export MonadLib.
From MonadLib.StateRelMonad Require Export StateRelBasic StateRelMonad.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export SimpleC.EE.LLM_bench.Algorithms.Dijkstra.Dijkstra_linked_forward_star_common_lib.
Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.

Export MonadNotation.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope monad.
Local Open Scope sac.

Import DijkstraGraph.
Import DijkstraLinkedForwardStar.

Module DijkstraIndexQueue.

Ltac dijkstra_index_min_epath_refl :=
  eapply (@dijkstra.min_value_weight_epath_refl DijkstraGraph.G DijkstraGraph.V
    DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance
    _ DijkstraGraph.PathData DijkstraGraph.path_instance
    DijkstraGraph.empty_path_instance DijkstraGraph.single_path_instance
    DijkstraGraph.concat_path_instance DijkstraGraph.destruct1n_path_instance
    DijkstraGraph.weight_instance); eauto.

Definition index_queue_push_result
    (before after : multiset (Z * Z)) (vertex distance : Z) : Prop :=
  after = multiset_insert before (heap_item distance vertex).

Definition index_queue_pop_result
    (before after : multiset (Z * Z)) (vertex distance : Z) : Prop :=
  exists popped,
    popped = heap_item distance vertex /\
    multiset_minimum before popped /\
    after = multiset_remove before popped.

Definition heap_queue_items_valid
    (g : DijkstraGraph.G) (queue_set : multiset (Z * Z)) : Prop :=
  forall item,
    In item (mlist queue_set) ->
    vertex_valid g (item_data item) /\
    0 <= item_key item <= DijkstraGraph.infinity.

Definition heap_queue_refines_unvisited_dist
    (g : DijkstraGraph.G) (visited_set : Z -> Prop)
    (dist_values : list Z) (queue_set : multiset (Z * Z)) : Prop :=
  priority_queue_refines_unvisited_dist
    g visited_set dist_values (mlist queue_set).

Definition heap_queue_capacity
    (edge_count : Z) (queue_set : multiset (Z * Z)) : Prop :=
  multiset_size queue_set <= edge_count + 1.

Definition heap_queue_has_push_room
    (edge_count : Z) (queue_set : multiset (Z * Z)) : Prop :=
  multiset_size queue_set < edge_count + 1.

Definition heap_queue_capacity_budget
    (edge_count : Z) (queue_set : multiset (Z * Z)) : Prop :=
  0 <= edge_count /\
  heap_queue_capacity edge_count queue_set.

Definition processed_edge_budget
    (edge_count : Z) (processed_edges : list Z)
    (queue_set : multiset (Z * Z)) : Prop :=
  0 <= edge_count /\
  NoDup processed_edges /\
  Forall (edge_index edge_count) processed_edges /\
  multiset_size queue_set <= Zlength processed_edges + 1.

Definition forward_star_suffix_fresh
    (next_values : list Z) (edge : Z)
    (processed_edges : list Z) : Prop :=
  forall idx,
    next_chain next_values edge idx ->
    ~ In idx processed_edges.

Definition forward_star_unvisited_fresh
    (head_values next_values : list Z)
    (visited_set : Z -> Prop)
    (processed_edges : list Z) : Prop :=
  forall u idx,
    storage_index u ->
    ~ visited_set u ->
    next_chain next_values (Znth u head_values (-1)) idx ->
    ~ In idx processed_edges.

Definition forward_star_chains_disjoint
    (head_values next_values : list Z) : Prop :=
  forall u1 u2 idx,
    storage_index u1 ->
    storage_index u2 ->
    next_chain next_values (Znth u1 head_values (-1)) idx ->
    next_chain next_values (Znth u2 head_values (-1)) idx ->
    u1 = u2.

Definition vertex_pair_valid (g : DijkstraGraph.G) (pair : Z * Z) : Prop :=
  vertex_valid g (fst pair) /\ vertex_valid g (snd pair).

Definition vertex_pair_code (pair : Z * Z) : Z :=
  fst pair * DijkstraGraph.max_vertices + snd pair.

Definition processed_vertex_pair_budget
    (g : DijkstraGraph.G) (processed_pairs : list (Z * Z))
    (queue_set : multiset (Z * Z)) : Prop :=
  NoDup processed_pairs /\
  Forall (vertex_pair_valid g) processed_pairs /\
  multiset_size queue_set <= Zlength processed_pairs + 1.

Definition processed_vertex_pairs_from_visited
    (visited_set : Z -> Prop) (processed_pairs : list (Z * Z)) : Prop :=
  forall u v,
    In (u, v) processed_pairs ->
    visited_set u.

Definition forward_star_pair_suffix_fresh
    (cur_vertex : Z) (to_values next_values : list Z) (edge : Z)
    (processed_pairs : list (Z * Z)) : Prop :=
  forall idx,
    next_chain next_values edge idx ->
    ~ In (cur_vertex, Znth idx to_values 0) processed_pairs.

Definition heap_queue_loop_capacity_state
    (g : DijkstraGraph.G) (visited_set : Z -> Prop)
    (queue_set : multiset (Z * Z)) : Prop :=
  exists processed_pairs,
    processed_vertex_pair_budget g processed_pairs queue_set /\
    processed_vertex_pairs_from_visited visited_set processed_pairs.

Definition heap_queue_edge_capacity_state
    (g : DijkstraGraph.G) (visited_set : Z -> Prop)
    (cur_vertex edge : Z)
    (head_values to_values next_values : list Z)
    (queue_set : multiset (Z * Z)) : Prop :=
  visited_set cur_vertex /\
  (edge = -1 \/
    next_chain next_values (Znth cur_vertex head_values (-1)) edge) /\
  exists processed_pairs,
    processed_vertex_pair_budget g processed_pairs queue_set /\
    processed_vertex_pairs_from_visited visited_set processed_pairs /\
    forward_star_pair_suffix_fresh
      cur_vertex to_values next_values edge processed_pairs.

Definition dijkstra_heap_loop_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (queue_set : multiset (Z * Z)) : Prop :=
  DijkstraGraph.graph_wf g /\
  vertex_valid g src /\
  nonnegative_edges g /\
  vector_shape dist_values /\
  dist_values_safe dist_values /\
  heap_queue_items_valid g queue_set.

Definition dijkstra_heap_edge_loop_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (cur_vertex cur_distance edge : Z) (dist_values : list Z)
    (queue_set : multiset (Z * Z)) : Prop :=
  dijkstra_heap_loop_state g src visited_set dist_values queue_set /\
  vertex_valid g cur_vertex /\
  dist_cell dist_values cur_vertex = cur_distance /\
  -1 <= edge.

Definition dijkstra_heap_loop_bridge_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (queue_set : multiset (Z * Z)) : Prop :=
  dijkstra_heap_loop_state g src visited_set dist_values queue_set /\
  heap_queue_refines_unvisited_dist
    g visited_set dist_values queue_set.

Definition dijkstra_heap_after_pop_bridge_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z)
    (queue_set_before queue_set_after : multiset (Z * Z))
    (cur_vertex cur_distance : Z) : Prop :=
  dijkstra_heap_loop_state g src visited_set dist_values queue_set_after /\
  heap_queue_refines_unvisited_dist
    g visited_set dist_values queue_set_before /\
  index_queue_pop_result
    queue_set_before queue_set_after cur_vertex cur_distance.

Definition dijkstra_heap_edge_loop_bridge_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (cur_vertex cur_distance edge : Z) (dist_values : list Z)
    (queue_set : multiset (Z * Z)) : Prop :=
  dijkstra_heap_edge_loop_state
    g src visited_set cur_vertex cur_distance edge dist_values queue_set /\
  heap_queue_refines_unvisited_dist
    g visited_set dist_values queue_set.

Definition index_queue_pop_choice
    (queue_set : multiset (Z * Z))
    : program state ((multiset (Z * Z) * Z) * Z) :=
  get (fun _ result =>
    index_queue_pop_result
      queue_set
      (fst (fst result))
      (snd (fst result))
      (snd result)).

Definition index_queue_push_choice
    (queue_set : multiset (Z * Z)) (vertex distance : Z)
    : program state (multiset (Z * Z)) :=
  get (fun _ queue_set_after =>
    index_queue_push_result queue_set queue_set_after vertex distance).

Definition dijkstra_heap_lfs_edge_body
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance : Z)
    (acc : Z * multiset (Z * Z))
    : program state
        (CntOrBrk (Z * multiset (Z * Z)) (multiset (Z * Z))) :=
  let edge := fst acc in
  let queue_set := snd acc in
  choice
    (assume (fun _ => edge = -1);;
     ret (by_break queue_set))
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
        queue_set_after <-
          index_queue_push_choice queue_set neighbor candidate;;
        ret (by_continue (next_edge, queue_set_after)))
       (assume (fun s =>
          edge_weight < 0 \/
          cur_distance > DijkstraGraph.infinity - edge_weight \/
          candidate >= state_distance_cell neighbor s);;
        ret (by_continue (next_edge, queue_set)))).

Definition dijkstra_heap_lfs_edge_loop
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance edge : Z)
    (queue_set : multiset (Z * Z))
    : program state (multiset (Z * Z)) :=
  repeat_break
    (dijkstra_heap_lfs_edge_body
      head_values to_values weight_values next_values
      cur_vertex cur_distance)
    (edge, queue_set).

Definition dijkstra_heap_lfs_loop_body
    (head_values to_values weight_values next_values : list Z)
    (queue_set : multiset (Z * Z))
    : program state (CntOrBrk (multiset (Z * Z)) unit) :=
  choice
    (assume (fun _ => mlist queue_set = nil);;
     ret (by_break tt))
    (assume (fun _ => mlist queue_set <> nil);;
     pop_result <- index_queue_pop_choice queue_set;;
     let queue_set_after := fst (fst pop_result) in
     let cur_vertex := snd (fst pop_result) in
     let cur_distance := snd pop_result in
     choice
      (assume (fun s =>
         cur_distance = state_distance_cell cur_vertex s);;
        update' (set_state_visited cur_vertex);;
        queue_set_after_edges <-
          dijkstra_heap_lfs_edge_loop
            head_values to_values weight_values next_values
            cur_vertex cur_distance
            (Znth cur_vertex head_values 0)
            queue_set_after;;
        ret (by_continue queue_set_after_edges))
       (assume (fun s =>
          cur_distance <> state_distance_cell cur_vertex s);;
        ret (by_continue queue_set_after))).

Definition dijkstra_heap_lfs_loop
    (head_values to_values weight_values next_values : list Z)
    (queue_set : multiset (Z * Z)) : program state unit :=
  repeat_break
    (dijkstra_heap_lfs_loop_body
      head_values to_values weight_values next_values)
    queue_set.

Definition singleton_source_queue (src : Z) : multiset (Z * Z) :=
  multiset_insert (list_to_multiset (@nil (Z * Z))) (heap_item 0 src).

Definition dijkstra_heap_lfs_program
    (src : Z)
    (head_values to_values weight_values next_values : list Z)
    : program state unit :=
  dijkstra_heap_lfs_loop head_values to_values weight_values next_values
    (singleton_source_queue src).

Definition dijkstra_heap_loop_phase_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (queue_set : multiset (Z * Z)) : Prop :=
  (visited_set_empty visited_set /\
   dijkstra_init_dist (DijkstraGraph.vertex_count g) src dist_values /\
   shortest_path_relaxation_bounded g src DijkstraGraph.infinity /\
   queue_set = singleton_source_queue src) \/
  (visited_set_valid g visited_set /\
   shortest_path_relaxation_bounded g src DijkstraGraph.infinity /\
   dijkstra_math_invariant g src visited_set dist_values).

Definition dijkstra_heap_edge_phase_state
    (g : DijkstraGraph.G) (src cur_vertex cur_distance edge : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (queue_set : multiset (Z * Z)) : Prop :=
  0 <= cur_distance < DijkstraGraph.infinity /\
  (((forall v, visited_set v <-> v = src) /\
    shortest_path_relaxation_bounded g src DijkstraGraph.infinity /\
    cur_vertex = src /\
    cur_distance = 0 /\
    (edge = -1 \/ next_chain next_values (Znth src head_values (-1)) edge) /\
    dijkstra_first_step_math_state
      g src
      (forward_star_done_edge_set
        head_values to_values weight_values next_values src edge)
      dist_values) \/
   (exists visited_before base_dist_values,
     visited_set_valid g visited_before /\
     shortest_path_relaxation_bounded g src DijkstraGraph.infinity /\
     visited_set_add visited_before cur_vertex visited_set /\
     cur_distance = dist_cell base_dist_values cur_vertex /\
     (edge = -1 \/ next_chain next_values (Znth cur_vertex head_values (-1)) edge) /\
     dijkstra_edge_math_state g src visited_before visited_set
       cur_vertex base_dist_values
       (forward_star_done_edge_set
         head_values to_values weight_values next_values cur_vertex edge)
       dist_values)).

Definition dijkstra_heap_lfs_edge_loop_after_body_cont
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance : Z)
    (step_result :
      CntOrBrk (Z * multiset (Z * Z)) (multiset (Z * Z)))
    : program state unit :=
  queue_set_after <-
    match step_result with
    | by_continue edge_state =>
        repeat_break
          (dijkstra_heap_lfs_edge_body
            head_values to_values weight_values next_values
            cur_vertex cur_distance)
          edge_state
    | by_break queue_set_done => ret queue_set_done
    end;;
  dijkstra_heap_lfs_loop
    head_values to_values weight_values next_values
    queue_set_after.

Definition dijkstra_heap_lfs_edge_loop_cont
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance edge : Z)
    (queue_set : multiset (Z * Z)) : program state unit :=
  queue_set_after <-
    dijkstra_heap_lfs_edge_loop
      head_values to_values weight_values next_values
      cur_vertex cur_distance edge queue_set;;
  dijkstra_heap_lfs_loop
    head_values to_values weight_values next_values
    queue_set_after.

Lemma dijkstra_init_dist_first_step_math_state_empty :
  forall g vertex_count src dist_values,
    graph_has_size g vertex_count ->
    vertex_valid g src ->
    dijkstra_init_dist vertex_count src dist_values ->
    dijkstra_first_step_math_state g src
      (fun _ : DijkstraGraph.E => False) dist_values.
Proof.
  intros g vertex_count src dist_values Hsize Hsrc Hinit.
  destruct Hinit as (Hshape & Hsafe & Hcount & Hsrc_bounds & Hcell).
  unfold dijkstra_first_step_math_state, Dijkstra.first_step_invariant.
  split.
  - intros v; rewrite dijkstra_array_state_visited_iff.
    unfold source_visited_set; sets_unfold.
    split.
    + intros (_ & Heq). symmetry. exact Heq.
    + intros Heq; subst v; split; [exact Hsrc | reflexivity].
  - split.
    + rewrite dijkstra_array_state_dist_valid by exact Hsrc.
      rewrite Hcell by exact Hsrc_bounds.
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
             (graph_has_size_vertex_valid_bounds
               g vertex_count v Hsize Hvalid) as (_ & Hv_bounds).
           rewrite Hcell by exact Hv_bounds.
           destruct (Z.eq_dec v src) as [Heq | _].
           ++ contradiction.
           ++ unfold cell_as_distance, DijkstraGraph.cell_as_distance.
              destruct (Z.eq_dec DijkstraGraph.infinity
                DijkstraGraph.infinity) as [_ | Hcontra];
                [reflexivity | contradiction Hcontra; reflexivity].
        -- apply dijkstra_array_state_dist_invalid; exact Hinvalid.
Qed.

Lemma index_queue_pop_result_singleton_source_early :
  forall src queue_set_after cur_vertex cur_distance,
    index_queue_pop_result
      (singleton_source_queue src) queue_set_after cur_vertex cur_distance ->
    queue_set_after = list_to_multiset (@nil (Z * Z)) /\
    cur_vertex = src /\
    cur_distance = 0.
Proof.
  intros src queue_set_after cur_vertex cur_distance Hpop.
  unfold index_queue_pop_result in Hpop.
  destruct Hpop as (popped & Hpopped & Hminimum & Hafter).
  destruct Hminimum as (Hin & _).
  unfold singleton_source_queue, multiset_insert, list_to_multiset
    in Hin, Hafter.
  simpl in Hin, Hafter.
  destruct Hin as [Hin | Hin]; [| contradiction].
  rewrite <- Hin in Hpopped.
  unfold heap_item in Hpopped.
  inversion Hpopped; subst cur_distance cur_vertex.
  subst queue_set_after.
  unfold multiset_remove, list_to_multiset.
  simpl.
  rewrite <- Hin.
  unfold heap_item.
  destruct (excluded_middle_informative ((0, src) = (0, src)))
    as [_ | Hneq].
  - repeat split; reflexivity.
  - contradiction Hneq; reflexivity.
Qed.

Definition dijkstra_heap_lfs_after_pop_cont
    (head_values to_values weight_values next_values : list Z)
    (queue_set_after : multiset (Z * Z))
    (cur_vertex cur_distance : Z) : program state unit :=
  step_result <-
    choice
      (assume (fun s =>
         cur_distance = state_distance_cell cur_vertex s);;
       update' (set_state_visited cur_vertex);;
       queue_set_after_edges <-
         dijkstra_heap_lfs_edge_loop
           head_values to_values weight_values next_values
           cur_vertex cur_distance
           (Znth cur_vertex head_values 0)
           queue_set_after;;
       ret (by_continue queue_set_after_edges))
      (assume (fun s =>
         cur_distance <> state_distance_cell cur_vertex s);;
       ret (by_continue queue_set_after));;
  match step_result with
  | by_continue queue_set_next =>
      dijkstra_heap_lfs_loop
        head_values to_values weight_values next_values
        queue_set_next
  | by_break done => ret done
  end.

Definition dijkstra_heap_loop_refines
    (g : DijkstraGraph.G) (src : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (queue_set : multiset (Z * Z)) (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (dijkstra_heap_lfs_loop head_values to_values weight_values next_values
      queue_set)
    X /\
  heap_queue_loop_capacity_state g visited_set queue_set /\
  heap_queue_refines_unvisited_dist g visited_set dist_values queue_set /\
  dijkstra_heap_loop_phase_state g src visited_set dist_values queue_set.

Definition dijkstra_heap_after_pop_refines
    (g : DijkstraGraph.G) (src : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (queue_set_after : multiset (Z * Z)) (cur_vertex cur_distance : Z)
    (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (dijkstra_heap_lfs_after_pop_cont head_values to_values weight_values
      next_values queue_set_after cur_vertex cur_distance)
    X /\
  heap_queue_loop_capacity_state g visited_set queue_set_after /\
  exists queue_set_before,
    dijkstra_heap_loop_state g src visited_set dist_values queue_set_before /\
    heap_queue_refines_unvisited_dist
      g visited_set dist_values queue_set_before /\
    index_queue_pop_result
      queue_set_before queue_set_after cur_vertex cur_distance /\
    dijkstra_heap_loop_phase_state
      g src visited_set dist_values queue_set_before.

Definition dijkstra_heap_edge_loop_refines
    (g : DijkstraGraph.G) (src cur_vertex cur_distance edge : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (queue_set : multiset (Z * Z)) (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (dijkstra_heap_lfs_edge_loop_cont head_values to_values weight_values
      next_values cur_vertex cur_distance edge queue_set)
    X /\
  heap_queue_edge_capacity_state
    g visited_set cur_vertex edge head_values to_values next_values
    queue_set /\
  heap_queue_refines_unvisited_dist g visited_set dist_values queue_set /\
  dijkstra_heap_edge_phase_state
    g src cur_vertex cur_distance edge
    head_values to_values weight_values next_values
    visited_set dist_values queue_set.

Definition dijkstra_heap_lfs_initial_refines
    (g : DijkstraGraph.G) (src : Z)
    (head_values to_values weight_values next_values : list Z)
    (X : unit -> state -> Prop) : Prop :=
  safeExec (eq (initial_state src))
    (dijkstra_heap_lfs_program
      src head_values to_values weight_values next_values)
    X /\
  shortest_path_relaxation_bounded g src DijkstraGraph.infinity.

Definition dijkstra_heap_after_relax_refines
    (g : DijkstraGraph.G) (src cur_vertex cur_distance edge
       neighbor candidate : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (queue_set : multiset (Z * Z)) (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (queue_set_after <-
       index_queue_push_choice queue_set neighbor candidate;;
     dijkstra_heap_lfs_edge_loop_cont head_values to_values weight_values
       next_values cur_vertex cur_distance
       (Znth edge next_values 0) queue_set_after)
    X /\
  heap_queue_edge_capacity_state
    g visited_set cur_vertex edge head_values to_values next_values
    queue_set /\
  forall queue_set_after,
    index_queue_push_result queue_set queue_set_after neighbor candidate ->
    heap_queue_refines_unvisited_dist
      g visited_set dist_values queue_set_after /\
    dijkstra_heap_edge_phase_state
      g src cur_vertex cur_distance (Znth edge next_values 0)
      head_values to_values weight_values next_values
      visited_set dist_values queue_set_after.

Lemma queue_set_empty_nil :
  forall (queue_set : multiset (Z * Z)),
    multiset_size queue_set = 0 ->
    mlist queue_set = nil.
Proof.
  intros [items] Hsize.
  unfold multiset_size in Hsize; simpl in Hsize.
  destruct items as [| item items_tail]; [reflexivity |].
  rewrite Zlength_cons in Hsize.
  pose proof (Zlength_nonneg items_tail).
  lia.
Qed.

Lemma multiset_remove_in_inv :
  forall (S : multiset (Z * Z)) item x,
    In x (mlist (multiset_remove S item)) ->
    In x (mlist S).
Proof.
  intros S item x Hx.
  destruct (classic (In item (mlist S))) as [Hin | Hnotin].
  - destruct (proj1 (multiset_remove_spec S item) Hin) as (_ & Hperm).
    apply (Permutation_in _ (Permutation_sym Hperm)).
    simpl; auto.
  - rewrite (proj2 (multiset_remove_spec S item) Hnotin) in Hx.
    exact Hx.
Qed.

Lemma multiset_size_insert :
  forall (S : multiset (Z * Z)) item,
    multiset_size (multiset_insert S item) =
    multiset_size S + 1.
Proof.
  intros S item.
  unfold multiset_size, multiset_insert, list_to_multiset.
  simpl.
  rewrite Zlength_cons.
  lia.
Qed.

Lemma multiset_insert_in_inv :
  forall (S : multiset (Z * Z)) item item0,
    In item0 (mlist (multiset_insert S item)) ->
    item0 = item \/ In item0 (mlist S).
Proof.
  intros S item item0 Hin.
  unfold multiset_insert, list_to_multiset in Hin; simpl in Hin.
  destruct Hin as [Heq | Hin].
  - left. symmetry. exact Heq.
  - right. exact Hin.
Qed.

Lemma multiset_insert_in_old :
  forall (S : multiset (Z * Z)) item item0,
    In item0 (mlist S) ->
    In item0 (mlist (multiset_insert S item)).
Proof.
  intros S item item0 Hin.
  unfold multiset_insert, list_to_multiset; simpl; auto.
Qed.

Lemma multiset_insert_in_new :
  forall (S : multiset (Z * Z)) item,
    In item (mlist (multiset_insert S item)).
Proof.
  intros S item.
  unfold multiset_insert, list_to_multiset; simpl; auto.
Qed.

Lemma multiset_insert_nodup :
  forall (S : multiset (Z * Z)) item,
    NoDup (mlist S) ->
    ~ In item (mlist S) ->
    NoDup (mlist (multiset_insert S item)).
Proof.
  intros S item Hnodup Hnotin.
  unfold multiset_insert, list_to_multiset; simpl.
  constructor; auto.
Qed.

Lemma multiset_size_remove_le :
  forall (S : multiset (Z * Z)) item,
    multiset_size (multiset_remove S item) <= multiset_size S.
Proof.
  intros S item.
  destruct (classic (In item (mlist S))) as [Hin | Hnotin].
  - destruct (proj1 (multiset_remove_spec S item) Hin) as (Hsize & _).
    rewrite Hsize.
    lia.
  - rewrite (proj2 (multiset_remove_spec S item) Hnotin).
    lia.
Qed.

Lemma multiset_size_remove_minimum :
  forall (S : multiset (Z * Z)) item,
    multiset_minimum S item ->
    multiset_size (multiset_remove S item) =
    multiset_size S - 1.
Proof.
  intros S item Hmin.
  unfold multiset_minimum in Hmin.
  destruct Hmin as (Hin & _).
  destruct (proj1 (multiset_remove_spec S item) Hin) as (Hsize & _).
  exact Hsize.
Qed.

Lemma multiset_remove_in_old_neq :
  forall (S : multiset (Z * Z)) item item0,
    In item0 (mlist S) ->
    item0 <> item ->
    In item0 (mlist (multiset_remove S item)).
Proof.
  intros S item item0 Hin Hneq.
  destruct (classic (In item (mlist S))) as [Hitem | Hnotin].
  - destruct (proj1 (multiset_remove_spec S item) Hitem)
      as (_ & Hperm).
    pose proof (Permutation_in _ Hperm Hin) as Hin_cons.
    simpl in Hin_cons.
    destruct Hin_cons as [Heq | Hin_remove].
    + contradiction Hneq. symmetry. exact Heq.
    + exact Hin_remove.
  - rewrite (proj2 (multiset_remove_spec S item) Hnotin).
    exact Hin.
Qed.

Lemma multiset_remove_nodup :
  forall (S : multiset (Z * Z)) item,
    NoDup (mlist S) ->
    NoDup (mlist (multiset_remove S item)).
Proof.
  intros S item Hnodup.
  destruct (classic (In item (mlist S))) as [Hitem | Hnotin].
  - destruct (proj1 (multiset_remove_spec S item) Hitem)
      as (_ & Hperm).
    apply Permutation_NoDup in Hperm; [| exact Hnodup].
    inversion Hperm; auto.
  - rewrite (proj2 (multiset_remove_spec S item) Hnotin).
    exact Hnodup.
Qed.

Lemma multiset_remove_not_in_removed_nodup :
  forall (S : multiset (Z * Z)) item,
    NoDup (mlist S) ->
    In item (mlist S) ->
    ~ In item (mlist (multiset_remove S item)).
Proof.
  intros S item Hnodup Hin Hremain.
  destruct (proj1 (multiset_remove_spec S item) Hin)
    as (_ & Hperm).
  apply Permutation_NoDup in Hperm; [| exact Hnodup].
  inversion Hperm as [| ? ? Hnotin_tail _]; subst.
  apply Hnotin_tail. exact Hremain.
Qed.

Lemma heap_queue_capacity_empty :
  forall edge_count,
    0 <= edge_count ->
    heap_queue_capacity edge_count (list_to_multiset (@nil (Z * Z))).
Proof.
  intros edge_count Hedge_nonneg.
  unfold heap_queue_capacity, multiset_size, list_to_multiset.
  simpl.
  rewrite Zlength_nil.
  lia.
Qed.

Lemma heap_queue_capacity_push :
  forall edge_count queue_set queue_set_after vertex distance,
    heap_queue_has_push_room edge_count queue_set ->
    index_queue_push_result queue_set queue_set_after vertex distance ->
    heap_queue_capacity edge_count queue_set_after.
Proof.
  intros edge_count queue_set queue_set_after vertex distance Hroom Hpush.
  unfold index_queue_push_result in Hpush.
  subst queue_set_after.
  unfold heap_queue_capacity, heap_queue_has_push_room in *.
  rewrite multiset_size_insert.
  lia.
Qed.

Lemma heap_queue_capacity_pop :
  forall edge_count queue_set_before queue_set_after vertex distance,
    heap_queue_capacity edge_count queue_set_before ->
    index_queue_pop_result queue_set_before queue_set_after vertex distance ->
    heap_queue_capacity edge_count queue_set_after.
Proof.
  intros edge_count queue_set_before queue_set_after vertex distance
    Hcapacity Hpop.
  unfold index_queue_pop_result in Hpop.
  destruct Hpop as (popped & _ & Hmin & Hafter).
  subst queue_set_after.
  unfold heap_queue_capacity in *.
  rewrite (multiset_size_remove_minimum queue_set_before popped Hmin).
  lia.
Qed.

Lemma heap_queue_room_to_size_bounds :
  forall edge_count queue_set queue_size,
    heap_queue_has_push_room edge_count queue_set ->
    multiset_size queue_set = queue_size ->
    0 <= edge_count ->
    edge_count + 1 <= heap_capacity ->
    queue_size < heap_capacity.
Proof.
  unfold heap_queue_has_push_room.
  intros edge_count queue_set queue_size Hroom Hsize
    Hedge_nonneg Hcapacity.
  lia.
Qed.

Lemma edge_index_in_seqZ :
  forall edge_count edge,
    0 <= edge_count ->
    edge_index edge_count edge ->
    In edge (map Z.of_nat (seq 0 (Z.to_nat edge_count))).
Proof.
  intros edge_count edge Hedge_count Hedge.
  unfold edge_index in Hedge.
  apply in_map_iff.
  exists (Z.to_nat edge).
  split.
  - apply Z2Nat.id; lia.
  - apply in_seq.
    split; [lia |].
    apply Z2Nat.inj_lt; lia.
Qed.

Lemma NoDup_Zlength_edge_index_bound :
  forall edge_count edges,
    0 <= edge_count ->
    NoDup edges ->
    Forall (edge_index edge_count) edges ->
    Zlength edges <= edge_count.
Proof.
  intros edge_count edges Hedge_count Hnodup Hrange.
  pose (all_edges := map Z.of_nat (seq 0 (Z.to_nat edge_count))).
  assert (Hincl : incl edges all_edges).
  {
    intros edge Hin.
    eapply edge_index_in_seqZ; eauto.
    apply Forall_forall with (x := edge) in Hrange; auto.
  }
  pose proof (NoDup_incl_length Hnodup Hincl) as Hlen.
  unfold all_edges in Hlen.
  rewrite length_map, length_seq in Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite !Zlength_correct.
  rewrite Z2Nat.id in Hlen by lia.
  exact Hlen.
Qed.

Lemma processed_edge_budget_empty :
  forall edge_count,
    0 <= edge_count ->
    processed_edge_budget edge_count nil
      (list_to_multiset (@nil (Z * Z))).
Proof.
  intros edge_count Hedge_count.
  unfold processed_edge_budget, multiset_size, list_to_multiset.
  simpl.
  rewrite !Zlength_nil.
  repeat split; try constructor; lia.
Qed.

Lemma processed_edge_budget_pop :
  forall edge_count processed_edges queue_set_before queue_set_after
         vertex distance,
    processed_edge_budget edge_count processed_edges queue_set_before ->
    index_queue_pop_result queue_set_before queue_set_after vertex distance ->
    processed_edge_budget edge_count processed_edges queue_set_after.
Proof.
  intros edge_count processed_edges queue_set_before queue_set_after
    vertex distance Hbudget Hpop.
  unfold processed_edge_budget in *.
  destruct Hbudget as (Hedge_count & Hnodup & Hrange & Hsize).
  repeat split; auto.
  unfold index_queue_pop_result in Hpop.
  destruct Hpop as (popped & _ & Hmin & Hafter).
  subst queue_set_after.
  rewrite (multiset_size_remove_minimum queue_set_before popped Hmin).
  lia.
Qed.

Lemma processed_edge_budget_mark_no_push :
  forall edge_count processed_edges queue_set edge,
    processed_edge_budget edge_count processed_edges queue_set ->
    edge_index edge_count edge ->
    ~ In edge processed_edges ->
    processed_edge_budget edge_count (edge :: processed_edges) queue_set.
Proof.
  intros edge_count processed_edges queue_set edge Hbudget Hedge Hnotin.
  unfold processed_edge_budget in *.
  destruct Hbudget as (Hedge_count & Hnodup & Hrange & Hsize).
  split; [exact Hedge_count |].
  split; [constructor; auto |].
  split; [constructor; auto |].
  rewrite Zlength_cons. lia.
Qed.

Lemma processed_edge_budget_mark_push :
  forall edge_count processed_edges queue_set queue_set_after edge
         vertex distance,
    processed_edge_budget edge_count processed_edges queue_set ->
    edge_index edge_count edge ->
    ~ In edge processed_edges ->
    index_queue_push_result queue_set queue_set_after vertex distance ->
    processed_edge_budget edge_count (edge :: processed_edges) queue_set_after.
Proof.
  intros edge_count processed_edges queue_set queue_set_after edge
    vertex distance Hbudget Hedge Hnotin Hpush.
  unfold processed_edge_budget in *.
  destruct Hbudget as (Hedge_count & Hnodup & Hrange & Hsize).
  unfold index_queue_push_result in Hpush.
  subst queue_set_after.
  split; [exact Hedge_count |].
  split; [constructor; auto |].
  split; [constructor; auto |].
  rewrite multiset_size_insert, Zlength_cons.
  lia.
Qed.

Lemma processed_edge_budget_has_push_room :
  forall edge_count processed_edges queue_set edge,
    processed_edge_budget edge_count processed_edges queue_set ->
    edge_index edge_count edge ->
    ~ In edge processed_edges ->
    heap_queue_has_push_room edge_count queue_set.
Proof.
  intros edge_count processed_edges queue_set edge Hbudget Hedge Hnotin.
  unfold processed_edge_budget in Hbudget.
  destruct Hbudget as (Hedge_count & Hnodup & Hrange & Hsize).
  assert (Hbound :
    Zlength (edge :: processed_edges) <= edge_count).
  {
    apply NoDup_Zlength_edge_index_bound.
    - exact Hedge_count.
    - constructor; auto.
    - constructor; auto.
  }
  unfold heap_queue_has_push_room.
  rewrite Zlength_cons in Hbound.
  lia.
Qed.

Lemma forward_star_suffix_fresh_current :
  forall next_values edge processed_edges,
    0 <= edge < Zlength next_values ->
    forward_star_suffix_fresh next_values edge processed_edges ->
    ~ In edge processed_edges.
Proof.
  intros next_values edge processed_edges Hedge Hfresh.
  apply Hfresh.
  constructor; exact Hedge.
Qed.

Lemma forward_star_suffix_fresh_step :
  forall head_values to_values next_values edge processed_edges,
    forward_star_chain_wf head_values to_values next_values ->
    0 <= edge < Zlength next_values ->
    forward_star_suffix_fresh next_values edge processed_edges ->
    forward_star_suffix_fresh next_values
      (Znth edge next_values 0) (edge :: processed_edges).
Proof.
  intros head_values to_values next_values edge processed_edges
    Hchain_wf Hedge_bounds Hfresh idx Hidx.
  pose proof Hchain_wf as (Hno_cycle & _).
  rewrite (Znth_indep next_values edge 0 (-1)) in Hidx by lia.
  intros [Hidx_edge | Hidx_old].
  - subst idx.
    destruct (Z.eq_dec (Znth edge next_values (-1)) (-1))
      as [Hnext_nil | Hnext_not_nil].
    + rewrite Hnext_nil in Hidx.
      eapply next_chain_minus_one_false; eauto.
    + eapply (Hno_cycle edge Hedge_bounds Hnext_not_nil).
      exact Hidx.
  - exfalso.
    apply (Hfresh idx).
    destruct (Z.eq_dec (Znth edge next_values (-1)) (-1))
      as [Hnext_nil | Hnext_not_nil].
    + rewrite Hnext_nil in Hidx.
      exfalso; eapply next_chain_minus_one_false; eauto.
    + eapply next_chain_next.
      * exact Hedge_bounds.
      * exact Hnext_not_nil.
      * exact Hidx.
    + exact Hidx_old.
Qed.

Lemma forward_star_unvisited_fresh_after_visit :
  forall head_values next_values visited_before visited_after
         processed_edges cur_vertex,
    forward_star_unvisited_fresh
      head_values next_values visited_before processed_edges ->
    visited_set_add visited_before cur_vertex visited_after ->
    forward_star_unvisited_fresh
      head_values next_values visited_after processed_edges.
Proof.
  intros head_values next_values visited_before visited_after
    processed_edges cur_vertex Hfresh Hvisit u idx Hu Hunvisited Hchain.
  apply (Hfresh u idx Hu).
  - intro Hu_before.
    apply Hunvisited.
    unfold visited_set_add in Hvisit.
    rewrite Hvisit.
    left; exact Hu_before.
  - exact Hchain.
Qed.

Lemma forward_star_unvisited_fresh_mark_current :
  forall head_values next_values visited_set processed_edges cur_vertex edge,
    forward_star_chains_disjoint head_values next_values ->
    forward_star_unvisited_fresh
      head_values next_values visited_set processed_edges ->
    visited_set cur_vertex ->
    storage_index cur_vertex ->
    next_chain next_values (Znth cur_vertex head_values (-1)) edge ->
    forward_star_unvisited_fresh
      head_values next_values visited_set (edge :: processed_edges).
Proof.
  intros head_values next_values visited_set processed_edges cur_vertex edge
    Hdisjoint Hfresh Hcur_visited Hcur_storage Hcur_chain
    u idx Hu_storage Hu_unvisited Hu_chain.
  intros [Hidx_edge | Hidx_old].
  - subst idx.
    assert (u = cur_vertex)
      by (eapply Hdisjoint; eauto).
    subst u.
    contradiction.
  - apply (Hfresh u idx Hu_storage Hu_unvisited Hu_chain).
    exact Hidx_old.
Qed.

Lemma vertex_pair_code_injective :
  forall g p q,
    DijkstraGraph.graph_wf g ->
    vertex_pair_valid g p ->
    vertex_pair_valid g q ->
    vertex_pair_code p = vertex_pair_code q ->
    p = q.
Proof.
  intros g [u1 v1] [u2 v2] Hwf Hvalid1 Hvalid2 Hcode.
  unfold vertex_pair_valid, vertex_valid, DijkstraGraph.vertex_valid in *.
  unfold vertex_pair_code, DijkstraGraph.max_vertices in Hcode.
  simpl in *.
  destruct Hwf as (Hcount & _).
  destruct Hvalid1 as (Hu1 & Hv1).
  destruct Hvalid2 as (Hu2 & Hv2).
  unfold DijkstraGraph.max_vertices in *.
  assert (u1 = u2) by lia.
  assert (v1 = v2) by lia.
  subst; reflexivity.
Qed.

Lemma NoDup_map_vertex_pair_code :
  forall g processed_pairs,
    DijkstraGraph.graph_wf g ->
    NoDup processed_pairs ->
    Forall (vertex_pair_valid g) processed_pairs ->
    NoDup (map vertex_pair_code processed_pairs).
Proof.
  intros g processed_pairs Hwf Hnodup Hvalids.
  induction processed_pairs as [|p ps IH]; simpl; constructor.
  - inversion Hnodup as [|? ? Hnotin _]; subst.
    inversion Hvalids as [|? ? Hp Hps]; subst.
    intro Hin.
    apply in_map_iff in Hin as (q & Hcode & Hq).
    assert (Hqvalid : vertex_pair_valid g q).
    {
      apply Forall_forall with (x := q) in Hps; auto.
    }
    apply Hnotin.
    replace p with q; auto.
    eapply vertex_pair_code_injective; eauto.
  - inversion Hnodup; subst.
    inversion Hvalids; subst.
    apply IH; assumption.
Qed.

Lemma vertex_pair_code_range :
  forall g pair,
    DijkstraGraph.graph_wf g ->
    vertex_pair_valid g pair ->
    edge_index (DijkstraGraph.max_vertices * DijkstraGraph.max_vertices)
      (vertex_pair_code pair).
Proof.
  intros g [u v] Hwf Hvalid.
  unfold edge_index, vertex_pair_valid, vertex_valid,
    DijkstraGraph.vertex_valid, vertex_pair_code,
    DijkstraGraph.max_vertices in *.
  simpl in *.
  destruct Hwf as (Hcount & _).
  destruct Hvalid as (Hu & Hv).
  unfold vertex_valid, DijkstraGraph.vertex_valid in Hu, Hv.
  unfold DijkstraGraph.max_vertices in Hcount.
  assert (Hu10 : 0 <= u < 10) by lia.
  assert (Hv10 : 0 <= v < 10) by lia.
  split.
  - apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg |]; lia.
  - replace (u * 10 + v) with (10 * u + v) by lia.
    lia.
Qed.

Lemma NoDup_Zlength_vertex_pair_bound :
  forall g processed_pairs,
    DijkstraGraph.graph_wf g ->
    NoDup processed_pairs ->
    Forall (vertex_pair_valid g) processed_pairs ->
    Zlength processed_pairs <=
      DijkstraGraph.max_vertices * DijkstraGraph.max_vertices.
Proof.
  intros g processed_pairs Hwf Hnodup Hvalids.
  pose proof
    (NoDup_map_vertex_pair_code g processed_pairs Hwf Hnodup Hvalids)
    as Hnodup_codes.
  assert (Hrange :
    Forall
      (edge_index (DijkstraGraph.max_vertices * DijkstraGraph.max_vertices))
      (map vertex_pair_code processed_pairs)).
  {
    apply Forall_forall.
    intros code Hin.
    apply in_map_iff in Hin as (pair & Hcode & Hpair).
    subst code.
    eapply (vertex_pair_code_range g pair); eauto.
    apply Forall_forall with (x := pair) in Hvalids; auto.
  }
  pose proof
    (NoDup_Zlength_edge_index_bound
      (DijkstraGraph.max_vertices * DijkstraGraph.max_vertices)
      (map vertex_pair_code processed_pairs)
      ltac:(unfold DijkstraGraph.max_vertices; lia)
      Hnodup_codes Hrange) as Hbound.
  rewrite !Zlength_correct in *.
  rewrite length_map in Hbound.
  exact Hbound.
Qed.

Lemma processed_vertex_pair_budget_singleton_source :
  forall g src,
    processed_vertex_pair_budget g nil (singleton_source_queue src).
Proof.
  intros g src.
  unfold processed_vertex_pair_budget, singleton_source_queue,
    multiset_size, multiset_insert, list_to_multiset.
  simpl.
  split; [constructor |].
  split; [apply Forall_nil |].
  rewrite Zlength_cons, Zlength_nil; lia.
Qed.

Lemma processed_vertex_pair_budget_pop :
  forall g processed_pairs queue_set_before queue_set_after vertex distance,
    processed_vertex_pair_budget g processed_pairs queue_set_before ->
    index_queue_pop_result queue_set_before queue_set_after vertex distance ->
    processed_vertex_pair_budget g processed_pairs queue_set_after.
Proof.
  intros g processed_pairs queue_set_before queue_set_after
    vertex distance Hbudget Hpop.
  unfold processed_vertex_pair_budget in *.
  destruct Hbudget as (Hnodup & Hvalids & Hsize).
  repeat split; auto.
  unfold index_queue_pop_result in Hpop.
  destruct Hpop as (popped & _ & Hmin & Hafter).
  subst queue_set_after.
  rewrite (multiset_size_remove_minimum queue_set_before popped Hmin).
  lia.
Qed.

Lemma processed_vertex_pair_budget_mark_no_push :
  forall g processed_pairs queue_set pair,
    processed_vertex_pair_budget g processed_pairs queue_set ->
    vertex_pair_valid g pair ->
    ~ In pair processed_pairs ->
    processed_vertex_pair_budget g (pair :: processed_pairs) queue_set.
Proof.
  intros g processed_pairs queue_set pair Hbudget Hvalid Hfresh.
  unfold processed_vertex_pair_budget in *.
  destruct Hbudget as (Hnodup & Hvalids & Hsize).
  repeat split.
  - constructor; auto.
  - constructor; auto.
  - rewrite Zlength_cons. lia.
Qed.

Lemma processed_vertex_pair_budget_mark_push :
  forall g processed_pairs queue_set queue_set_after pair vertex distance,
    processed_vertex_pair_budget g processed_pairs queue_set ->
    vertex_pair_valid g pair ->
    ~ In pair processed_pairs ->
    index_queue_push_result queue_set queue_set_after vertex distance ->
    processed_vertex_pair_budget
      g (pair :: processed_pairs) queue_set_after.
Proof.
  intros g processed_pairs queue_set queue_set_after pair vertex distance
    Hbudget Hvalid Hfresh Hpush.
  unfold index_queue_push_result in Hpush.
  subst queue_set_after.
  unfold processed_vertex_pair_budget in *.
  destruct Hbudget as (Hnodup & Hvalids & Hsize).
  repeat split.
  - constructor; auto.
  - constructor; auto.
  - rewrite multiset_size_insert, Zlength_cons. lia.
Qed.

Lemma processed_vertex_pair_budget_has_push_room :
  forall g processed_pairs queue_set pair,
    DijkstraGraph.graph_wf g ->
    processed_vertex_pair_budget g processed_pairs queue_set ->
    vertex_pair_valid g pair ->
    ~ In pair processed_pairs ->
    multiset_size queue_set <
      DijkstraGraph.max_vertices * DijkstraGraph.max_vertices + 1.
Proof.
  intros g processed_pairs queue_set pair Hwf Hbudget Hvalid Hfresh.
  unfold processed_vertex_pair_budget in Hbudget.
  destruct Hbudget as (Hnodup & Hvalids & Hsize).
  assert (Hnodup_cons : NoDup (pair :: processed_pairs))
    by (constructor; auto).
  assert (Hvalids_cons : Forall (vertex_pair_valid g) (pair :: processed_pairs))
    by (constructor; auto).
  pose proof
    (NoDup_Zlength_vertex_pair_bound g (pair :: processed_pairs)
      Hwf Hnodup_cons Hvalids_cons) as Hbound.
  rewrite Zlength_cons in Hbound.
  lia.
Qed.

Lemma heap_queue_loop_capacity_state_singleton_source :
  forall g visited_set src,
    visited_set_empty visited_set ->
    heap_queue_loop_capacity_state
      g visited_set (singleton_source_queue src).
Proof.
  intros g visited_set src Hempty.
  exists nil.
  split.
  - apply processed_vertex_pair_budget_singleton_source.
  - intros u v Hin. contradiction.
Qed.

Lemma heap_queue_loop_capacity_state_pop :
  forall g visited_set queue_set_before queue_set_after cur_vertex cur_distance,
    heap_queue_loop_capacity_state g visited_set queue_set_before ->
    index_queue_pop_result queue_set_before queue_set_after
      cur_vertex cur_distance ->
    heap_queue_loop_capacity_state g visited_set queue_set_after.
Proof.
  intros g visited_set queue_set_before queue_set_after
    cur_vertex cur_distance Hstate Hpop.
  destruct Hstate as (processed_pairs & Hbudget & Hfrom).
  exists processed_pairs.
  split; [eapply processed_vertex_pair_budget_pop; eauto | exact Hfrom].
Qed.

Lemma heap_queue_edge_capacity_state_start :
  forall g visited_before visited_after cur_vertex edge
         head_values to_values next_values queue_set,
    visited_set_add visited_before cur_vertex visited_after ->
    ~ visited_before cur_vertex ->
    edge = -1 \/
      next_chain next_values (Znth cur_vertex head_values (-1)) edge ->
    heap_queue_loop_capacity_state g visited_before queue_set ->
    heap_queue_edge_capacity_state
      g visited_after cur_vertex edge head_values to_values next_values
      queue_set.
Proof.
  intros g visited_before visited_after cur_vertex edge
    head_values to_values next_values queue_set Hvisit Hunvisited Hchain
    Hstate.
  destruct Hstate as (processed_pairs & Hbudget & Hfrom_before).
  split.
  - unfold visited_set_add in Hvisit.
    apply Hvisit; right; reflexivity.
  - split; [exact Hchain |].
    exists processed_pairs.
    split; [exact Hbudget |].
    split.
    + intros u v Hin.
      unfold visited_set_add in Hvisit.
      apply Hvisit; left.
      apply (Hfrom_before u v Hin).
    + intros idx _ Hin.
      apply Hunvisited.
      apply (Hfrom_before cur_vertex (Znth idx to_values 0) Hin).
Qed.

Lemma heap_queue_edge_capacity_state_to_loop :
  forall g visited_set cur_vertex edge head_values to_values next_values
         queue_set,
    heap_queue_edge_capacity_state
      g visited_set cur_vertex edge head_values to_values next_values
      queue_set ->
    heap_queue_loop_capacity_state g visited_set queue_set.
Proof.
  intros g visited_set cur_vertex edge head_values to_values next_values
    queue_set Hstate.
  destruct Hstate as (_ & _ & processed_pairs & Hbudget & Hfrom & _).
  exists processed_pairs.
  split; assumption.
Qed.

Lemma heap_queue_edge_capacity_state_has_push_room :
  forall g visited_set cur_vertex edge head_values to_values next_values
         queue_set neighbor,
    DijkstraGraph.graph_wf g ->
    vertex_valid g cur_vertex ->
    vertex_valid g neighbor ->
    neighbor = Znth edge to_values 0 ->
    0 <= edge < Zlength next_values ->
    heap_queue_edge_capacity_state
      g visited_set cur_vertex edge head_values to_values next_values
      queue_set ->
    multiset_size queue_set <
      DijkstraGraph.max_vertices * DijkstraGraph.max_vertices + 1.
Proof.
  intros g visited_set cur_vertex edge head_values to_values next_values
    queue_set neighbor Hwf Hcur_valid Hneighbor_valid Hneighbor Hedge
    Hstate.
  destruct Hstate as (_ & _ & processed_pairs & Hbudget & _ & Hfresh).
  eapply processed_vertex_pair_budget_has_push_room with
    (pair := (cur_vertex, neighbor)); eauto.
  - unfold vertex_pair_valid; simpl; auto.
  - subst neighbor.
    apply Hfresh.
    constructor; exact Hedge.
Qed.

Lemma heap_queue_edge_capacity_state_no_push_step :
  forall g visited_set cur_vertex edge head_values to_values next_values
         queue_set,
    edge <> -1 ->
    0 <= edge < Zlength next_values ->
    (Znth edge next_values 0 = -1 \/
      0 <= Znth edge next_values 0 < Zlength next_values) ->
    heap_queue_edge_capacity_state
      g visited_set cur_vertex edge head_values to_values next_values
      queue_set ->
    heap_queue_edge_capacity_state
      g visited_set cur_vertex (Znth edge next_values 0)
      head_values to_values next_values queue_set.
Proof.
  intros g visited_set cur_vertex edge head_values to_values next_values
    queue_set Hedge_not_nil Hedge_bounds Hnext_case Hstate.
  destruct Hstate as
    (Hvisited & Hloc & processed_pairs & Hbudget & Hfrom & Hfresh).
  split; [exact Hvisited |].
  split.
  - destruct Hloc as [Hedge_nil | Hhead_edge]; [contradiction |].
    destruct Hnext_case as [Hnext_nil | Hnext_bounds].
    + left; exact Hnext_nil.
    + right.
      eapply next_chain_trans; [exact Hhead_edge |].
      rewrite (Znth_indep next_values edge 0 (-1)) by lia.
      eapply next_chain_tail_to_head; eauto.
      * rewrite <- (Znth_indep next_values edge 0 (-1)) by lia.
        lia.
      * constructor.
        rewrite <- (Znth_indep next_values edge 0 (-1)) by lia.
        lia.
  - exists processed_pairs.
    split; [exact Hbudget |].
    split; [exact Hfrom |].
    intros idx Hidx Hin.
    apply (Hfresh idx).
    destruct Hnext_case as [Hnext_nil | Hnext_bounds].
    + rewrite Hnext_nil in Hidx.
      exfalso; eapply next_chain_minus_one_false; eauto.
    + rewrite (Znth_indep next_values edge 0 (-1)) in Hidx by lia.
      eapply next_chain_tail_to_head; eauto.
      rewrite <- (Znth_indep next_values edge 0 (-1)) by lia.
      lia.
    + exact Hin.
Qed.

Lemma heap_queue_edge_capacity_state_push_step :
  forall g visited_set cur_vertex edge head_values to_values next_values
         queue_set queue_set_after neighbor distance,
    forward_star_chain_wf head_values to_values next_values ->
    storage_index cur_vertex ->
    vertex_pair_valid g (cur_vertex, neighbor) ->
    neighbor = Znth edge to_values 0 ->
    edge <> -1 ->
    0 <= edge < Zlength next_values ->
    0 <= edge < Zlength to_values ->
    Zlength next_values = Zlength to_values ->
    (Znth edge next_values 0 = -1 \/
      0 <= Znth edge next_values 0 < Zlength next_values) ->
    index_queue_push_result queue_set queue_set_after neighbor distance ->
    heap_queue_edge_capacity_state
      g visited_set cur_vertex edge head_values to_values next_values
      queue_set ->
    heap_queue_edge_capacity_state
      g visited_set cur_vertex (Znth edge next_values 0)
      head_values to_values next_values queue_set_after.
Proof.
  intros g visited_set cur_vertex edge head_values to_values next_values
    queue_set queue_set_after neighbor distance Hchain_wf Hcur_storage
    Hpair_valid Hneighbor Hedge_not_nil Hedge_next_bounds Hedge_to_bounds
    Hlen_next_to Hnext_case Hpush Hstate.
  destruct Hstate as
    (Hvisited & Hloc & processed_pairs & Hbudget & Hfrom & Hfresh).
  destruct Hloc as [Hedge_nil | Hhead_edge]; [contradiction |].
  assert (Hpair_fresh : ~ In (cur_vertex, neighbor) processed_pairs).
  {
    subst neighbor.
    apply Hfresh.
    constructor; exact Hedge_next_bounds.
  }
  split; [exact Hvisited |].
  split.
  - destruct Hnext_case as [Hnext_nil | Hnext_bounds].
    + left; exact Hnext_nil.
    + right.
      eapply next_chain_trans; [exact Hhead_edge |].
      rewrite (Znth_indep next_values edge 0 (-1)) by lia.
      eapply next_chain_tail_to_head; eauto.
      * rewrite <- (Znth_indep next_values edge 0 (-1)) by lia.
        lia.
      * constructor.
        rewrite <- (Znth_indep next_values edge 0 (-1)) by lia.
        lia.
  - exists ((cur_vertex, neighbor) :: processed_pairs).
    split.
    + eapply processed_vertex_pair_budget_mark_push; eauto.
    + split.
      * intros u v Hin.
        destruct Hin as [Hin | Hin].
        -- inversion Hin; subst.
           exact Hvisited.
        -- exact (Hfrom u v Hin).
      * intros idx Hidx Hin.
        destruct Hnext_case as [Hnext_nil | Hnext_bounds].
        -- rewrite Hnext_nil in Hidx.
           exfalso; eapply next_chain_minus_one_false; eauto.
        -- rewrite (Znth_indep next_values edge 0 (-1)) in Hidx by lia.
           assert (Hedge_idx : next_chain next_values edge idx).
           {
             eapply next_chain_tail_to_head; eauto.
             rewrite <- (Znth_indep next_values edge 0 (-1)) by lia.
             lia.
           }
           destruct Hin as [Hnew | Hold].
           ++ inversion Hnew as [Hpair_eq].
              simpl in Hpair_eq.
              subst neighbor.
              destruct Hchain_wf as (Hno_cycle & Hno_dup & Hchain_bound).
              assert (Hhead_not_nil :
                Znth cur_vertex head_values (-1) <> -1).
              {
                intro Hnil.
                rewrite Hnil in Hhead_edge.
                eapply next_chain_minus_one_false; eauto.
              }
              assert (Hhead_idx :
                next_chain next_values (Znth cur_vertex head_values (-1)) idx)
                by (eapply next_chain_trans; eauto).
              assert (Hidx_next_bounds : 0 <= idx < Zlength next_values)
                by (eapply Hchain_bound; eauto).
              assert (Hidx_to_bounds : 0 <= idx < Zlength to_values)
                by lia.
              assert (idx = edge).
              {
                eapply Hno_dup; eauto.
              }
              subst idx.
              eapply (Hno_cycle edge Hedge_next_bounds).
              ** rewrite <- (Znth_indep next_values edge 0 (-1)) by lia.
                 lia.
              ** exact Hidx.
           ++ apply (Hfresh idx Hedge_idx Hold).
Qed.

Lemma heap_queue_refines_unvisited_dist_singleton_source :
  forall g vertex_count src visited_set dist_values,
    graph_has_size g vertex_count ->
    vertex_valid g src ->
    visited_set_empty visited_set ->
    dijkstra_init_dist vertex_count src dist_values ->
    heap_queue_refines_unvisited_dist
      g visited_set dist_values (singleton_source_queue src).
Proof.
  intros g vertex_count src visited_set dist_values
    Hsize Hsrc Hempty Hinit.
  unfold heap_queue_refines_unvisited_dist,
    priority_queue_refines_unvisited_dist,
    singleton_source_queue, multiset_insert, list_to_multiset.
  simpl.
  destruct Hinit as (_Hshape & _Hsafe & Hcount & Hsrc_bounds & Hcell).
  repeat split.
  - intros v Hvalid _ Hfinite.
    pose proof (graph_has_size_vertex_valid_bounds g vertex_count v Hsize Hvalid)
      as (_ & Hv_bounds).
    rewrite Hcell in Hfinite by exact Hv_bounds.
    destruct (Z.eq_dec v src) as [Heq | Hneq].
    + subst v.
      simpl; left.
      rewrite Hcell by exact Hsrc_bounds.
      destruct (Z.eq_dec src src); [reflexivity | contradiction].
    + unfold DijkstraGraph.infinity in Hfinite; lia.
  - intros d v Hin Hdist.
    destruct Hin as [Hin | []].
    inversion Hin; subst d v.
    apply Hempty.
  - intros d v Hin.
    destruct Hin as [Hin | []].
    inversion Hin; subst d v.
    rewrite Hcell by exact Hsrc_bounds.
    destruct (Z.eq_dec src src); [lia | contradiction].
  - intros d v Hin.
    destruct Hin as [Hin | []].
    inversion Hin; subst d v.
    unfold DijkstraGraph.infinity; lia.
  - constructor; [intro H; contradiction | constructor].
Qed.

Lemma heap_queue_refines_unvisited_dist_relax_push :
  forall g vertex_count visited_set dist_values queue_set queue_set_after
         neighbor candidate,
    graph_has_size g vertex_count ->
    vector_shape dist_values ->
    storage_index neighbor ->
    ~ visited_set neighbor ->
    candidate < dist_cell dist_values neighbor ->
    candidate < DijkstraGraph.infinity ->
    heap_queue_items_valid g queue_set ->
    heap_queue_refines_unvisited_dist
      g visited_set dist_values queue_set ->
    index_queue_push_result queue_set queue_set_after neighbor candidate ->
    heap_queue_refines_unvisited_dist g visited_set
      (replace_Znth neighbor candidate dist_values) queue_set_after.
Proof.
  intros g vertex_count visited_set dist_values queue_set queue_set_after
    neighbor candidate Hsize Hshape Hneighbor_storage Hneighbor_unvisited
    Hstrict Hcandidate_finite Hitems_valid Hrefines Hpush.
  unfold index_queue_push_result in Hpush.
  subst queue_set_after.
  unfold heap_queue_refines_unvisited_dist in *.
  destruct Hrefines as
    (Hcovers & Hfresh & Hlower & Hitems_finite & Hnodup).
  split.
  - intros v Hvalid Hunvisited Hfinite.
    destruct (Z.eq_dec v neighbor) as [Heq | Hneq].
    + subst v.
      erewrite dist_cell_replace_Znth_same by eauto.
      apply multiset_insert_in_new.
    + pose proof
        (graph_has_size_vertex_valid_storage _ _ _ Hsize Hvalid)
        as Hv_storage.
      erewrite dist_cell_replace_Znth_diff in Hfinite |- * by eauto.
      apply multiset_insert_in_old.
      apply Hcovers; auto.
  - split.
    + intros d v Hin Hdist_new.
      destruct (multiset_insert_in_inv _ _ _ Hin) as [Hnew | Hold].
      * inversion Hnew; subst d v; simpl in *.
        exact Hneighbor_unvisited.
      * destruct (Z.eq_dec v neighbor) as [Heq | Hneq].
        -- subst v.
           erewrite dist_cell_replace_Znth_same in Hdist_new by eauto.
           subst d.
           pose proof (Hlower candidate neighbor Hold) as Hlower_old.
           lia.
        -- destruct (Hitems_valid (d, v) Hold) as (Hv_valid & _).
           pose proof
             (graph_has_size_vertex_valid_storage _ _ _ Hsize Hv_valid)
             as Hv_storage.
           erewrite dist_cell_replace_Znth_diff in Hdist_new by eauto.
           apply (Hfresh d v); auto.
    + split.
      * intros d v Hin.
        destruct (multiset_insert_in_inv _ _ _ Hin) as [Hnew | Hold].
        -- inversion Hnew; subst d v; simpl.
           erewrite dist_cell_replace_Znth_same by eauto.
           lia.
        -- destruct (Z.eq_dec v neighbor) as [Heq | Hneq].
           ++ subst v.
              erewrite dist_cell_replace_Znth_same by eauto.
              pose proof (Hlower d neighbor Hold) as Hlower_old.
              lia.
           ++ destruct (Hitems_valid (d, v) Hold) as (Hv_valid & _).
              pose proof
                (graph_has_size_vertex_valid_storage _ _ _ Hsize Hv_valid)
                as Hv_storage.
              erewrite dist_cell_replace_Znth_diff by eauto.
              apply Hlower. exact Hold.
      * split.
        -- intros d v Hin.
           destruct (multiset_insert_in_inv _ _ _ Hin) as [Hnew | Hold].
           ++ inversion Hnew; subst d v; simpl.
              exact Hcandidate_finite.
           ++ apply (Hitems_finite d v). exact Hold.
        -- apply multiset_insert_nodup; [exact Hnodup |].
           intro Hin.
           pose proof (Hlower candidate neighbor Hin) as Hlower_item.
           lia.
Qed.

Lemma dijkstra_heap_loop_state_pop :
  forall g src visited_set dist_values queue_set_before queue_set_after
         cur_vertex cur_distance,
    dijkstra_heap_loop_state g src visited_set dist_values queue_set_before ->
    index_queue_pop_result queue_set_before queue_set_after
      cur_vertex cur_distance ->
    dijkstra_heap_loop_state g src visited_set dist_values queue_set_after.
Proof.
  intros g src visited_set dist_values queue_set_before queue_set_after
    cur_vertex cur_distance Hstate Hpop.
  unfold index_queue_pop_result in Hpop.
  destruct Hpop as (popped & Hpopped & _Hmin & Hafter).
  subst queue_set_after.
  unfold dijkstra_heap_loop_state in *.
  destruct Hstate as (Hwf & Hsrc & Hnonneg & Hshape & Hsafe & Hvalid).
  do 5 (split; [assumption |]).
  unfold heap_queue_items_valid in *.
  intros item Hin.
  apply Hvalid.
  eapply multiset_remove_in_inv; eauto.
Qed.

Lemma dijkstra_heap_pop_result_bounds :
  forall g vertex_count src visited_set dist_values queue_set_before
         queue_set_after cur_vertex cur_distance,
    graph_has_size g vertex_count ->
    dijkstra_heap_loop_state g src visited_set dist_values queue_set_before ->
    index_queue_pop_result queue_set_before queue_set_after
      cur_vertex cur_distance ->
    storage_index cur_vertex /\
    0 <= cur_vertex < vertex_count /\
    0 <= cur_distance <= DijkstraGraph.infinity.
Proof.
  intros g vertex_count src visited_set dist_values queue_set_before
    queue_set_after cur_vertex cur_distance Hsize Hstate Hpop.
  unfold index_queue_pop_result in Hpop.
  destruct Hpop as (popped & Hpopped & Hmin & _).
  subst popped.
  destruct Hmin as (Hin & _).
  unfold dijkstra_heap_loop_state, heap_queue_items_valid in Hstate.
  destruct Hstate as (_ & _ & _ & _ & _ & Hvalid).
  specialize (Hvalid (heap_item cur_distance cur_vertex) Hin).
  unfold heap_item, item_key, item_data in Hvalid.
  simpl in Hvalid.
  destruct Hvalid as (Hvertex & Hdistance).
  pose proof
    (graph_has_size_vertex_valid_storage g vertex_count cur_vertex
      Hsize Hvertex) as Hstorage.
  pose proof
    (graph_has_size_vertex_valid_bounds g vertex_count cur_vertex
      Hsize Hvertex) as (_ & Hbounds).
  split; [exact Hstorage |].
  split; [exact Hbounds | exact Hdistance].
Qed.

Lemma dijkstra_heap_pop_selected_min :
  forall g vertex_count src visited_set dist_values queue_set_before
         queue_set_after cur_vertex cur_distance,
    graph_has_size g vertex_count ->
    dijkstra_heap_loop_state g src visited_set dist_values queue_set_before ->
    heap_queue_refines_unvisited_dist
      g visited_set dist_values queue_set_before ->
    index_queue_pop_result queue_set_before queue_set_after
      cur_vertex cur_distance ->
    cur_distance = dist_cell dist_values cur_vertex ->
    0 <= cur_distance < DijkstraGraph.infinity ->
    dijkstra_selected_min g visited_set dist_values cur_vertex.
Proof.
  intros g vertex_count src visited_set dist_values queue_set_before
    queue_set_after cur_vertex cur_distance Hsize Hloop Hrefines Hpop
    Hcur_dist Hcur_finite.
  unfold dijkstra_selected_min.
  pose proof
    (dijkstra_heap_pop_result_bounds
      g vertex_count src visited_set dist_values queue_set_before
      queue_set_after cur_vertex cur_distance Hsize Hloop Hpop)
    as (_ & _ & _).
  unfold index_queue_pop_result in Hpop.
  destruct Hpop as (popped & Hpopped & Hminimum & Hafter).
  subst popped.
  destruct Hminimum as (Hpopped_in & Hminimum).
  unfold heap_queue_refines_unvisited_dist in Hrefines.
  destruct Hrefines as (Hcovers & Hfresh & Hlower & _ & _).
  assert (Hshape : vector_shape dist_values)
    by (unfold dijkstra_heap_loop_state in Hloop; tauto).
  assert (Hsafe : dist_values_safe dist_values)
    by (unfold dijkstra_heap_loop_state in Hloop; tauto).
  assert (Hcur_valid : vertex_valid g cur_vertex).
  {
    unfold dijkstra_heap_loop_state, heap_queue_items_valid in Hloop.
    destruct Hloop as (_ & _ & _ & _ & _ & Hvalid).
    specialize (Hvalid (heap_item cur_distance cur_vertex) Hpopped_in).
    unfold heap_item, item_data in Hvalid; simpl in Hvalid.
    exact (proj1 Hvalid).
  }
  assert (Hcur_unvisited_set : ~ visited_set cur_vertex).
  {
    apply (Hfresh cur_distance cur_vertex).
    - exact Hpopped_in.
    - exact Hcur_dist.
  }
  split.
  - unfold Dijkstra.unvisited.
    simpl.
    intro Hvisited_state.
    apply Hcur_unvisited_set.
    exact (proj2 Hvisited_state).
  - intros v Hunvisited.
    unfold Dijkstra.unvisited in Hunvisited.
    simpl in Hunvisited.
    destruct (classic (vertex_valid g v)) as [Hvalid | Hnot_valid].
    + assert (~ visited_set v) as Hunvisited_set.
      {
        intro Hvisited_set.
        apply Hunvisited.
        split; assumption.
      }
      assert (cur_distance <= dist_cell dist_values v) as Hcell_le.
      {
        destruct (Z_lt_ge_dec (dist_cell dist_values v)
          DijkstraGraph.infinity) as [Hfinite_v | Hinf].
        - pose proof (Hcovers v Hvalid Hunvisited_set Hfinite_v) as Hin.
          specialize (Hminimum (dist_cell dist_values v, v) Hin).
          simpl in Hminimum.
          exact Hminimum.
        - pose proof
            (graph_has_size_vertex_valid_storage
              g vertex_count v Hsize Hvalid) as Hv_storage.
          pose proof (Hsafe v Hv_storage).
          lia.
      }
      rewrite dijkstra_array_state_dist_valid by exact Hcur_valid.
      rewrite <- Hcur_dist.
      destruct (@dist Z (dijkstra_array_state g visited_set
        dist_values) v) as [dv |] eqn:Hdist_v.
      * rewrite dijkstra_array_state_dist_valid in Hdist_v by exact Hvalid.
        unfold cell_as_distance, DijkstraGraph.cell_as_distance
          in Hdist_v.
        destruct (Z.eq_dec (dist_cell dist_values v)
          DijkstraGraph.infinity) as [Hinf | Hfinite].
        -- discriminate.
        -- inversion Hdist_v; subst dv.
           rewrite (cell_as_distance_finite cur_distance)
             by exact Hcur_finite.
           simpl. exact Hcell_le.
      * rewrite (cell_as_distance_finite cur_distance)
          by exact Hcur_finite.
        simpl. exact I.
    + rewrite dijkstra_array_state_dist_valid by exact Hcur_valid.
      rewrite <- Hcur_dist.
      rewrite dijkstra_array_state_dist_invalid by exact Hnot_valid.
      rewrite (cell_as_distance_finite cur_distance)
        by exact Hcur_finite.
      simpl. exact I.
Qed.

Lemma heap_queue_refines_unvisited_dist_pop_stale :
  forall g visited_set dist_values queue_set_before queue_set_after
         cur_vertex cur_distance,
    heap_queue_refines_unvisited_dist
      g visited_set dist_values queue_set_before ->
    index_queue_pop_result queue_set_before queue_set_after
      cur_vertex cur_distance ->
    cur_distance <> dist_cell dist_values cur_vertex ->
    heap_queue_refines_unvisited_dist
      g visited_set dist_values queue_set_after.
Proof.
  intros g visited_set dist_values queue_set_before queue_set_after
    cur_vertex cur_distance Hrefines Hpop Hstale.
  unfold index_queue_pop_result in Hpop.
  destruct Hpop as (popped & Hpopped & _ & Hafter).
  subst popped queue_set_after.
  unfold heap_queue_refines_unvisited_dist in *.
  destruct Hrefines as (Hcovers & Hfresh & Hlower & Hfinite & Hnodup).
  split.
  - intros v Hvalid Hunvisited Hfinite_v.
    pose proof (Hcovers v Hvalid Hunvisited Hfinite_v) as Hin.
    eapply multiset_remove_in_old_neq; [exact Hin |].
    intro Heq.
    unfold heap_item in Heq.
    inversion Heq; subst.
    apply Hstale. reflexivity.
  - split.
    + intros d v Hin Hdist.
      apply (Hfresh d v).
      * eapply multiset_remove_in_inv; eauto.
      * exact Hdist.
    + split.
      * intros d v Hin.
        apply Hlower.
        eapply multiset_remove_in_inv; eauto.
      * split.
        -- intros d v Hin.
           apply (Hfinite d v).
           eapply multiset_remove_in_inv; eauto.
        -- apply multiset_remove_nodup.
           exact Hnodup.
Qed.

Lemma heap_queue_refines_unvisited_dist_pop_visit :
  forall g visited_before visited_after dist_values queue_set_before
         queue_set_after cur_vertex cur_distance,
    vertex_valid g cur_vertex ->
    visited_set_add visited_before cur_vertex visited_after ->
    heap_queue_refines_unvisited_dist
      g visited_before dist_values queue_set_before ->
    index_queue_pop_result queue_set_before queue_set_after
      cur_vertex cur_distance ->
    cur_distance = dist_cell dist_values cur_vertex ->
    heap_queue_refines_unvisited_dist
      g visited_after dist_values queue_set_after.
Proof.
  intros g visited_before visited_after dist_values queue_set_before
    queue_set_after cur_vertex cur_distance Hcur_valid Hvisit_add
    Hrefines Hpop Hcur_dist.
  unfold index_queue_pop_result in Hpop.
  destruct Hpop as (popped & Hpopped & Hminimum & Hafter).
  subst popped queue_set_after.
  destruct Hminimum as (Hpopped_in & _).
  unfold heap_queue_refines_unvisited_dist in *.
  destruct Hrefines as (Hcovers & Hfresh & Hlower & Hfinite & Hnodup).
  split.
  - intros v Hvalid Hunvisited_after Hfinite_v.
    assert (~ visited_before v) as Hunvisited_before.
    {
      intro Hvisited_before.
      apply Hunvisited_after.
      unfold visited_set_add in Hvisit_add.
      apply Hvisit_add; left; exact Hvisited_before.
    }
    pose proof (Hcovers v Hvalid Hunvisited_before Hfinite_v) as Hin.
    eapply multiset_remove_in_old_neq; [exact Hin |].
    intro Heq.
    unfold heap_item in Heq.
    inversion Heq; subst v.
    apply Hunvisited_after.
    unfold visited_set_add in Hvisit_add.
    apply Hvisit_add; right; reflexivity.
  - split.
    + intros d v Hin Hdist.
      assert (Hin_before : In (d, v) (mlist queue_set_before))
        by (eapply multiset_remove_in_inv; eauto).
      assert (~ visited_before v) as Hunvisited_before
        by (eapply Hfresh; eauto).
      intro Hvisited_after.
      unfold visited_set_add in Hvisit_add.
      apply Hvisit_add in Hvisited_after.
      destruct Hvisited_after as [Hvisited_before | Heq].
      * apply Hunvisited_before. exact Hvisited_before.
      * subst v.
        apply (multiset_remove_not_in_removed_nodup
          queue_set_before (heap_item cur_distance cur_vertex)
          Hnodup Hpopped_in).
        unfold heap_item.
        rewrite <- Hcur_dist in Hdist.
        subst d.
        exact Hin.
    + split.
      * intros d v Hin.
        apply Hlower.
        eapply multiset_remove_in_inv; eauto.
      * split.
        -- intros d v Hin.
           apply (Hfinite d v).
           eapply multiset_remove_in_inv; eauto.
        -- apply multiset_remove_nodup.
           exact Hnodup.
Qed.

Lemma dijkstra_heap_loop_bridge_state_pop_result :
  forall g src visited_set dist_values queue_set_before queue_set_after
         cur_vertex cur_distance,
    dijkstra_heap_loop_bridge_state
      g src visited_set dist_values queue_set_before ->
    index_queue_pop_result queue_set_before queue_set_after
      cur_vertex cur_distance ->
    dijkstra_heap_after_pop_bridge_state
      g src visited_set dist_values queue_set_before queue_set_after
      cur_vertex cur_distance.
Proof.
  intros g src visited_set dist_values queue_set_before queue_set_after
    cur_vertex cur_distance Hbridge Hpop.
  unfold dijkstra_heap_loop_bridge_state in Hbridge.
  destruct Hbridge as (Hloop & Hrefines).
  unfold dijkstra_heap_after_pop_bridge_state.
  split.
  - eapply dijkstra_heap_loop_state_pop; eauto.
  - split; assumption.
Qed.

Lemma dijkstra_heap_after_pop_bridge_state_stale_to_loop_bridge :
  forall g src visited_set dist_values queue_set_before queue_set_after
         cur_vertex cur_distance,
    dijkstra_heap_after_pop_bridge_state
      g src visited_set dist_values queue_set_before queue_set_after
      cur_vertex cur_distance ->
    cur_distance <> dist_cell dist_values cur_vertex ->
    dijkstra_heap_loop_bridge_state
      g src visited_set dist_values queue_set_after.
Proof.
  intros g src visited_set dist_values queue_set_before queue_set_after
    cur_vertex cur_distance Hbridge Hstale.
  unfold dijkstra_heap_after_pop_bridge_state in Hbridge.
  destruct Hbridge as (Hloop_after & Hrefines_before & Hpop).
  unfold dijkstra_heap_loop_bridge_state.
  split; [exact Hloop_after |].
  eapply heap_queue_refines_unvisited_dist_pop_stale; eauto.
Qed.

Lemma dijkstra_heap_after_pop_bridge_state_equal_to_edge_bridge :
  forall g src visited_before visited_after dist_values queue_set_before
         queue_set_after cur_vertex cur_distance edge,
    vertex_valid g cur_vertex ->
    visited_set_add visited_before cur_vertex visited_after ->
    dist_cell dist_values cur_vertex = cur_distance ->
    -1 <= edge ->
    dijkstra_heap_after_pop_bridge_state
      g src visited_before dist_values queue_set_before queue_set_after
      cur_vertex cur_distance ->
    dijkstra_heap_edge_loop_bridge_state
      g src visited_after cur_vertex cur_distance edge
      dist_values queue_set_after.
Proof.
  intros g src visited_before visited_after dist_values queue_set_before
    queue_set_after cur_vertex cur_distance edge Hcur_valid Hvisit_add
    Hcur_dist Hedge Hbridge.
  unfold dijkstra_heap_after_pop_bridge_state in Hbridge.
  destruct Hbridge as (Hloop_after & Hrefines_before & Hpop).
  unfold dijkstra_heap_edge_loop_bridge_state.
  split.
  - unfold dijkstra_heap_edge_loop_state.
    split; [exact Hloop_after |].
    split; [exact Hcur_valid |].
    split; [exact Hcur_dist | exact Hedge].
  - eapply heap_queue_refines_unvisited_dist_pop_visit; eauto.
Qed.

Lemma dijkstra_heap_edge_loop_to_loop_state :
  forall g src visited_set cur_vertex cur_distance edge dist_values queue_set,
    dijkstra_heap_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values queue_set ->
    dijkstra_heap_loop_state g src visited_set dist_values queue_set.
Proof. unfold dijkstra_heap_edge_loop_state; tauto. Qed.

Lemma dijkstra_heap_edge_loop_next :
  forall g src visited_set cur_vertex cur_distance edge next_edge
         dist_values queue_set,
    dijkstra_heap_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values queue_set ->
    -1 <= next_edge ->
    dijkstra_heap_edge_loop_state
      g src visited_set cur_vertex cur_distance next_edge dist_values queue_set.
Proof.
  unfold dijkstra_heap_edge_loop_state; intros; tauto.
Qed.

Lemma dijkstra_heap_edge_loop_state_relax_update :
  forall g vertex_count src visited_set cur_vertex cur_distance edge
         neighbor edge_weight candidate dist_values queue_set,
    graph_has_size g vertex_count ->
    vertex_valid g neighbor ->
    storage_index neighbor ->
    0 <= candidate < DijkstraGraph.infinity ->
    0 <= edge_weight ->
    candidate = cur_distance + edge_weight ->
    candidate < dist_cell dist_values neighbor ->
    dijkstra_heap_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values queue_set ->
    dijkstra_heap_edge_loop_state
      g src visited_set cur_vertex cur_distance edge
      (replace_Znth neighbor candidate dist_values) queue_set.
Proof.
  intros g vertex_count src visited_set cur_vertex cur_distance edge
    neighbor edge_weight candidate dist_values queue_set
    Hsize Hneighbor_valid Hneighbor_storage Hcandidate_bounds
    Hweight_nonneg Hcandidate Hrelax Hedge.
  unfold dijkstra_heap_edge_loop_state in *.
  destruct Hedge as (Hloop & Hcur_valid & Hcur_dist & Hedge_nonneg).
  assert (Hshape_loop : vector_shape dist_values)
    by (unfold dijkstra_heap_loop_state in Hloop; tauto).
  assert (Hneighbor_ne_cur : neighbor <> cur_vertex)
    by (intro Hsame; subst neighbor;
        rewrite Hcur_dist in Hrelax; subst candidate; lia).
  split.
  - unfold dijkstra_heap_loop_state in *.
    destruct Hloop as
      (Hwf & Hsrc & Hnonneg & Hshape & Hsafe & Hqueue_valid).
    do 3 (split; [assumption |]).
    split.
    + unfold vector_shape in *.
      rewrite Zlength_replace_Znth.
      exact Hshape.
    + split.
      * eapply dist_values_safe_replace_Znth; eauto.
      * exact Hqueue_valid.
  - split; [exact Hcur_valid |].
    split.
    + rewrite dist_cell_replace_Znth_diff
        by (eauto using graph_has_size_vertex_valid_storage; lia).
      exact Hcur_dist.
    + exact Hedge_nonneg.
Qed.

Lemma dijkstra_heap_loop_state_push :
  forall g vertex_count src visited_set dist_values queue_set queue_set_after
         vertex distance,
    graph_has_size g vertex_count ->
    dijkstra_heap_loop_state g src visited_set dist_values queue_set ->
    vertex_valid g vertex ->
    0 <= distance <= DijkstraGraph.infinity ->
    index_queue_push_result queue_set queue_set_after vertex distance ->
    dijkstra_heap_loop_state g src visited_set dist_values queue_set_after.
Proof.
  intros g vertex_count src visited_set dist_values queue_set queue_set_after
    vertex distance Hsize Hstate Hvertex Hdistance Hpush.
  unfold index_queue_push_result in Hpush.
  subst queue_set_after.
  unfold dijkstra_heap_loop_state in *.
  destruct Hstate as (Hwf & Hsrc & Hnonneg & Hshape & Hsafe & Hvalid).
  do 5 (split; [assumption |]).
  unfold heap_queue_items_valid in *.
  intros item Hin.
  unfold multiset_insert, list_to_multiset in Hin.
  simpl in Hin.
  destruct Hin as [Hitem | Hin].
  - subst item; simpl; auto.
  - apply Hvalid; exact Hin.
Qed.

Lemma dijkstra_heap_edge_loop_bridge_next :
  forall g src visited_set cur_vertex cur_distance edge next_edge
         dist_values queue_set,
    dijkstra_heap_edge_loop_bridge_state
      g src visited_set cur_vertex cur_distance edge
      dist_values queue_set ->
    -1 <= next_edge ->
    dijkstra_heap_edge_loop_bridge_state
      g src visited_set cur_vertex cur_distance next_edge
      dist_values queue_set.
Proof.
  intros g src visited_set cur_vertex cur_distance edge next_edge
    dist_values queue_set Hbridge Hnext.
  unfold dijkstra_heap_edge_loop_bridge_state in *.
  destruct Hbridge as (Hedge & Hrefines).
  split; [eapply dijkstra_heap_edge_loop_next; eauto | exact Hrefines].
Qed.

Lemma dijkstra_heap_edge_loop_bridge_to_loop_bridge :
  forall g src visited_set cur_vertex cur_distance edge
         dist_values queue_set,
    dijkstra_heap_edge_loop_bridge_state
      g src visited_set cur_vertex cur_distance edge
      dist_values queue_set ->
    dijkstra_heap_loop_bridge_state
      g src visited_set dist_values queue_set.
Proof.
  intros g src visited_set cur_vertex cur_distance edge
    dist_values queue_set Hbridge.
  unfold dijkstra_heap_edge_loop_bridge_state,
    dijkstra_heap_loop_bridge_state in *.
  destruct Hbridge as (Hedge & Hrefines).
  split; [eapply dijkstra_heap_edge_loop_to_loop_state; eauto | exact Hrefines].
Qed.

Lemma dijkstra_heap_edge_loop_bridge_relax_update_push_result :
  forall g vertex_count src visited_set cur_vertex cur_distance edge
         next_edge neighbor edge_weight candidate dist_values
         queue_set queue_set_after,
    graph_has_size g vertex_count ->
    vertex_valid g neighbor ->
    storage_index neighbor ->
    ~ visited_set neighbor ->
    0 <= candidate < DijkstraGraph.infinity ->
    0 <= edge_weight ->
    candidate = cur_distance + edge_weight ->
    candidate < dist_cell dist_values neighbor ->
    -1 <= next_edge ->
    index_queue_push_result queue_set queue_set_after neighbor candidate ->
    dijkstra_heap_edge_loop_bridge_state
      g src visited_set cur_vertex cur_distance edge
      dist_values queue_set ->
    dijkstra_heap_edge_loop_bridge_state
      g src visited_set cur_vertex cur_distance next_edge
      (replace_Znth neighbor candidate dist_values) queue_set_after.
Proof.
  intros g vertex_count src visited_set cur_vertex cur_distance edge
    next_edge neighbor edge_weight candidate dist_values
    queue_set queue_set_after Hsize Hneighbor_valid Hneighbor_storage
    Hneighbor_unvisited Hcandidate_bounds Hweight_nonneg Hcandidate_eq
    Hrelax Hnext Hpush Hbridge.
  unfold dijkstra_heap_edge_loop_bridge_state in Hbridge.
  destruct Hbridge as (Hedge & Hrefines).
  assert (Hshape_old : vector_shape dist_values)
    by (unfold dijkstra_heap_edge_loop_state,
          dijkstra_heap_loop_state in Hedge; tauto).
  assert (Hitems_valid : heap_queue_items_valid g queue_set)
    by (unfold dijkstra_heap_edge_loop_state,
          dijkstra_heap_loop_state in Hedge; tauto).
  assert (Hupdated_edge :
    dijkstra_heap_edge_loop_state g src visited_set cur_vertex cur_distance edge
      (replace_Znth neighbor candidate dist_values) queue_set).
  {
    eapply dijkstra_heap_edge_loop_state_relax_update; eauto.
  }
  destruct Hupdated_edge as (Hloop_updated & Hcur_valid & Hcur_dist & _).
  unfold dijkstra_heap_edge_loop_bridge_state.
  split.
  - unfold dijkstra_heap_edge_loop_state.
    split.
    + eapply (dijkstra_heap_loop_state_push
        g vertex_count src visited_set
        (replace_Znth neighbor candidate dist_values)
        queue_set queue_set_after neighbor candidate); eauto.
      lia.
    + do 2 (split; [eassumption |]).
      exact Hnext.
  - eapply heap_queue_refines_unvisited_dist_relax_push.
    + exact Hsize.
    + exact Hshape_old.
    + exact Hneighbor_storage.
    + exact Hneighbor_unvisited.
    + exact Hrelax.
    + lia.
    + exact Hitems_valid.
    + exact Hrefines.
    + exact Hpush.
Qed.

Lemma dijkstra_heap_lfs_edge_loop_cont_unfold :
  forall head_values to_values weight_values next_values
         cur_vertex cur_distance edge queue_set,
    Sets.equiv
      (dijkstra_heap_lfs_edge_loop_cont
        head_values to_values weight_values next_values
        cur_vertex cur_distance edge queue_set)
      (step_result <-
        dijkstra_heap_lfs_edge_body
          head_values to_values weight_values next_values
          cur_vertex cur_distance (edge, queue_set);;
       dijkstra_heap_lfs_edge_loop_after_body_cont
        head_values to_values weight_values next_values
        cur_vertex cur_distance step_result).
Proof.
  intros.
  unfold dijkstra_heap_lfs_edge_loop_cont,
    dijkstra_heap_lfs_edge_loop_after_body_cont,
    dijkstra_heap_lfs_edge_loop.
  rewrite (repeat_break_unfold
    (dijkstra_heap_lfs_edge_body
      head_values to_values weight_values next_values
      cur_vertex cur_distance)
    (edge, queue_set)), bind_assoc.
  reflexivity.
Qed.

Lemma dijkstra_heap_lfs_initial_to_loop_refines :
  forall g vertex_count src head_values to_values weight_values next_values
         visited_set dist_values queue_set X,
    graph_has_size g vertex_count ->
    visited_set_empty visited_set ->
    dijkstra_init_dist vertex_count src dist_values ->
    index_queue_push_result
      (list_to_multiset (@nil (Z * Z))) queue_set src 0 ->
    dijkstra_heap_lfs_initial_refines
      g src head_values to_values weight_values next_values X ->
    dijkstra_heap_loop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values queue_set X.
Proof.
  intros g vertex_count src head_values to_values weight_values next_values
    visited_set dist_values queue_set X Hsize Hempty Hinit Hpush Hrefines.
  unfold index_queue_push_result in Hpush.
  subst queue_set.
  unfold dijkstra_heap_lfs_initial_refines in Hrefines.
  destruct Hrefines as (Hrefines & Hno_overflow).
  unfold dijkstra_heap_lfs_program in Hrefines.
  unfold singleton_source_queue in Hrefines.
  unfold dijkstra_heap_loop_refines.
  split.
  - eapply safeExec_conseq.
    + exact Hrefines.
    + intros s Hs.
      subst s.
      apply dijkstra_init_dist_graph_state_model_initial
        with (vertex_count := vertex_count); auto.
  - split.
    + apply heap_queue_loop_capacity_state_singleton_source.
      exact Hempty.
    + split.
      * assert (Hsrc_valid : vertex_valid g src).
      {
        pose proof Hinit as Hinit_copy.
        unfold graph_has_size, vertex_valid, DijkstraGraph.vertex_valid in *.
        destruct Hinit_copy as (_ & _ & _ & Hsrc_bounds & _).
        lia.
      }
        eapply heap_queue_refines_unvisited_dist_singleton_source; eauto.
      * left.
        split; [exact Hempty |].
        split.
        -- destruct Hsize as (Hvertex_count & _).
           rewrite Hvertex_count.
           exact Hinit.
        -- split; [exact Hno_overflow |].
           unfold singleton_source_queue.
           reflexivity.
Qed.

Lemma dijkstra_heap_loop_refines_empty_to_return :
  forall g src head_values to_values weight_values next_values
         visited_set dist_values queue_set X,
    mlist queue_set = nil ->
    dijkstra_heap_loop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values queue_set X ->
    safeExec (graph_state_model g visited_set dist_values) (return tt) X.
Proof.
  intros g src head_values to_values weight_values next_values
    visited_set dist_values queue_set X Hempty Hrefines.
  unfold dijkstra_heap_loop_refines in Hrefines.
  destruct Hrefines as (Hrefines & _Hcap & _Hheap).
  unfold dijkstra_heap_lfs_loop in Hrefines.
  eapply safeExec_proequiv in Hrefines.
  2: { apply repeat_break_unfold. }
  unfold dijkstra_heap_lfs_loop_body in Hrefines.
  eapply safeExec_bind_reta with (a := by_break tt) in Hrefines.
  - simpl in Hrefines.
    exact Hrefines.
  - intros Xbody Hbody.
    apply safeExec_choice_l in Hbody.
    eapply safeExec_testst_bind in Hbody.
    + exact Hbody.
    + intros s _.
      exact Hempty.
Qed.

Lemma dijkstra_heap_loop_refines_pop :
  forall g src head_values to_values weight_values next_values
         visited_set dist_values queue_set queue_set_after cur_vertex
         cur_distance X,
    index_queue_pop_result queue_set queue_set_after cur_vertex cur_distance ->
    dijkstra_heap_loop_state g src visited_set dist_values queue_set ->
    dijkstra_heap_loop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values queue_set X ->
    dijkstra_heap_after_pop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values queue_set_after cur_vertex cur_distance X.
Proof.
  intros g src head_values to_values weight_values next_values
    visited_set dist_values queue_set queue_set_after cur_vertex cur_distance X
    Hpop Hloop_state Hrefines.
  assert (Hnotnil : mlist queue_set <> nil).
  {
    pose proof Hpop as Hpop_copy.
    unfold index_queue_pop_result, multiset_minimum in Hpop_copy.
    destruct Hpop_copy as
      (popped & _Hpopped & (Hin & _Hminimum) & _Hafter).
    intro Hnil. rewrite Hnil in Hin. contradiction.
  }
  unfold dijkstra_heap_loop_refines in Hrefines.
  destruct Hrefines as (Hrefines & Hcap & Hheap_refines & Hphase).
  unfold dijkstra_heap_after_pop_refines.
  split.
  - unfold dijkstra_heap_lfs_loop in Hrefines.
    eapply safeExec_proequiv in Hrefines.
    2: { apply repeat_break_unfold. }
    unfold dijkstra_heap_lfs_loop_body in Hrefines.
    lfs_prog_nf Hrefines.
    apply safeExec_choice_r in Hrefines.
    lfs_prog_nf Hrefines.
    eapply safeExec_testst_bind in Hrefines.
    2: { intros s _. exact Hnotnil. }
    lfs_prog_nf Hrefines.
    unfold index_queue_pop_choice in Hrefines.
    lfs_prog_nf Hrefines.
    eapply safeExec_get_bind with
      (a := ((queue_set_after, cur_vertex), cur_distance)) in Hrefines.
    2: { intros s _. exact Hpop. }
    cbn in Hrefines.
    lfs_prog_nf Hrefines.
    unfold dijkstra_heap_lfs_after_pop_cont.
    unfold dijkstra_heap_lfs_loop.
    unfold dijkstra_heap_lfs_loop_body.
    unfold index_queue_pop_choice.
    cbn.
    eapply safeExec_proequiv.
    2: { exact Hrefines. }
    symmetry.
    rewrite bind_choice_equiv.
    repeat rewrite bind_assoc; reflexivity.
  - split.
    + eapply heap_queue_loop_capacity_state_pop; eauto.
    + exists queue_set.
      split; [exact Hloop_state |].
      split; [exact Hheap_refines |].
      split; [exact Hpop | exact Hphase].
Qed.

Lemma dijkstra_heap_after_pop_refines_equal_to_edge_loop :
  forall g edge_count src head_values to_values weight_values next_values
         visited_set visited_set' dist_values queue_set_after
         cur_vertex cur_distance X,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    vertex_valid g cur_vertex ->
    visited_set_add visited_set cur_vertex visited_set' ->
    dist_cell dist_values cur_vertex = cur_distance ->
    (Znth cur_vertex head_values 0 = -1 \/
      next_chain next_values (Znth cur_vertex head_values (-1))
        (Znth cur_vertex head_values 0)) ->
    dijkstra_heap_after_pop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values queue_set_after cur_vertex cur_distance X ->
    dijkstra_heap_edge_loop_refines
      g src cur_vertex cur_distance (Znth cur_vertex head_values 0)
      head_values to_values weight_values next_values
      visited_set' dist_values queue_set_after X.
Proof.
  intros g edge_count src head_values to_values weight_values next_values
    visited_set visited_set' dist_values queue_set_after
    cur_vertex cur_distance X Hmodel Hvalid Hvisit_add Hdist Hchain_loc
    Hrefines.
  unfold dijkstra_heap_after_pop_refines in Hrefines.
  destruct Hrefines as
    (Hrefines & Hcap & queue_set_before & Hloop_before
     & Hheap_before & Hpop & Hphase_before).
  assert (Hunvisited : ~ visited_set cur_vertex).
  {
    pose proof Hheap_before as Hheap_before_copy.
    unfold heap_queue_refines_unvisited_dist,
      priority_queue_refines_unvisited_dist in Hheap_before_copy.
    destruct Hheap_before_copy as (_ & Hfresh & _).
    pose proof Hpop as Hpop_copy.
    unfold index_queue_pop_result in Hpop_copy.
    destruct Hpop_copy as (popped & Hpopped & Hmin & _).
    subst popped.
    destruct Hmin as (Hin & _).
    eapply Hfresh.
    - exact Hin.
    - symmetry; exact Hdist.
  }
  unfold dijkstra_heap_lfs_after_pop_cont in Hrefines.
  lfs_prog_nf Hrefines.
  apply safeExec_choice_l in Hrefines.
  lfs_prog_nf Hrefines.
  eapply safeExec_testst_bind in Hrefines.
  2: {
    intros s Hstate_model.
    erewrite graph_state_model_dist_cell by eauto.
    symmetry.
    exact Hdist.
  }
  lfs_prog_nf Hrefines.
  apply safeExec_update'_bind in Hrefines.
  lfs_prog_nf Hrefines.
  unfold dijkstra_heap_edge_loop_refines.
  split.
  - unfold dijkstra_heap_lfs_edge_loop_cont.
    unfold dijkstra_heap_lfs_loop.
    eapply safeExec_conseq.
    + eapply safeExec_proequiv.
      2: { exact Hrefines. }
      lfs_finish_equiv.
    + intros s (s0 & Hs & Hstate_model).
      subst s.
      apply graph_state_model_visit_state with (visited_set := visited_set);
        auto.
  - split.
    + eapply heap_queue_edge_capacity_state_start; eauto.
    + split.
      * eapply heap_queue_refines_unvisited_dist_pop_visit; eauto.
	      * assert (Hwf : DijkstraGraph.graph_wf g)
	          by (unfold dijkstra_heap_loop_state in Hloop_before; tauto).
	        assert (Hsize_self :
	          graph_has_size g (DijkstraGraph.vertex_count g)).
	        {
	          unfold graph_has_size.
	          split; [reflexivity |].
	          destruct Hwf as (Hcount_bound & _).
	          exact Hcount_bound.
	        }
        destruct Hphase_before as
          [(Hempty & Hinit & Hno_overflow & Hsingleton) |
           (Hvisited_valid & Hno_overflow & Hmath)].
        -- pose proof Hpop as Hpop_singleton.
           rewrite Hsingleton in Hpop_singleton.
           pose proof
             (index_queue_pop_result_singleton_source_early
               src queue_set_after cur_vertex cur_distance Hpop_singleton)
             as (_Hqueue_empty & Hcur_vertex & Hcur_distance).
           subst cur_vertex cur_distance.
           split; [unfold DijkstraGraph.infinity; lia |].
	           left.
	           split.
	           ++ intro v.
              unfold visited_set_add in Hvisit_add.
              split.
              ** intro Hv.
                 apply Hvisit_add in Hv as [Hv_old | Hv_src].
                 --- exfalso. apply (Hempty v). exact Hv_old.
                 --- exact Hv_src.
	              ** intro Hv.
	                 apply Hvisit_add. right. exact Hv.
	           ++ split; [exact Hno_overflow |].
	              split; [reflexivity |].
	              split; [exact Hcur_distance |].
              split; [exact Hchain_loc |].
              eapply dijkstra_first_step_math_state_done_equiv.
              ** intros e_abs.
                 symmetry.
                 eapply forward_star_done_edge_set_head_empty_equiv; eauto.
              ** eapply dijkstra_init_dist_first_step_math_state_empty;
                   eauto.
        -- assert (Hcur_finite :
             0 <= cur_distance < DijkstraGraph.infinity).
           {
             split.
             - rewrite <- Hdist.
               unfold dijkstra_heap_loop_state in Hloop_before.
               destruct Hloop_before as
                 (_ & _ & _ & _ & Hsafe & _).
               apply Hsafe.
               eapply graph_has_size_vertex_valid_storage; eauto.
             - unfold heap_queue_refines_unvisited_dist,
                 priority_queue_refines_unvisited_dist in Hheap_before.
               destruct Hheap_before as (_ & _ & _ & Hfinite & _).
               pose proof Hpop as Hpop_in.
               unfold index_queue_pop_result in Hpop_in.
               destruct Hpop_in as (popped & Hpopped & (Hin & _) & _).
               subst popped.
               apply (Hfinite cur_distance cur_vertex).
               exact Hin.
           }
           split; [exact Hcur_finite |].
           right.
           exists visited_set, dist_values.
           split; [exact Hvisited_valid |].
           split; [exact Hno_overflow |].
           split; [exact Hvisit_add |].
           split; [symmetry; exact Hdist |].
           split; [exact Hchain_loc |].
	           assert (Hselected :
	             dijkstra_selected_min g visited_set dist_values cur_vertex).
	           {
	             eapply dijkstra_heap_pop_selected_min
	               with (vertex_count := DijkstraGraph.vertex_count g)
	                    (queue_set_after := queue_set_after);
	               eauto;
	               try exact Hsize_self;
	               try (symmetry; exact Hdist);
	               try exact Hcur_finite.
	           }
           eapply (dijkstra_edge_math_state_done_equiv
             g src visited_set visited_set' cur_vertex dist_values
             (fun _ : DijkstraGraph.E => False)
             (forward_star_done_edge_set
               head_values to_values weight_values next_values
               cur_vertex (Znth cur_vertex head_values 0))
             dist_values).
           ++ intros e_abs.
              symmetry.
              eapply forward_star_done_edge_set_head_empty_equiv; eauto.
           ++ unfold dijkstra_edge_math_state, Dijkstra.relax_step_invariant.
              split; [exact Hvisit_add |].
              split; [exact Hmath |].
              split; [exact Hselected |].
              split.
              ** unfold dijkstra_after_visit_state, set_state_visited,
                   dijkstra_array_state; simpl; sets_unfold.
                 intro v; split.
                 --- intros [Hvalid_after Hvisited_after].
	                     unfold visited_set_add in Hvisit_add.
	                     apply Hvisit_add in Hvisited_after as
	                       [Hvisited_before | Heq].
	                     { left; split; [apply Hvisited_valid |];
	                         exact Hvisited_before. }
	                     { right; symmetry; exact Heq. }
	                 --- intros [[Hvalid_before Hvisited_before] | Heq];
	                     subst.
	                     { split; [exact Hvalid_before |].
	                       unfold visited_set_add in Hvisit_add.
	                       apply Hvisit_add; left; exact Hvisited_before. }
	                     { split; [exact Hvalid |].
	                       unfold visited_set_add in Hvisit_add.
	                       apply Hvisit_add; right; reflexivity. }
              ** split; [reflexivity |].
                 split.
                 --- intros v e _ Hfalse _. contradiction.
                 --- intros v _ _.
                     unfold dijkstra_after_visit_state, set_state_visited,
                       dijkstra_array_state; simpl.
                     destruct (vertex_valid_dec g v); reflexivity.
Qed.

Lemma dijkstra_heap_after_pop_refines_not_equal_to_loop :
  forall g src head_values to_values weight_values next_values
         visited_set dist_values queue_set_after cur_vertex cur_distance X,
    vertex_valid g cur_vertex ->
    cur_distance <> dist_cell dist_values cur_vertex ->
    dijkstra_heap_after_pop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values queue_set_after cur_vertex cur_distance X ->
    dijkstra_heap_loop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values queue_set_after X.
Proof.
  intros g src head_values to_values weight_values next_values
    visited_set dist_values queue_set_after cur_vertex cur_distance X
    Hvalid Hdist_neq Hrefines.
  unfold dijkstra_heap_after_pop_refines in Hrefines.
  destruct Hrefines as
    (Hrefines & Hcap & queue_set_before & Hloop_before
     & Hheap_before & Hpop & Hphase_before).
  unfold dijkstra_heap_lfs_after_pop_cont in Hrefines.
  lfs_prog_nf Hrefines.
  apply safeExec_choice_r in Hrefines.
  lfs_prog_nf Hrefines.
  eapply safeExec_testst_bind in Hrefines.
  2: {
    intros s Hstate_model.
    erewrite graph_state_model_dist_cell by eauto.
    exact Hdist_neq.
  }
  unfold dijkstra_heap_loop_refines.
  split.
  - eapply safeExec_proequiv.
    2: { exact Hrefines. }
    lfs_finish_equiv.
  - split; [exact Hcap |].
    split.
    + eapply heap_queue_refines_unvisited_dist_pop_stale; eauto.
    + destruct Hphase_before as
        [(Hempty & Hinit & Hno_overflow & Hsingleton) | Hnormal_phase].
      * exfalso.
        pose proof Hpop as Hpop_singleton.
        rewrite Hsingleton in Hpop_singleton.
        pose proof
          (index_queue_pop_result_singleton_source_early
            src queue_set_after cur_vertex cur_distance Hpop_singleton)
          as (_ & Hcur_vertex & Hcur_distance).
        subst cur_vertex cur_distance.
        apply Hdist_neq.
        destruct Hinit as (_ & _ & _ & Hsrc_bounds & Hcell).
        rewrite Hcell by exact Hsrc_bounds.
        destruct (Z.eq_dec src src); [reflexivity | contradiction].
      * right. exact Hnormal_phase.
Qed.

Lemma dijkstra_heap_after_relax_refines_push_to_edge_loop :
  forall g edge_count src cur_vertex cur_distance edge neighbor candidate
         head_values to_values weight_values next_values visited_set dist_values
         queue_set queue_set_after X,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    vertex_valid g cur_vertex ->
    edge_index edge_count edge ->
    neighbor = Znth edge to_values 0 ->
    index_queue_push_result queue_set queue_set_after neighbor candidate ->
    dijkstra_heap_after_relax_refines
      g src cur_vertex cur_distance edge neighbor candidate
      head_values to_values weight_values next_values
      visited_set dist_values queue_set X ->
    dijkstra_heap_edge_loop_refines
      g src cur_vertex cur_distance (Znth edge next_values 0)
      head_values to_values weight_values next_values
      visited_set dist_values queue_set_after X.
Proof.
  intros g edge_count src cur_vertex cur_distance edge neighbor candidate
    head_values to_values weight_values next_values visited_set dist_values
    queue_set queue_set_after X Hmodel Hcur_valid Hedge_index Hneighbor
    Hpush Hrefines.
  unfold dijkstra_heap_after_relax_refines in Hrefines.
  destruct Hrefines as (Hrefines & Hcap & Hheap_after).
  unfold index_queue_push_choice in Hrefines.
  eapply safeExec_get_bind with (a := queue_set_after) in Hrefines.
  2: { intros s _. exact Hpush. }
  unfold dijkstra_heap_edge_loop_refines.
  split; [exact Hrefines |].
  split.
  - pose proof
      (forward_star_model_chain_wf _ _ _ _ _ _ Hmodel) as Hchain_wf.
    pose proof
      (forward_star_model_edge_safe _ _ _ _ _ _ Hmodel)
      as (Hto_len & _Hweight_len & Hnext_len & _).
    pose proof
      (forward_star_model_edge_bounds _ _ _ _ _ _ _ Hmodel Hedge_index)
      as (Hneighbor_bounds & _Hneighbor_storage & _Hweight_bounds
          & Hnext_case).
    pose proof Hmodel as Hmodel_copy.
    unfold forward_star_model in Hmodel_copy.
    destruct Hmodel_copy as (_Hwf & Hsize_model & _).
    assert (Hcur_storage : storage_index cur_vertex)
      by (eapply graph_has_size_vertex_valid_storage; eauto).
    assert (Hpair_valid : vertex_pair_valid g (cur_vertex, neighbor)).
    {
      unfold vertex_pair_valid.
      split; [exact Hcur_valid |].
      subst neighbor.
      unfold vertex_valid, DijkstraGraph.vertex_valid.
      exact Hneighbor_bounds.
    }
    eapply (heap_queue_edge_capacity_state_push_step
      g visited_set cur_vertex edge head_values to_values next_values
      queue_set queue_set_after neighbor candidate).
    + exact Hchain_wf.
    + exact Hcur_storage.
    + exact Hpair_valid.
    + exact Hneighbor.
    + unfold edge_index in Hedge_index; lia.
    + unfold edge_index in Hedge_index; lia.
    + unfold edge_index in Hedge_index; lia.
    + lia.
    + destruct Hnext_case as [Hnext_nil | Hnext_edge].
      * left.
        rewrite (Znth_indep next_values edge 0 (-1))
          by (unfold edge_index in Hedge_index; lia).
        exact Hnext_nil.
      * right.
        rewrite (Znth_indep next_values edge 0 (-1))
          by (unfold edge_index in Hedge_index; lia).
        unfold edge_index in Hnext_edge.
        rewrite Hnext_len.
        exact Hnext_edge.
    + exact Hpush.
    + exact Hcap.
  - specialize (Hheap_after queue_set_after Hpush) as
      (Hheap_refines_after & Hphase_after).
    split; [exact Hheap_refines_after | exact Hphase_after].
Qed.

Lemma dijkstra_heap_edge_phase_relax_update :
  forall g vertex_count edge_count src cur_vertex cur_distance edge
         neighbor edge_weight candidate
         head_values to_values weight_values next_values
         visited_set dist_values queue_set,
    graph_has_size g vertex_count ->
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_index edge_count edge ->
    edge <> -1 ->
    neighbor = Znth edge to_values 0 ->
    edge_weight = Znth edge weight_values 0 ->
    candidate = cur_distance + edge_weight ->
    vertex_valid g neighbor ->
    storage_index neighbor ->
    ~ visited_set neighbor ->
    0 <= candidate < DijkstraGraph.infinity ->
    0 <= edge_weight ->
    candidate < dist_cell dist_values neighbor ->
    dijkstra_heap_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values queue_set ->
    dijkstra_heap_edge_phase_state
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values queue_set ->
    dijkstra_heap_edge_phase_state
      g src cur_vertex cur_distance (Znth edge next_values 0)
      head_values to_values weight_values next_values
      visited_set (replace_Znth neighbor candidate dist_values) queue_set.
Proof.
  intros g vertex_count edge_count src cur_vertex cur_distance edge
    neighbor edge_weight candidate head_values to_values weight_values
    next_values visited_set dist_values queue_set Hsize Hmodel Hedge_index
    Hedge_not_nil Hneighbor Hweight Hcandidate Hneighbor_valid
    Hneighbor_storage Hunvisited Hcandidate_bounds Hweight_nonneg Hrelax
    Hedge_state Hphase.
  subst neighbor edge_weight candidate.
  assert (Hcur_valid : vertex_valid g cur_vertex)
    by (unfold dijkstra_heap_edge_loop_state in Hedge_state; tauto).
  assert (Hloop_state :
    dijkstra_heap_loop_state g src visited_set dist_values queue_set)
    by (eapply dijkstra_heap_edge_loop_to_loop_state; eauto).
  assert (Hshape : vector_shape dist_values)
    by (unfold dijkstra_heap_loop_state in Hloop_state; tauto).
  assert (Hsafe : dist_values_safe dist_values)
    by (unfold dijkstra_heap_loop_state in Hloop_state; tauto).
  assert (Hcur_dist : dist_cell dist_values cur_vertex = cur_distance)
    by (unfold dijkstra_heap_edge_loop_state in Hedge_state; tauto).
  assert (Hcur_storage : storage_index cur_vertex)
    by (eapply graph_has_size_vertex_valid_storage; eauto).
  assert (Hcur_finite :
    0 <= cur_distance < DijkstraGraph.infinity).
  {
    split.
    - rewrite <- Hcur_dist. apply Hsafe. exact Hcur_storage.
    - assert (cur_distance <=
        cur_distance + Znth edge weight_values 0) by lia.
      lia.
  }
  split; [exact Hcur_finite |].
  destruct Hphase as
    (_Hcur_finite_phase &
    [(Hvisited_src & Hno_overflow & Hcur_src & Hcur_zero & Hchain & Hfirst) |
     (visited_before & base_dist_values & Hvisited_valid & Hno_overflow
      & Hvisit_add & Hcur_base & Hchain & Hmath)]).
  - subst cur_vertex cur_distance.
    assert (Hnonneg : nonnegative_edges g)
      by (unfold dijkstra_heap_edge_loop_state,
            dijkstra_heap_loop_state in Hedge_state; tauto).
    assert (Hhead_edge :
      next_chain next_values (Znth src head_values (-1)) edge)
      by (destruct Hchain as [Hnil | Hchain]; [contradiction | exact Hchain]).
    pose proof
      (forward_star_current_edge_facts
        g vertex_count edge_count head_values to_values weight_values
        next_values src edge Hsize Hmodel Hcur_valid Hhead_edge
        Hedge_index)
      as (Hchain_wf & Hsrc_storage & Hedge_to & Hedge_next
          & Hneighbor_valid0 & Hneighbor_storage0 & Hstep & Hweight_edge
          & _Hnext_eq).
    left.
    split; [exact Hvisited_src |].
    split; [exact Hno_overflow |].
    split; [reflexivity |].
    split; [reflexivity |].
    split.
    + eapply forward_star_next_0_nil_or_chain; eauto.
    + eapply dijkstra_first_step_math_state_done_equiv.
      * intros e_abs.
        symmetry.
        eapply forward_star_done_edge_set_step_0; eauto.
      * unfold dijkstra_first_step_math_state in *.
        eapply dijkstra_first_step_invariant_add_edge; eauto.
        -- intros e_abs Hdone.
           eapply forward_star_done_edge_set_step_aux; eauto.
        -- eapply forward_star_current_edge_not_done; eauto.
        -- intro Hsame.
           subst.
           eapply DijkstraGraph_step_aux_no_self; eauto.
           eapply forward_star_model_graph_wf; eauto.
        -- unfold dijkstra_array_state; simpl; reflexivity.
	        -- erewrite dijkstra_array_state_dist_replace_other
	             by (eauto; intro Hsame; subst;
	                 eapply DijkstraGraph_step_aux_no_self; eauto;
	                 eapply forward_star_model_graph_wf; eauto).
	           reflexivity.
        -- erewrite dijkstra_array_state_dist_replace_same by eauto.
           rewrite Hweight_edge.
           replace (0 + Znth edge weight_values 0)
             with (Znth edge weight_values 0) by lia.
           reflexivity.
        -- intros v Hneq_neighbor.
           erewrite dijkstra_array_state_dist_replace_other by eauto.
           reflexivity.
  - assert (Hhead_edge :
      next_chain next_values (Znth cur_vertex head_values (-1)) edge)
      by (destruct Hchain as [Hnil | Hchain]; [contradiction | exact Hchain]).
    pose proof
      (forward_star_current_edge_facts
        g vertex_count edge_count head_values to_values weight_values
        next_values cur_vertex edge Hsize Hmodel Hcur_valid Hhead_edge
        Hedge_index)
      as (Hchain_wf & Hcur_storage0 & Hedge_to & Hedge_next
          & Hneighbor_valid0 & Hneighbor_storage0 & Hstep & Hweight_edge
          & _Hnext_eq).
    right.
    exists visited_before, base_dist_values.
    split; [exact Hvisited_valid |].
    split; [exact Hno_overflow |].
    split; [exact Hvisit_add |].
    split; [exact Hcur_base |].
    split.
    + eapply forward_star_next_0_nil_or_chain; eauto.
    + eapply dijkstra_edge_math_state_done_equiv.
      * intros e_abs.
        symmetry.
        eapply forward_star_done_edge_set_step_0; eauto.
	      * eapply (dijkstra_edge_math_state_relax_update
	          g vertex_count src visited_before visited_set cur_vertex
	          base_dist_values
	          (forward_star_done_edge_set
	            head_values to_values weight_values next_values cur_vertex edge)
	          dist_values (cur_vertex, Znth edge to_values 0)
	          (Znth edge to_values 0) (Znth edge weight_values 0)
	          cur_distance (cur_distance + Znth edge weight_values 0)).
	        -- exact Hsize.
	        -- eapply forward_star_model_graph_wf; eauto.
	        -- exact Hshape.
	        -- exact Hsafe.
	        -- exact Hneighbor_valid0.
	        -- exact Hneighbor_storage0.
	        -- exact Hcur_base.
	        -- exact Hcur_finite.
	        -- exact Hcandidate_bounds.
	        -- reflexivity.
	        -- exact Hweight_edge.
	        -- exact Hrelax.
	        -- intros e_abs Hdone.
	           eapply forward_star_done_edge_set_step_aux; eauto.
	        -- eapply forward_star_current_edge_not_done; eauto.
	        -- exact Hstep.
        -- exact Hmath.
Qed.

Lemma dijkstra_heap_edge_phase_candidate_bounds :
  forall g vertex_count edge_count src cur_vertex cur_distance edge
         head_values to_values weight_values next_values
         visited_set dist_values queue_set,
    graph_has_size g vertex_count ->
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_index edge_count edge ->
    edge <> -1 ->
    dijkstra_heap_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values queue_set ->
    dijkstra_heap_edge_phase_state
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values queue_set ->
    0 <= cur_distance + Znth edge weight_values 0 <
      DijkstraGraph.infinity.
Proof.
  intros g vertex_count edge_count src cur_vertex cur_distance edge
    head_values to_values weight_values next_values visited_set dist_values
    queue_set Hsize Hmodel Hedge_index Hedge_not_nil Hedge_state Hphase.
  assert (Hcur_valid : vertex_valid g cur_vertex)
    by (unfold dijkstra_heap_edge_loop_state in Hedge_state; tauto).
  destruct Hphase as
    (Hcur_finite_phase &
    [(Hvisited_src & Hno_overflow & Hcur_src & Hcur_zero & Hchain & _Hfirst) |
     (visited_before & base_dist_values & Hvisited_valid & Hno_overflow
      & Hvisit_add & Hcur_base & Hchain & Hmath)]).
  - subst cur_vertex cur_distance.
    assert (Hnonneg : nonnegative_edges g)
      by (unfold dijkstra_heap_edge_loop_state,
            dijkstra_heap_loop_state in Hedge_state; tauto).
    assert (Hhead_edge :
      next_chain next_values (Znth src head_values (-1)) edge)
      by (destruct Hchain as [Hnil | Hchain]; [contradiction | exact Hchain]).
    pose proof
      (forward_star_current_edge_facts
        g vertex_count edge_count head_values to_values weight_values
        next_values src edge Hsize Hmodel Hcur_valid Hhead_edge
        Hedge_index)
      as (_ & _ & _ & _ & Hneighbor_valid & _ & Hstep & Hweight & _).
	    apply (Hno_overflow src (Znth edge to_values 0)
	      (src, Znth edge to_values 0) 0 (Znth edge weight_values 0));
	      [exact Hcur_valid | exact Hneighbor_valid | exact Hstep
	      | dijkstra_index_min_epath_refl
	      | exact Hweight].
  - assert (Hhead_edge :
      next_chain next_values (Znth cur_vertex head_values (-1)) edge)
      by (destruct Hchain as [Hnil | Hchain]; [contradiction | exact Hchain]).
    pose proof
      (forward_star_current_edge_facts
        g vertex_count edge_count head_values to_values weight_values
        next_values cur_vertex edge Hsize Hmodel Hcur_valid Hhead_edge
        Hedge_index)
      as (_ & _ & _ & _ & Hneighbor_valid & _ & Hstep & Hweight & _).
    unfold dijkstra_edge_math_state in Hmath.
    destruct Hmath as (_ & Hmath_before & Hselected & _).
    unfold dijkstra_math_invariant in Hmath_before.
    destruct Hmath_before as (_ & Hoptimal & _).
    pose proof
      (dijkstra_greedy_choice_correct
        g ltac:(eapply forward_star_model_graph_wf; eauto)
        src
        ltac:(unfold dijkstra_heap_edge_loop_state,
               dijkstra_heap_loop_state in Hedge_state; tauto)
        cur_vertex
        (@visited Z
          (dijkstra_array_state g visited_before base_dist_values))
        (@dist Z
          (dijkstra_array_state g visited_before base_dist_values))
        Hoptimal Hselected) as Hshortest.
    replace (@dist Z
      (dijkstra_array_state g visited_before base_dist_values)
      cur_vertex) with (Some cur_distance) in Hshortest.
    2: {
      rewrite dijkstra_array_state_dist_valid by exact Hcur_valid.
      rewrite <- Hcur_base.
      symmetry.
      apply cell_as_distance_finite.
      exact Hcur_finite_phase.
    }
    apply (Hno_overflow cur_vertex (Znth edge to_values 0)
      (cur_vertex, Znth edge to_values 0)
      cur_distance (Znth edge weight_values 0));
      auto.
Qed.

Lemma dijkstra_heap_skip_assume_to_dist_cell_pure :
  forall g edge_count head_values to_values weight_values next_values
         dist_values edge cur_distance,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_index edge_count edge ->
    0 <= cur_distance + Znth edge weight_values 0 <
      DijkstraGraph.infinity ->
    Znth edge weight_values 0 < 0 \/
      cur_distance > DijkstraGraph.infinity - Znth edge weight_values 0 \/
      cur_distance + Znth edge weight_values 0 >=
        dist_cell dist_values (Znth edge to_values 0) ->
    dist_cell dist_values (Znth edge to_values 0) <=
      cur_distance + Znth edge weight_values 0.
Proof.
  intros g edge_count head_values to_values weight_values next_values
    dist_values edge cur_distance Hmodel Hedge_index Hcandidate_bounds Hskip.
  destruct Hskip as [Hneg | [Hoverflow | Hge]].
  - pose proof
      (forward_star_model_edge_bounds _ _ _ _ _ _ _ Hmodel Hedge_index)
      as (_ & _ & Hweight_bounds & _).
    lia.
  - lia.
  - lia.
Qed.

Lemma dijkstra_heap_edge_phase_skip_update :
  forall g edge_count src cur_vertex cur_distance edge
         head_values to_values weight_values next_values
         visited_set dist_values queue_set,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_index edge_count edge ->
    edge <> -1 ->
    vertex_valid g (Znth edge to_values 0) ->
    Znth edge weight_values 0 < 0 \/
      cur_distance > DijkstraGraph.infinity - Znth edge weight_values 0 \/
      cur_distance + Znth edge weight_values 0 >=
        dist_cell dist_values (Znth edge to_values 0) ->
    dijkstra_heap_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values queue_set ->
    dijkstra_heap_edge_phase_state
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values queue_set ->
    dijkstra_heap_edge_phase_state
      g src cur_vertex cur_distance (Znth edge next_values 0)
      head_values to_values weight_values next_values
      visited_set dist_values queue_set.
Proof.
  intros g edge_count src cur_vertex cur_distance edge
    head_values to_values weight_values next_values visited_set dist_values
    queue_set Hmodel Hedge_index Hedge_not_nil Hneighbor_valid Hskip
    Hedge_state Hphase.
  assert (Hwf : DijkstraGraph.graph_wf g)
    by (eapply forward_star_model_graph_wf; eauto).
  assert (Hsize_self : graph_has_size g (DijkstraGraph.vertex_count g)).
  {
    unfold graph_has_size.
    split; [reflexivity |].
    destruct Hwf as (Hcount_bound & _).
    exact Hcount_bound.
  }
  assert (Hcur_valid : vertex_valid g cur_vertex)
    by (unfold dijkstra_heap_edge_loop_state in Hedge_state; tauto).
  assert (Hhead_edge :
    next_chain next_values (Znth cur_vertex head_values (-1)) edge).
  {
    destruct Hphase as (_ & [(_ & _ & Hcur_src & _ & Hchain & _) |
      (visited_before & base_dist_values & _ & _ & _ & _ & Hchain & _)]).
    - subst cur_vertex.
      destruct Hchain as [Hnil | Hchain]; [contradiction | exact Hchain].
    - destruct Hchain as [Hnil | Hchain]; [contradiction | exact Hchain].
  }
  pose proof
    (forward_star_current_edge_facts
      g (DijkstraGraph.vertex_count g) edge_count
      head_values to_values weight_values next_values cur_vertex edge
      Hsize_self Hmodel Hcur_valid Hhead_edge Hedge_index)
    as (Hchain_wf & _Hcur_storage & _Hedge_to & _Hedge_next
        & Hneighbor_valid0 & _Hneighbor_storage & Hstep & Hweight
        & _Hnext_eq).
  pose proof Hphase as Hphase_full.
  pose proof
    (dijkstra_heap_edge_phase_candidate_bounds
      g (DijkstraGraph.vertex_count g) edge_count src cur_vertex
      cur_distance edge head_values to_values weight_values next_values
      visited_set dist_values queue_set
      Hsize_self Hmodel Hedge_index Hedge_not_nil Hedge_state Hphase_full)
    as Hcandidate_bounds.
  assert (Hskip_cell :
    dist_cell dist_values (Znth edge to_values 0) <=
      cur_distance + Znth edge weight_values 0)
    by (eapply dijkstra_heap_skip_assume_to_dist_cell_pure; eauto).
  destruct Hphase as
    (Hcur_finite &
    [(Hvisited_src & Hno_overflow & Hcur_src & Hcur_zero & Hchain & Hfirst) |
     (visited_before & base_dist_values & Hvisited_valid & Hno_overflow
      & Hvisit_add & Hcur_base & Hchain & Hmath)]).
  - subst cur_vertex cur_distance.
    split; [exact Hcur_finite |].
    left.
    split; [exact Hvisited_src |].
    split; [exact Hno_overflow |].
    split; [reflexivity |].
    split; [reflexivity |].
    split.
    + eapply forward_star_next_0_nil_or_chain; eauto.
    + eapply dijkstra_first_step_math_state_done_equiv.
      * intros e_abs.
        symmetry.
        eapply forward_star_done_edge_set_step_0; eauto.
      * unfold dijkstra_first_step_math_state in *.
        pose proof Hfirst as Hfirst_cut.
        unfold Dijkstra.first_step_invariant in Hfirst_cut.
        destruct Hfirst_cut as (_ & _ & _ & Hcut).
        assert (Hneighbor_ne_src : Znth edge to_values 0 <> src)
          by (intro Heq; subst;
              eapply DijkstraGraph_step_aux_no_self; eauto).
        eapply dijkstra_first_step_invariant_add_edge.
        -- intros e_abs Hdone.
           eapply forward_star_done_edge_set_step_aux; eauto.
        -- eapply forward_star_current_edge_not_done; eauto.
        -- exact Hstep.
        -- exact Hneighbor_ne_src.
        -- exact Hfirst.
        -- unfold dijkstra_array_state; simpl; reflexivity.
        -- unfold dijkstra_array_state; simpl; reflexivity.
        -- exfalso.
           assert (Hno_old :
             forall e_abs,
               forward_star_done_edge_set head_values to_values
                 weight_values next_values src edge e_abs ->
               ~ dijkstra_step_aux g e_abs src (Znth edge to_values 0)).
           {
             eapply dijkstra_done_no_same_target; eauto.
             - intros e_abs Hdone.
               eapply forward_star_done_edge_set_step_aux; eauto.
             - apply forward_star_current_edge_not_done; auto.
           }
           pose proof
             (Hcut (Znth edge to_values 0) Hneighbor_ne_src Hno_old)
             as Hdist_none.
           rewrite dijkstra_array_state_dist_valid in Hdist_none
             by exact Hneighbor_valid0.
           unfold cell_as_distance, DijkstraGraph.cell_as_distance
             in Hdist_none.
           destruct (Z.eq_dec
             (dist_cell dist_values (Znth edge to_values 0))
             DijkstraGraph.infinity); [lia | discriminate].
        -- intros v Hneq_neighbor.
           unfold dijkstra_array_state; simpl; reflexivity.
  - split; [exact Hcur_finite |].
    right.
    exists visited_before, base_dist_values.
    split; [exact Hvisited_valid |].
    split; [exact Hno_overflow |].
    split; [exact Hvisit_add |].
    split; [exact Hcur_base |].
    split.
    + eapply forward_star_next_0_nil_or_chain; eauto.
    + eapply dijkstra_edge_math_state_done_equiv.
      * intros e_abs.
        symmetry.
        eapply forward_star_done_edge_set_step_0; eauto.
      * eapply (dijkstra_edge_math_state_relax_skip
          g (DijkstraGraph.vertex_count g) src visited_before visited_set
          cur_vertex base_dist_values
          (forward_star_done_edge_set
            head_values to_values weight_values next_values cur_vertex edge)
          dist_values (cur_vertex, Znth edge to_values 0)
          (Znth edge to_values 0) (Znth edge weight_values 0)
          cur_distance (cur_distance + Znth edge weight_values 0)).
        -- exact Hsize_self.
        -- exact Hwf.
        -- unfold dijkstra_heap_edge_loop_state,
             dijkstra_heap_loop_state in Hedge_state; tauto.
        -- exact Hneighbor_valid0.
        -- eapply graph_has_size_vertex_valid_storage; eauto.
        -- exact Hcur_base.
        -- exact Hcur_finite.
        -- exact Hcandidate_bounds.
        -- reflexivity.
        -- exact Hweight.
        -- exact Hskip_cell.
        -- intros e_abs Hdone.
           eapply forward_star_done_edge_set_step_aux; eauto.
        -- eapply forward_star_current_edge_not_done; eauto.
        -- exact Hstep.
        -- exact Hmath.
Qed.

Lemma dijkstra_heap_edge_phase_relax_neighbor_unvisited :
  forall g vertex_count edge_count src cur_vertex cur_distance edge
         head_values to_values weight_values next_values
         visited_set dist_values queue_set,
    graph_has_size g vertex_count ->
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_index edge_count edge ->
    edge <> -1 ->
    cur_distance + Znth edge weight_values 0 <
      dist_cell dist_values (Znth edge to_values 0) ->
    dijkstra_heap_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values queue_set ->
    dijkstra_heap_edge_phase_state
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values queue_set ->
    ~ visited_set (Znth edge to_values 0).
Proof.
  intros g vertex_count edge_count src cur_vertex cur_distance edge
    head_values to_values weight_values next_values visited_set dist_values
    queue_set Hsize Hmodel Hedge_index Hedge_not_nil Hrelax
    Hedge_state Hphase.
  assert (Hcur_valid : vertex_valid g cur_vertex)
    by (unfold dijkstra_heap_edge_loop_state in Hedge_state; tauto).
  assert (Hhead_edge :
    next_chain next_values (Znth cur_vertex head_values (-1)) edge).
  {
    destruct Hphase as (_ & [(_ & _ & Hcur_src & _ & Hchain & _) |
      (visited_before & base_dist_values & _ & _ & _ & _ & Hchain & _)]).
    - subst cur_vertex.
      destruct Hchain as [Hnil | Hchain]; [contradiction | exact Hchain].
    - destruct Hchain as [Hnil | Hchain]; [contradiction | exact Hchain].
  }
  pose proof
    (forward_star_current_edge_facts
      g vertex_count edge_count head_values to_values weight_values
      next_values cur_vertex edge Hsize Hmodel Hcur_valid Hhead_edge
      Hedge_index)
    as (_Hchain_wf & _Hcur_storage & _Hedge_to & _Hedge_next
        & Hneighbor_valid & _Hneighbor_storage & Hstep & Hweight
        & _Hnext_eq).
  assert (Hcur_dist : dist_cell dist_values cur_vertex = cur_distance)
    by (unfold dijkstra_heap_edge_loop_state in Hedge_state; tauto).
  assert (Hnonneg : nonnegative_edges g)
    by (unfold dijkstra_heap_edge_loop_state,
          dijkstra_heap_loop_state in Hedge_state; tauto).
  destruct Hphase as
    (Hcur_finite &
    [(Hvisited_src & _Hno_overflow & Hcur_src & Hcur_zero & _ & _Hfirst) |
     (visited_before & base_dist_values & _Hvisited_valid & _Hno_overflow
      & Hvisit_add & Hcur_base & _ & Hmath)]).
  - subst cur_vertex cur_distance.
    intro Hvisited_neighbor.
    apply Hvisited_src in Hvisited_neighbor.
    subst.
    rewrite Hcur_dist in Hrelax.
    pose proof
      (forward_star_model_edge_bounds _ _ _ _ _ _ _ Hmodel Hedge_index)
      as (_ & _ & Hweight_bounds & _).
    lia.
  - intro Hvisited_after.
    unfold visited_set_add in Hvisit_add.
    destruct (proj1 (Hvisit_add (Znth edge to_values 0)) Hvisited_after)
      as [Hvisited_before | Hneighbor_cur].
    + assert (Hneighbor_ne_cur : Znth edge to_values 0 <> cur_vertex)
        by (intro Hsame; subst;
            eapply DijkstraGraph_step_aux_no_self;
            eauto using forward_star_model_graph_wf).
      pose proof
        (fun e_abs Hdone =>
          forward_star_done_edge_set_step_aux
            g edge_count head_values to_values weight_values next_values
            cur_vertex edge e_abs Hmodel Hcur_valid Hdone) as Hdone_subset.
      pose proof
        (dijkstra_edge_math_state_no_done_target_dist_base
          g src visited_before visited_set cur_vertex base_dist_values
          (forward_star_done_edge_set
            head_values to_values weight_values next_values cur_vertex edge)
          dist_values (cur_vertex, Znth edge to_values 0)
          (Znth edge to_values 0)
          Hdone_subset
          ltac:(apply forward_star_current_edge_not_done; auto)
          Hneighbor_ne_cur Hstep Hmath) as Hdist_base.
      rewrite dijkstra_array_state_dist_valid in Hdist_base
        by exact Hneighbor_valid.
      unfold dijkstra_after_visit_state, set_state_visited,
        dijkstra_array_state in Hdist_base.
      simpl in Hdist_base.
      destruct (vertex_valid_dec g (Znth edge to_values 0))
        as [_ | Hinvalid_neighbor]; [| contradiction].
      unfold dijkstra_edge_math_state in Hmath.
      destruct Hmath as (_ & Hmath_before & Hselected & _).
      pose proof
        (dijkstra_math_invariant_no_relax_to_old_visited
          g vertex_count src visited_before base_dist_values
          cur_vertex (Znth edge to_values 0)
          (cur_vertex, Znth edge to_values 0)
          Hsize Hnonneg Hcur_valid Hneighbor_valid Hmath_before
          Hselected Hvisited_before Hstep) as Hold_le_candidate.
      rewrite <- Hcur_base in Hold_le_candidate.
      rewrite (cell_as_distance_finite cur_distance) in Hold_le_candidate
        by exact Hcur_finite.
      rewrite Hweight in Hold_le_candidate.
      simpl in Hold_le_candidate.
      rewrite <- Hdist_base in Hold_le_candidate.
      unfold cell_as_distance, DijkstraGraph.cell_as_distance, Z_op_le
        in Hold_le_candidate.
      destruct (Z.eq_dec
        (dist_cell dist_values (Znth edge to_values 0))
        DijkstraGraph.infinity);
      [contradiction | lia].
    + rewrite Hneighbor_cur in Hrelax.
      rewrite Hcur_dist in Hrelax.
      pose proof
        (forward_star_model_edge_bounds _ _ _ _ _ _ _ Hmodel Hedge_index)
        as (_ & _ & Hweight_bounds & _).
      lia.
Qed.

Lemma dijkstra_heap_edge_loop_refines_relax_to_after_relax :
  forall g vertex_count edge_count src cur_vertex cur_distance edge neighbor
         edge_weight candidate
         head_values to_values weight_values next_values visited_set dist_values
         queue_set X,
    graph_has_size g vertex_count ->
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_index edge_count edge ->
    dijkstra_heap_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values queue_set ->
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
    dijkstra_heap_edge_loop_refines
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values queue_set X ->
    dijkstra_heap_after_relax_refines
      g src cur_vertex cur_distance edge neighbor candidate
      head_values to_values weight_values next_values
      visited_set (replace_Znth neighbor candidate dist_values) queue_set X.
Proof.
  intros g vertex_count edge_count src cur_vertex cur_distance edge neighbor
    edge_weight candidate head_values to_values weight_values next_values
    visited_set dist_values queue_set X Hsize Hmodel Hedge_index
    Hedge_state Hedge_not_nil Hneighbor Hweight Hcandidate Hvalid Hstorage
    Hcandidate_bounds Hweight_nonneg
    Hoverflow Hrelax Hrefines.
  subst neighbor edge_weight candidate.
  unfold dijkstra_heap_edge_loop_refines in Hrefines.
  destruct Hrefines as (Hrefines & Hcap & Hheap_refines & Hphase).
  assert (Hunvisited : ~ visited_set (Znth edge to_values 0))
    by (eapply dijkstra_heap_edge_phase_relax_neighbor_unvisited; eauto).
  eapply safeExec_proequiv in Hrefines.
  2: {
    apply dijkstra_heap_lfs_edge_loop_cont_unfold.
  }
  unfold dijkstra_heap_lfs_edge_body in Hrefines.
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
    intros s Hstate_model.
    do 2 (split; [eassumption |]).
    erewrite graph_state_model_dist_cell by eauto.
    exact Hrelax.
  }
  lfs_prog_nf Hrefines.
  apply safeExec_update'_bind in Hrefines.
  lfs_prog_nf Hrefines.
  unfold dijkstra_heap_lfs_edge_loop_after_body_cont in Hrefines.
  change (safeExec
    (fun s : state =>
       exists s0 : state,
         s = set_state_distance (Znth edge to_values 0)
               (cur_distance + Znth edge weight_values 0) s0 /\
         graph_state_model g visited_set dist_values s0)
    (queue_set_after <-
       index_queue_push_choice queue_set (Znth edge to_values 0)
         (cur_distance + Znth edge weight_values 0);;
     dijkstra_heap_lfs_edge_loop_cont head_values to_values weight_values
       next_values cur_vertex cur_distance (Znth edge next_values 0)
       queue_set_after)
    X) in Hrefines.
  unfold dijkstra_heap_after_relax_refines.
  split.
  - eapply safeExec_conseq.
    + exact Hrefines.
    + intros s (s0 & Hs & Hstate_model).
      subst s.
      eapply graph_state_model_replace_Znth_set_state_distance; eauto.
  - split; [exact Hcap |].
    intros queue_set_after Hpush.
    assert (Hshape_old : vector_shape dist_values)
      by (unfold dijkstra_heap_edge_loop_state,
            dijkstra_heap_loop_state in Hedge_state; tauto).
    assert (Hitems_valid : heap_queue_items_valid g queue_set)
      by (unfold dijkstra_heap_edge_loop_state,
            dijkstra_heap_loop_state in Hedge_state; tauto).
    split.
    + eapply heap_queue_refines_unvisited_dist_relax_push.
      * exact Hsize.
      * exact Hshape_old.
      * exact Hstorage.
      * exact Hunvisited.
      * exact Hrelax.
      * lia.
      * exact Hitems_valid.
      * exact Hheap_refines.
      * exact Hpush.
    + eapply (dijkstra_heap_edge_phase_relax_update
        g vertex_count edge_count src cur_vertex cur_distance edge
        (Znth edge to_values 0) (Znth edge weight_values 0)
        (cur_distance + Znth edge weight_values 0)
        head_values to_values weight_values next_values
        visited_set dist_values queue_set); eauto.
Qed.

Lemma dijkstra_heap_edge_loop_refines_after_body :
  forall g src cur_vertex cur_distance edge
         head_values to_values weight_values next_values
         visited_set dist_values queue_set X result Q,
    graph_state_model g visited_set dist_values -@
      dijkstra_heap_lfs_edge_body
        head_values to_values weight_values next_values
        cur_vertex cur_distance (edge, queue_set)
      -⥅ Q ♯ result ->
    dijkstra_heap_edge_loop_refines
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values queue_set X ->
    safeExec Q
      (dijkstra_heap_lfs_edge_loop_after_body_cont
        head_values to_values weight_values next_values
        cur_vertex cur_distance result)
      X.
Proof.
  intros g src cur_vertex cur_distance edge
    head_values to_values weight_values next_values
    visited_set dist_values queue_set X result Q Hbody Hrefines.
  unfold dijkstra_heap_edge_loop_refines in Hrefines.
  destruct Hrefines as (Hrefines & _Hcap & _Hheap).
  eapply highstepbind_derive; eauto.
  eapply safeExec_proequiv.
  - apply dijkstra_heap_lfs_edge_loop_cont_unfold.
  - exact Hrefines.
Qed.

Lemma dijkstra_heap_edge_loop_refines_no_relax_to_next :
  forall g edge_count src cur_vertex cur_distance edge neighbor edge_weight
         head_values to_values weight_values next_values visited_set dist_values
         queue_set X,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_index edge_count edge ->
    dijkstra_heap_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values queue_set ->
    edge <> -1 ->
    neighbor = Znth edge to_values 0 ->
    edge_weight = Znth edge weight_values 0 ->
    vertex_valid g neighbor ->
    (edge_weight < 0 \/
      cur_distance > DijkstraGraph.infinity - edge_weight \/
      cur_distance + edge_weight >= dist_cell dist_values neighbor) ->
    dijkstra_heap_edge_loop_refines
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values queue_set X ->
    dijkstra_heap_edge_loop_refines
      g src cur_vertex cur_distance (Znth edge next_values 0)
      head_values to_values weight_values next_values
      visited_set dist_values queue_set X.
Proof.
  intros g edge_count src cur_vertex cur_distance edge neighbor edge_weight
    head_values to_values weight_values next_values visited_set dist_values
    queue_set X Hmodel Hedge_index Hedge_state Hedge_not_nil Hneighbor
    Hweight Hvalid Hskip Hrefines.
  subst neighbor edge_weight.
  pose proof Hrefines as Hrefines_full.
  unfold dijkstra_heap_edge_loop_refines in Hrefines_full.
  destruct Hrefines_full as
    (Hrefines_safe & Hcap & Hheap_refines & Hphase).
  assert (Hbody_step :
    graph_state_model g visited_set dist_values -@
      dijkstra_heap_lfs_edge_body
        head_values to_values weight_values next_values
        cur_vertex cur_distance (edge, queue_set)
      -⥅ graph_state_model g visited_set dist_values
      ♯ by_continue (Znth edge next_values 0, queue_set)).
  {
    unfold dijkstra_heap_lfs_edge_body.
    apply hsevalchoice_right_derive.
    eapply hsevalbind_derive'.
    + apply hs_eval_assume_state.
      intros s _.
      exact Hedge_not_nil.
    + apply hsevalchoice_right_derive.
      eapply hsevalbind_derive'.
      * apply hs_eval_assume_state.
        intros s Hstate_model.
        destruct Hskip as [Hskip | [Hskip | Hskip]].
        -- left. exact Hskip.
        -- right. left. exact Hskip.
        -- right. right.
           erewrite graph_state_model_dist_cell by eauto.
           exact Hskip.
      * apply highret_eval2.
  }
  unfold dijkstra_heap_edge_loop_refines, dijkstra_heap_lfs_edge_loop_cont,
    dijkstra_heap_lfs_edge_loop.
  split.
  - change (safeExec (graph_state_model g visited_set dist_values)
    (dijkstra_heap_lfs_edge_loop_after_body_cont head_values to_values
      weight_values next_values cur_vertex cur_distance
      (by_continue (Znth edge next_values 0, queue_set))) X).
    eapply dijkstra_heap_edge_loop_refines_after_body; eauto.
  - split.
    + pose proof
        (forward_star_model_edge_safe _ _ _ _ _ _ Hmodel)
        as (_ & _ & Hnext_len & _).
      pose proof
        (forward_star_model_next_case_0 _ _ _ _ _ _ _ Hmodel Hedge_index)
        as Hnext_case.
      eapply heap_queue_edge_capacity_state_no_push_step; eauto.
      * unfold edge_index in Hedge_index. lia.
      * destruct Hnext_case as [Hnext_nil | Hnext_edge].
        -- left; exact Hnext_nil.
        -- right.
           unfold edge_index in Hnext_edge.
           rewrite Hnext_len.
           exact Hnext_edge.
    + split; [exact Hheap_refines |].
      eapply dijkstra_heap_edge_phase_skip_update; eauto.
Qed.

Lemma dijkstra_min_epath_in_vset_equiv :
  forall g src v S1 S2 z,
    Sets.equiv S1 S2 ->
    dijkstra_min_epath_in_vset g src v S1 z ->
    dijkstra_min_epath_in_vset g src v S2 z.
Proof.
  intros g src v S1 S2 z Hequiv Hmin.
  pose proof
    (@min_value_weight_epath_in_vset_Proper
      DijkstraGraph.G DijkstraGraph.V DijkstraGraph.E
      DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance
      DijkstraGraph.PathData DijkstraGraph.path_instance
      DijkstraGraph.weight_instance) as Hproper.
  unfold Proper, respectful in Hproper.
  specialize (Hproper g g eq_refl src src eq_refl v v eq_refl
    S1 S2 Hequiv z z eq_refl).
  apply Hproper.
  exact Hmin.
Qed.

Lemma dijkstra_math_invariant_source_visited_equiv :
  forall g src visited_set dist_values,
    (forall v, visited_set v <-> v = src) ->
    dijkstra_math_invariant g src (source_visited_set src) dist_values ->
    dijkstra_math_invariant g src visited_set dist_values.
Proof.
  intros g src visited_set dist_values Hvisited_src Hmath.
  assert (Hvisited_equiv :
    Sets.equiv
      (@visited Z (dijkstra_array_state g visited_set dist_values))
      (@visited Z
        (dijkstra_array_state g (source_visited_set src) dist_values))).
  {
    intros v.
    unfold dijkstra_array_state, source_visited_set.
    simpl.
    split.
    - intros [Hvalid Hv].
      split; [exact Hvalid |].
      apply Hvisited_src; exact Hv.
    - intros [Hvalid Hv].
      split; [exact Hvalid |].
      apply Hvisited_src; exact Hv.
  }
  assert (Hdist_eq : forall v,
    @dist Z (dijkstra_array_state g visited_set dist_values) v =
    @dist Z (dijkstra_array_state g (source_visited_set src) dist_values) v).
  {
    intro v.
    unfold dijkstra_array_state.
    simpl.
    reflexivity.
  }
  unfold dijkstra_math_invariant in *.
  destruct Hmath as (Hfinal & Hoptimal & Hle).
  split.
  - intros v Hv.
    pose proof (Hfinal v (proj1 (Hvisited_equiv v) Hv))
      as (Hmin & Hmin_set).
    rewrite Hdist_eq.
    split; [exact Hmin |].
    eapply dijkstra_min_epath_in_vset_equiv.
    + intro x; symmetry; apply Hvisited_equiv.
    + exact Hmin_set.
  - split.
    + intros v Hunvisited.
      assert (~ @visited Z
        (dijkstra_array_state g (source_visited_set src) dist_values) v)
        as Hunvisited_src
        by (intro Hv; apply Hunvisited; apply (proj2 (Hvisited_equiv v)); exact Hv).
      pose proof (Hoptimal v Hunvisited_src) as Hmin_set.
      rewrite Hdist_eq.
      eapply dijkstra_min_epath_in_vset_equiv.
      * intro x; symmetry; apply Hvisited_equiv.
      * exact Hmin_set.
    + intros u v Hu Hv.
      rewrite !Hdist_eq.
      apply Hle.
      * apply (proj1 (Hvisited_equiv u)); exact Hu.
      * intro Hv_src.
        apply Hv.
        apply (proj2 (Hvisited_equiv v)); exact Hv_src.
Qed.

Lemma dijkstra_heap_edge_phase_finish_to_loop_phase :
  forall g edge_count src cur_vertex cur_distance edge
         head_values to_values weight_values next_values
         visited_set dist_values queue_set,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge = -1 ->
    dijkstra_heap_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values queue_set ->
    dijkstra_heap_edge_phase_state
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values queue_set ->
    dijkstra_heap_loop_phase_state g src visited_set dist_values queue_set.
Proof.
  intros g edge_count src cur_vertex cur_distance edge head_values to_values
    weight_values next_values visited_set dist_values queue_set
    Hmodel Hedge_nil Hedge_state Hphase.
  unfold dijkstra_heap_edge_loop_state in Hedge_state.
  destruct Hedge_state as (Hloop_state & Hcur_valid & _Hcur_dist & _).
  unfold dijkstra_heap_loop_state in Hloop_state.
  destruct Hloop_state as (Hwf & Hsrc_valid & Hnonneg & _).
  destruct Hphase as
    (_Hcur_finite &
    [(Hvisited_src & Hno_overflow & Hcur_src & _ & _ & Hfirst) |
     (visited_before & base_dist_values & Hvisited_valid & Hno_overflow
      & Hvisit_add & _ & _ & Hmath)]).
  - right.
    subst cur_vertex.
    split.
    + unfold visited_set_valid.
      intros v Hv.
      apply Hvisited_src in Hv.
      subst v; exact Hsrc_valid.
    + split; [exact Hno_overflow |].
      eapply dijkstra_math_invariant_source_visited_equiv.
      * exact Hvisited_src.
      * eapply dijkstra_first_step_full_done_to_math; eauto.
        eapply dijkstra_first_step_math_state_done_equiv.
        -- intros e_abs.
           subst edge.
           eapply forward_star_done_edge_set_minus_one_equiv_step_aux;
             eauto.
        -- exact Hfirst.
  - right.
    split.
    + unfold visited_set_valid.
      intros v Hv.
      unfold visited_set_add in Hvisit_add.
      destruct (proj1 (Hvisit_add v) Hv) as [Hv_before | ->].
      * apply Hvisited_valid; exact Hv_before.
      * exact Hcur_valid.
    + split; [exact Hno_overflow |].
      eapply dijkstra_edge_math_state_full_done_to_math; eauto.
      intros e_abs.
      subst edge.
      eapply forward_star_done_edge_set_minus_one_equiv_step_aux; eauto.
Qed.

Lemma dijkstra_heap_edge_loop_refines_break_to_loop :
  forall g edge_count src cur_vertex cur_distance edge
         head_values to_values weight_values next_values visited_set dist_values
         queue_set X,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    dijkstra_heap_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values queue_set ->
    edge = -1 ->
    dijkstra_heap_edge_loop_refines
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values queue_set X ->
    dijkstra_heap_loop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values queue_set X.
Proof.
  intros g edge_count src cur_vertex cur_distance edge
    head_values to_values weight_values next_values visited_set dist_values
    queue_set X Hmodel Hedge_state Hedge_nil Hrefines.
  pose proof Hrefines as Hrefines_full.
  unfold dijkstra_heap_edge_loop_refines in Hrefines_full.
  destruct Hrefines_full as (_Hrefines_safe & Hcap & Hheap_refines & Hphase).
  assert (Hbody_step :
    graph_state_model g visited_set dist_values -@
      dijkstra_heap_lfs_edge_body
        head_values to_values weight_values next_values
        cur_vertex cur_distance (edge, queue_set)
      -⥅ graph_state_model g visited_set dist_values
      ♯ by_break queue_set).
  {
    unfold dijkstra_heap_lfs_edge_body.
    apply hsevalchoice_left_derive.
    eapply hsevalbind_derive'.
    + apply hs_eval_assume_state.
      intros s _.
      exact Hedge_nil.
    + apply highret_eval2.
  }
  unfold dijkstra_heap_loop_refines.
  split.
  - eapply safeExec_proequiv.
    2: { eapply dijkstra_heap_edge_loop_refines_after_body; eauto. }
    unfold dijkstra_heap_lfs_edge_loop_after_body_cont.
    rewrite ret_equiv.
    reflexivity.
  - split.
    + eapply heap_queue_edge_capacity_state_to_loop; eauto.
    + split; [exact Hheap_refines |].
      eapply dijkstra_heap_edge_phase_finish_to_loop_phase; eauto.
Qed.

Lemma store_heap_zero_empty :
  forall key data queue_set,
    store_heap key data queue_set 0 |--
      “ mlist queue_set = nil ” &&
      store_heap key data queue_set 0.
Proof.
  intros key data queue_set.
  unfold store_heap at 1.
  Intros key_values.
  Intros data_values.
  match goal with
  | Hrep : heap_representation queue_set key_values data_values 0 |- _ =>
      pose proof Hrep as Hrep_keep;
      assert (Hempty : mlist queue_set = nil) by
        (unfold heap_representation in Hrep;
         destruct Hrep as (_ & _ & Hsize & _);
         unfold multiset_size in Hsize;
         apply Zlength_nil_inv; lia)
  end.
  split_pure_spatial.
  - unfold store_heap.
    Exists key_values data_values.
    split_pure_spatial.
    + cancel (IntArray.full key 0 key_values).
      cancel (heap_tail key 0).
      cancel (IntArray.full data 0 data_values).
      cancel (heap_tail data 0).
    + split_pures; dump_pre_spatial; exact Hrep_keep.
  - dump_pre_spatial; exact Hempty.
Qed.

Lemma store_heap_size_eq :
  forall key data queue_set size,
    store_heap key data queue_set size |--
      “ multiset_size queue_set = size ” &&
      store_heap key data queue_set size.
Proof.
  intros key data queue_set size.
  unfold store_heap at 1.
  Intros key_values.
  Intros data_values.
  match goal with
  | Hrep : heap_representation queue_set key_values data_values size |- _ =>
      pose proof Hrep as Hrep_keep;
      assert (Hsize : multiset_size queue_set = size) by
        (unfold heap_representation in Hrep; tauto)
  end.
  split_pure_spatial.
  - unfold store_heap.
    Exists key_values data_values.
    split_pure_spatial.
    + cancel (IntArray.full key size key_values).
      cancel (heap_tail key size).
      cancel (IntArray.full data size data_values).
      cancel (heap_tail data size).
    + split_pures; dump_pre_spatial; exact Hrep_keep.
  - dump_pre_spatial; exact Hsize.
Qed.

Definition dijkstra_heap_loop_math_bridge_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (queue_set : multiset (Z * Z)) : Prop :=
  dijkstra_heap_loop_bridge_state g src visited_set dist_values queue_set /\
  visited_set_valid g visited_set /\
  dijkstra_math_invariant g src visited_set dist_values.

Definition dijkstra_heap_edge_loop_math_bridge_state
    (g : DijkstraGraph.G) (src : Z)
    (visited_before visited_after : Z -> Prop)
    (cur_vertex cur_distance edge : Z)
    (base_dist_values dist_values : list Z)
    (queue_set : multiset (Z * Z))
    (head_values to_values weight_values next_values : list Z) : Prop :=
  dijkstra_heap_edge_loop_bridge_state
    g src visited_after cur_vertex cur_distance edge dist_values queue_set /\
  visited_set_valid g visited_before /\
  visited_set_add visited_before cur_vertex visited_after /\
  cur_distance = dist_cell base_dist_values cur_vertex /\
  (edge = -1 \/ next_chain next_values (Znth cur_vertex head_values (-1)) edge) /\
  dijkstra_edge_math_state g src visited_before visited_after
    cur_vertex base_dist_values
    (forward_star_done_edge_set
      head_values to_values weight_values next_values cur_vertex edge)
    dist_values.

Definition dijkstra_heap_loop_math_model
    (g : DijkstraGraph.G) (src : Z)
    (queue_set : multiset (Z * Z)) (s : state) : Prop :=
  exists visited_set dist_values,
    graph_state_model g visited_set dist_values s /\
    dijkstra_heap_loop_math_bridge_state
      g src visited_set dist_values queue_set.

Definition dijkstra_heap_edge_loop_math_model
    (g : DijkstraGraph.G) (src : Z)
    (visited_before visited_after : Z -> Prop)
    (cur_vertex cur_distance edge : Z)
    (base_dist_values : list Z) (queue_set : multiset (Z * Z))
    (head_values to_values weight_values next_values : list Z)
    (s : state) : Prop :=
  exists dist_values,
    graph_state_model g visited_after dist_values s /\
    0 <= cur_distance < DijkstraGraph.infinity /\
    dijkstra_heap_edge_loop_math_bridge_state
      g src visited_before visited_after cur_vertex cur_distance edge
      base_dist_values dist_values queue_set
      head_values to_values weight_values next_values.

Definition dijkstra_heap_first_edge_loop_math_bridge_state
    (g : DijkstraGraph.G) (src edge : Z)
    (dist_values : list Z) (queue_set : multiset (Z * Z))
    (head_values to_values weight_values next_values : list Z) : Prop :=
  dijkstra_heap_edge_loop_bridge_state
    g src (source_visited_set src) src 0 edge dist_values queue_set /\
  (edge = -1 \/ next_chain next_values (Znth src head_values (-1)) edge) /\
  dijkstra_first_step_math_state
    g src
    (forward_star_done_edge_set
      head_values to_values weight_values next_values src edge)
    dist_values.

Definition dijkstra_heap_first_edge_loop_math_model
    (g : DijkstraGraph.G) (src edge : Z)
    (queue_set : multiset (Z * Z))
    (head_values to_values weight_values next_values : list Z)
    (s : state) : Prop :=
  exists dist_values,
    graph_state_model g (source_visited_set src) dist_values s /\
    dijkstra_heap_first_edge_loop_math_bridge_state
      g src edge dist_values queue_set
      head_values to_values weight_values next_values.

Ltac dijkstra_heap_edge_body_hoare :=
  unfold dijkstra_heap_lfs_edge_body;
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
        | intros queue_set_after;
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

Ltac dijkstra_heap_loop_body_hoare :=
  unfold dijkstra_heap_lfs_loop_body;
  match goal with
  | |- Hoare _ _ ?Post =>
      apply Hoare_choice;
      [ apply Hoare_assume_bind;
        apply Hoare_ret';
        intros s [Hempty Hpre]
      | apply Hoare_assume_bind;
        eapply Hoare_bind;
        [ apply Hoare_get
        | intros [[queue_set_after cur_vertex] cur_distance];
          cbn [fst snd];
          apply Hoare_choice;
          [ apply Hoare_assume_bind;
            eapply Hoare_bind;
            [ apply Hoare_update
            | intros [];
              eapply Hoare_bind
                with (Q := fun queue_set_after_edges s =>
                  Post (by_continue queue_set_after_edges) s);
              [ idtac
              | intros queue_set_after_edges;
                apply Hoare_ret';
                intros s Hloop;
                exact Hloop ] ]
          | apply Hoare_assume_bind;
            apply Hoare_ret';
            intros s [Hneq_dist Hpre];
            destruct Hpre as (Hpop & Hpre);
            destruct Hpre as (Hnonempty & Hpre) ] ] ]
  end.

Ltac pose_dijkstra_heap_edge_loop_current_facts
    edge_count cur_vertex edge head_values next_values
    Hsize Hmodel Hedge_not_nil Hbridge :=
  let Hbridge0 := fresh "Hbridge" in
  let Hedge_bridge0 := fresh "Hedge_bridge" in
  let Hedge_state0 := fresh "Hedge_state" in
  let Hedge_chain0 := fresh "Hedge_chain" in
  pose proof Hbridge as Hbridge0;
  unfold dijkstra_heap_edge_loop_math_bridge_state in Hbridge0;
  destruct Hbridge0 as
    (Hedge_bridge0 & _ & _ & _ & Hedge_chain0 & _);
  unfold dijkstra_heap_edge_loop_bridge_state in Hedge_bridge0;
  destruct Hedge_bridge0 as (Hedge_state0 & _);
  unfold dijkstra_heap_edge_loop_state in Hedge_state0;
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

Lemma index_queue_pop_result_singleton_source :
  forall src queue_set_after cur_vertex cur_distance,
    index_queue_pop_result
      (singleton_source_queue src) queue_set_after cur_vertex cur_distance ->
    queue_set_after = list_to_multiset (@nil (Z * Z)) /\
    cur_vertex = src /\
    cur_distance = 0.
Proof.
  intros src queue_set_after cur_vertex cur_distance Hpop.
  unfold index_queue_pop_result in Hpop.
  destruct Hpop as (popped & Hpopped & Hminimum & Hafter).
  destruct Hminimum as (Hin & _).
  unfold singleton_source_queue, multiset_insert, list_to_multiset in Hin, Hafter.
  simpl in Hin, Hafter.
  destruct Hin as [Hin | Hin]; [| contradiction].
  rewrite <- Hin in Hpopped.
  unfold heap_item in Hpopped.
  inversion Hpopped; subst cur_distance cur_vertex.
  subst queue_set_after.
  unfold multiset_remove, list_to_multiset.
  simpl.
  rewrite <- Hin.
  unfold heap_item.
  destruct (excluded_middle_informative ((0, src) = (0, src))) as [_ | Hneq].
  - repeat split; reflexivity.
  - contradiction Hneq; reflexivity.
Qed.

Section HeapFirstStepProofs.

Context (g : DijkstraGraph.G)
        (vertex_count edge_count src : Z)
        (head_values to_values weight_values next_values : list Z).

Hypothesis Hsize : graph_has_size g vertex_count.
Hypothesis Hsrc : vertex_valid g src.
Hypothesis Hnonneg : nonnegative_edges g.
Hypothesis Hmodel :
  forward_star_model g edge_count
    head_values to_values weight_values next_values.
Hypothesis Hno_overflow :
  shortest_path_relaxation_bounded g src DijkstraGraph.infinity.

Local Notation done_edges :=
  (forward_star_done_edge_set
    head_values to_values weight_values next_values).

Ltac pose_heap_first_edge_current_facts edge dist_values queue_set
    Hedge_not_nil Hbridge :=
  let Hbridge_facts := fresh "Hbridge_facts" in
  let Hedge_bridge_facts := fresh "Hedge_bridge_facts" in
  pose proof Hbridge as Hbridge_facts;
  unfold dijkstra_heap_first_edge_loop_math_bridge_state in Hbridge_facts;
  destruct Hbridge_facts as
    (Hedge_bridge_facts & [? | Hhead_edge] & _);
    [contradiction |];
  assert (Hsrc_valid : vertex_valid g src)
    by (unfold dijkstra_heap_edge_loop_bridge_state,
          dijkstra_heap_edge_loop_state in Hedge_bridge_facts; tauto);
  assert (Hedge_index : edge_index edge_count edge)
    by (eapply forward_star_next_chain_edge_index; eauto);
  pose proof
    (forward_star_current_edge_facts
      _ _ _ _ _ _ _ _ _ Hsize Hmodel Hsrc_valid
      Hhead_edge Hedge_index)
    as (Hchain_wf & Hsrc_storage & Hedge_to & Hedge_next
        & Hneighbor_valid & Hneighbor_storage
        & Hcurrent_step & Hcurrent_weight & Hnext_eq).

Ltac solve_heap_first_edge_candidate_bounds
    edge Hsrc_valid Hneighbor_valid Hcurrent_step Hcurrent_weight :=
  simpl in Hcurrent_weight;
  apply (Hno_overflow src (Znth edge to_values 0)
    (src, Znth edge to_values 0) 0
    (Znth edge weight_values 0));
  [exact Hsrc_valid | exact Hneighbor_valid | exact Hcurrent_step
  | dijkstra_min_epath_refl | exact Hcurrent_weight].

Ltac solve_heap_forward_star_done_step :=
  intros e_abs; symmetry;
  apply forward_star_done_edge_set_step_0; auto;
  try (eapply forward_star_model_chain_wf; eauto).

Ltac heap_first_edge_done_equiv edge dist_values :=
  eapply (dijkstra_first_step_math_state_done_equiv
    g src
    (fun e_abs =>
      done_edges src edge e_abs \/
      e_abs = (src, Znth edge to_values 0))
    (done_edges src (Znth edge next_values 0))
    dist_values);
  [ solve_heap_forward_star_done_step
  | unfold dijkstra_first_step_math_state in * ].

Ltac solve_heap_forward_star_done_subset :=
  intros e_abs Hdone;
  eapply forward_star_done_edge_set_step_aux; eauto.

Ltac solve_heap_current_edge_add_side_condition :=
  solve [ solve_heap_forward_star_done_subset
        | apply forward_star_current_edge_not_done; auto
        | reflexivity ].

Lemma initial_heap_first_edge_loop_math_model :
    dijkstra_heap_first_edge_loop_math_model
      g src (Znth src head_values 0)
      (list_to_multiset (@nil (Z * Z)))
      head_values to_values weight_values next_values
      (set_state_visited src (initial_state src)).
Proof.
  pose proof
    (graph_has_size_vertex_valid_bounds
      g vertex_count src Hsize Hsrc) as (Hcount & Hsrc_bounds).
  pose proof
    (graph_has_size_vertex_valid_storage g vertex_count src Hsize Hsrc)
    as Hsrc_storage.
  unfold dijkstra_heap_first_edge_loop_math_model.
  exists (initial_dist_values src).
  split.
  - apply graph_state_model_visit_state
      with (visited_set := fun _ : Z => False).
    + exact Hsrc.
    + unfold visited_set_add, source_visited_set; tauto.
    + apply dijkstra_init_dist_graph_state_model_initial
        with (vertex_count := vertex_count).
      * exact Hsize.
      * unfold visited_set_empty; tauto.
      * apply initial_dist_values_init; auto.
  - unfold dijkstra_heap_first_edge_loop_math_bridge_state.
    split.
    + eapply dijkstra_heap_after_pop_bridge_state_equal_to_edge_bridge
        with (visited_before := fun _ : Z => False)
             (queue_set_before := singleton_source_queue src).
      * exact Hsrc.
      * unfold visited_set_add, source_visited_set; tauto.
      * rewrite initial_dist_values_cell by exact Hsrc_storage.
        destruct (Z.eq_dec src src); [reflexivity | contradiction].
      * eapply forward_star_head_0_lower_bound; eauto.
      * unfold dijkstra_heap_after_pop_bridge_state.
        split.
        -- unfold dijkstra_heap_loop_state.
           split; [eapply forward_star_model_graph_wf; eauto |].
           split; [exact Hsrc |].
           split; [exact Hnonneg |].
           split; [apply initial_dist_values_shape; exact Hsrc_storage |].
           split; [apply initial_dist_values_safe; exact Hsrc_storage |].
           unfold heap_queue_items_valid, list_to_multiset.
           intros item Hin; contradiction.
        -- split.
           ++ unfold heap_queue_refines_unvisited_dist,
                priority_queue_refines_unvisited_dist,
                singleton_source_queue, multiset_insert, list_to_multiset.
              simpl.
              repeat split.
              ** intros v Hvalid _ Hfinite.
                 pose proof
                   (graph_has_size_vertex_valid_storage
                     g vertex_count v Hsize Hvalid) as Hv_storage.
                 rewrite initial_dist_values_cell by auto.
                 rewrite initial_dist_values_cell in Hfinite by auto.
                 destruct (Z.eq_dec v src) as [Heq | Hneq].
                 --- subst; simpl; auto.
                 --- unfold DijkstraGraph.infinity in Hfinite; lia.
              ** intros d v Hin _.
                 tauto.
              ** intros d v Hin.
                 destruct Hin as [Hin | []].
                 inversion Hin; subst d v.
                 rewrite initial_dist_values_cell by auto.
                 destruct (Z.eq_dec src src); [lia | contradiction].
              ** intros d v Hin.
                 destruct Hin as [Hin | []].
                 inversion Hin; subst d v.
                 unfold DijkstraGraph.infinity; lia.
              ** constructor; [intro H; contradiction | constructor].
           ++ unfold index_queue_pop_result.
              exists (heap_item 0 src).
              split; [reflexivity |].
              split.
              ** unfold multiset_minimum.
                 split.
                 --- unfold singleton_source_queue, multiset_insert,
                       list_to_multiset; simpl; auto.
                 --- unfold singleton_source_queue, multiset_insert,
                       list_to_multiset; simpl; intros x Hx.
                     destruct Hx as [<- | []]; simpl; lia.
              ** unfold singleton_source_queue, multiset_insert,
                   list_to_multiset, multiset_remove.
                 simpl.
                 unfold heap_item.
                 destruct (excluded_middle_informative ((0, src) = (0, src)))
                   as [_ | Hneq]; [reflexivity | contradiction Hneq; reflexivity].
    + split.
      * eapply forward_star_head_0_nil_or_chain; eauto.
      * eapply dijkstra_first_step_math_state_done_equiv.
        -- intros e_abs.
           symmetry.
           eapply forward_star_done_edge_set_head_empty_equiv; eauto.
        -- apply initial_first_step_math_state_empty
             with (vertex_count := vertex_count); auto.
Qed.

Lemma dijkstra_heap_lfs_first_edge_body_math_step :
  forall edge queue_set,
    Hoare
      (dijkstra_heap_first_edge_loop_math_model
        g src edge queue_set
        head_values to_values weight_values next_values)
      (dijkstra_heap_lfs_edge_body
        head_values to_values weight_values next_values
        src 0 (edge, queue_set))
      (fun result s =>
        match result with
        | by_continue acc =>
            dijkstra_heap_first_edge_loop_math_model
              g src (fst acc) (snd acc)
              head_values to_values weight_values next_values s
        | by_break queue_set_done =>
            dijkstra_heap_loop_math_model g src queue_set_done s
        end).
Proof.
  intros edge queue_set.
  dijkstra_heap_edge_body_hoare.
  - subst edge.
    unfold dijkstra_heap_first_edge_loop_math_model in Hpre.
    destruct Hpre as (dist_values & Hstate & Hbridge).
    assert (Hsrc_valid : vertex_valid g src)
      by (unfold dijkstra_heap_first_edge_loop_math_bridge_state,
          dijkstra_heap_edge_loop_bridge_state,
          dijkstra_heap_edge_loop_state in Hbridge; tauto).
    unfold dijkstra_heap_loop_math_model.
    exists (source_visited_set src), dist_values.
    split; [exact Hstate |].
    unfold dijkstra_heap_first_edge_loop_math_bridge_state in Hbridge.
    destruct Hbridge as (Hedge_bridge & _ & Hfirst).
    unfold dijkstra_heap_loop_math_bridge_state.
    split.
    + eapply dijkstra_heap_edge_loop_bridge_to_loop_bridge; eauto.
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
  - destruct Hrelax_assume as (Hweight_nonneg & _ & Hrelax_state).
    unfold dijkstra_heap_first_edge_loop_math_model in Hpre.
    destruct Hpre as (dist_values & Hstate & Hbridge).
    pose_heap_first_edge_current_facts edge dist_values queue_set
      Hedge_not_nil Hbridge.
    unfold dijkstra_heap_first_edge_loop_math_bridge_state in Hbridge.
    destruct Hbridge as (Hedge_bridge & Hedge_chain & Hfirst).
    assert (Hcandidate_bounds :
      0 <= 0 + Znth edge weight_values 0 < DijkstraGraph.infinity)
      by (solve_heap_first_edge_candidate_bounds
        edge Hsrc_valid Hneighbor_valid Hcurrent_step Hcurrent_weight).
    erewrite graph_state_model_dist_cell in Hrelax_state by eauto.
    pose proof Hstate as ((Hshape & Hsafe & _) & _).
    assert (Hneighbor_unvisited :
      ~ source_visited_set src (Znth edge to_values 0)).
    {
      unfold source_visited_set; intro Hsame; subst.
      unfold dijkstra_heap_edge_loop_bridge_state,
        dijkstra_heap_edge_loop_state in Hedge_bridge.
      destruct Hedge_bridge as ((_ & _ & Hsrc_dist & _) & _).
      rewrite Hsrc_dist in Hrelax_state; lia.
    }
    unfold dijkstra_heap_first_edge_loop_math_model.
    exists (replace_Znth (Znth edge to_values 0)
             (0 + Znth edge weight_values 0) dist_values).
    split.
    + eapply graph_state_model_replace_Znth_set_state_distance; eauto.
    + unfold dijkstra_heap_first_edge_loop_math_bridge_state.
      split.
      * eapply dijkstra_heap_edge_loop_bridge_relax_update_push_result;
          eauto using forward_star_next_0_lower_bound; reflexivity.
      * split.
        -- eapply forward_star_next_0_nil_or_chain; eauto.
        -- heap_first_edge_done_equiv edge
             (replace_Znth (Znth edge to_values 0)
               (0 + Znth edge weight_values 0) dist_values).
           eapply dijkstra_first_step_invariant_add_edge;
             eauto;
             try solve_heap_current_edge_add_side_condition.
           ++ erewrite dijkstra_array_state_dist_replace_other
                by (eauto; lia).
              reflexivity.
           ++ erewrite dijkstra_array_state_dist_replace_same by eauto.
              rewrite Hcurrent_weight.
              replace (0 + Znth edge weight_values 0)
                with (Znth edge weight_values 0) by lia.
              reflexivity.
           ++ intros v Hneq_neighbor.
              erewrite dijkstra_array_state_dist_replace_other by eauto.
              reflexivity.
  - unfold dijkstra_heap_first_edge_loop_math_model in Hpre.
    destruct Hpre as (dist_values & Hstate & Hbridge).
    pose_heap_first_edge_current_facts edge dist_values queue_set
      Hedge_not_nil Hbridge.
    unfold dijkstra_heap_first_edge_loop_math_bridge_state in Hbridge.
    destruct Hbridge as (Hedge_bridge & Hedge_chain & Hfirst).
    assert (Hcandidate_bounds :
      0 <= 0 + Znth edge weight_values 0 < DijkstraGraph.infinity)
      by (solve_heap_first_edge_candidate_bounds
        edge Hsrc_valid Hneighbor_valid Hcurrent_step Hcurrent_weight).
    assert (Hskip_cell :
      dist_cell dist_values (Znth edge to_values 0) <=
        0 + Znth edge weight_values 0)
      by (eapply dijkstra_skip_assume_to_dist_cell; eauto).
    unfold dijkstra_heap_first_edge_loop_math_model.
    exists dist_values.
    split; [exact Hstate |].
    unfold dijkstra_heap_first_edge_loop_math_bridge_state.
    split.
    + eapply dijkstra_heap_edge_loop_bridge_next;
        eauto using forward_star_next_0_lower_bound.
    + split.
      * eapply forward_star_next_0_nil_or_chain; eauto.
      * heap_first_edge_done_equiv edge dist_values.
        pose proof Hfirst as Hfirst_cut.
        unfold Dijkstra.first_step_invariant in Hfirst_cut.
        destruct Hfirst_cut as (_ & _ & _ & Hcut).
        assert (Hneighbor_ne_src : Znth edge to_values 0 <> src)
          by (intro Heq; subst;
              eapply DijkstraGraph_step_aux_no_self;
              eauto using forward_star_model_graph_wf).
        eapply dijkstra_first_step_invariant_add_edge;
          eauto;
          try solve_heap_current_edge_add_side_condition.
        exfalso.
        assert (Hno_old :
          forall e_abs,
            done_edges src edge e_abs ->
            ~ dijkstra_step_aux g e_abs src (Znth edge to_values 0)).
        { eapply dijkstra_done_no_same_target; eauto.
          - solve_heap_forward_star_done_subset.
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

End HeapFirstStepProofs.

Lemma dijkstra_heap_loop_math_model_empty_canonical :
  forall g src queue_set s,
    mlist queue_set = nil ->
    dijkstra_heap_loop_math_model g src queue_set s ->
    dijkstra_heap_loop_math_model
      g src (list_to_multiset (@nil (Z * Z))) s.
Proof.
  intros g src queue_set s Hempty Hmodel.
  unfold dijkstra_heap_loop_math_model in *.
  destruct Hmodel as (visited_set & dist_values & Hstate & Hbridge_math).
  exists visited_set, dist_values.
  split; [exact Hstate |].
  unfold dijkstra_heap_loop_math_bridge_state in *.
  destruct Hbridge_math as (Hbridge & Hvisited & Hmath).
  split.
  - unfold dijkstra_heap_loop_bridge_state in *.
    destruct Hbridge as (Hloop & Hrefines).
    split.
    + unfold dijkstra_heap_loop_state in *.
      destruct Hloop as (Hwf & Hsrc & Hnonneg & Hshape & Hsafe & Hvalid).
      split; [exact Hwf |].
      split; [exact Hsrc |].
      split; [exact Hnonneg |].
      split; [exact Hshape |].
      split; [exact Hsafe |].
      unfold heap_queue_items_valid in *.
      intros item Hin.
      unfold list_to_multiset in Hin; simpl in Hin; contradiction.
    + unfold heap_queue_refines_unvisited_dist in *.
      unfold priority_queue_refines_unvisited_dist in *.
      rewrite Hempty in Hrefines.
      exact Hrefines.
  - split; assumption.
Qed.

Section HeapLoopMathProofs.

Context (g : DijkstraGraph.G)
        (vertex_count edge_count src : Z)
        (head_values to_values weight_values next_values : list Z).

Hypothesis Hsize : graph_has_size g vertex_count.
Hypothesis Hnonneg : nonnegative_edges g.
Hypothesis Hmodel :
  forward_star_model g edge_count
    head_values to_values weight_values next_values.
Hypothesis Hno_overflow :
  shortest_path_relaxation_bounded g src DijkstraGraph.infinity.

Local Notation done_edges :=
  (forward_star_done_edge_set
    head_values to_values weight_values next_values).

Ltac solve_heap_forward_star_done_step :=
  intros e_abs; symmetry;
  apply forward_star_done_edge_set_step_0; auto;
  try (eapply forward_star_model_chain_wf; eauto).

Ltac solve_heap_forward_star_done_subset :=
  intros e_abs Hdone;
  eapply forward_star_done_edge_set_step_aux; eauto.

Ltac finish_heap_edge_math_done lemma :=
  cbn [fst snd];
  eapply dijkstra_edge_math_state_done_equiv;
  [ solve_heap_forward_star_done_step
  | eapply lemma; eauto;
    [ eapply forward_star_model_graph_wf; eauto
    | solve_heap_forward_star_done_subset
    | apply forward_star_current_edge_not_done; auto ] ].

Ltac solve_heap_edge_loop_candidate_bounds
    visited_before cur_vertex cur_distance edge base_dist_values
    Hbridge Hcur_finite Hcur_valid Hneighbor_valid Hstep Hweight :=
  let Hbridge0 := fresh "Hbridge" in
  let Hcur_base0 := fresh "Hcur_base" in
  let Hmath_edge0 := fresh "Hmath_edge" in
  let Hmath_before0 := fresh "Hmath_before" in
  let Hselected0 := fresh "Hselected" in
  let Hoptimal0 := fresh "Hoptimal" in
  let Hshortest0 := fresh "Hshortest" in
  pose proof Hbridge as Hbridge0;
  unfold dijkstra_heap_edge_loop_math_bridge_state in Hbridge0;
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
    (cur_vertex, Znth edge to_values 0)
    cur_distance (Znth edge weight_values 0));
  [exact Hcur_valid | exact Hneighbor_valid | exact Hstep
  | exact Hshortest0 | exact Hweight].

Ltac solve_heap_edge_loop_relax_neighbor_unvisited
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
  unfold dijkstra_heap_edge_loop_math_bridge_state in Hbridge0;
  destruct Hbridge0 as
    (Hedge_bridge0 & _ & Hvisit_add0 & Hcur_base0 & _ & Hmath0);
  unfold dijkstra_heap_edge_loop_bridge_state in Hedge_bridge0;
  destruct Hedge_bridge0 as (Hedge_state0 & _);
  unfold dijkstra_heap_edge_loop_state in Hedge_state0;
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

Lemma dijkstra_heap_lfs_edge_body_math_step :
  forall visited_before visited_after
         cur_vertex cur_distance edge base_dist_values queue_set,
    Hoare
      (dijkstra_heap_edge_loop_math_model
        g src visited_before visited_after cur_vertex cur_distance edge
        base_dist_values queue_set
        head_values to_values weight_values next_values)
      (dijkstra_heap_lfs_edge_body
        head_values to_values weight_values next_values
        cur_vertex cur_distance (edge, queue_set))
      (fun result s =>
        match result with
        | by_continue acc =>
            dijkstra_heap_edge_loop_math_model
              g src visited_before visited_after cur_vertex cur_distance
              (fst acc) base_dist_values (snd acc)
              head_values to_values weight_values next_values s
        | by_break queue_set_done =>
            dijkstra_heap_loop_math_model g src queue_set_done s
        end).
Proof.
  intros visited_before visited_after cur_vertex cur_distance edge
    base_dist_values queue_set.
  dijkstra_heap_edge_body_hoare.
  - unfold dijkstra_heap_edge_loop_math_model in Hpre.
    destruct Hpre as (dist_values & Hstate & Hcur_finite & Hbridge).
    unfold dijkstra_heap_loop_math_model.
    exists visited_after, dist_values.
    split; [exact Hstate |].
    subst edge.
    unfold dijkstra_heap_edge_loop_math_bridge_state in Hbridge.
    destruct Hbridge as
      (Hedge_bridge & Hvisited_valid & Hvisit_add & _ & _ & Hmath_edge).
    assert (Hcur_valid : vertex_valid g cur_vertex).
    {
      unfold dijkstra_heap_edge_loop_bridge_state in Hedge_bridge.
      destruct Hedge_bridge as (Hedge_state & _).
      unfold dijkstra_heap_edge_loop_state in Hedge_state.
      tauto.
    }
    unfold dijkstra_heap_loop_math_bridge_state.
    split.
    + eapply dijkstra_heap_edge_loop_bridge_to_loop_bridge; eauto.
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
  - destruct Hrelax_assume as (Hweight_nonneg & _ & Hrelax_state).
    unfold dijkstra_heap_edge_loop_math_model in Hpre.
    destruct Hpre as (dist_values & Hstate & Hcur_finite & Hbridge).
    pose_dijkstra_heap_edge_loop_current_facts
      edge_count cur_vertex edge head_values next_values
      Hsize Hmodel Hedge_not_nil Hbridge.
    assert (Hcandidate_bounds :
      0 <= cur_distance + Znth edge weight_values 0 <
        DijkstraGraph.infinity)
      by (solve_heap_edge_loop_candidate_bounds
        visited_before cur_vertex cur_distance edge base_dist_values
        Hbridge Hcur_finite Hcur_valid Hneighbor_valid Hstep Hweight).
    erewrite graph_state_model_dist_cell in Hrelax_state by eauto.
    pose proof Hstate as ((Hshape & Hsafe & _) & _).
    assert (Hneighbor_unvisited :
      ~ visited_after (Znth edge to_values 0))
      by (solve_heap_edge_loop_relax_neighbor_unvisited
        visited_before visited_after cur_vertex cur_distance edge
        base_dist_values dist_values Hbridge Hcur_valid Hneighbor_valid
        Hstep Hweight Hcur_finite Hrelax_state).
    unfold dijkstra_heap_edge_loop_math_model.
    exists (replace_Znth (Znth edge to_values 0)
             (cur_distance + Znth edge weight_values 0) dist_values).
    split.
    + eapply graph_state_model_replace_Znth_set_state_distance; eauto.
    + split.
      * exact Hcur_finite.
      * unfold dijkstra_heap_edge_loop_math_bridge_state in Hbridge.
        destruct Hbridge as
          (Hedge_bridge & Hvisited_valid & Hvisit_add
           & Hcur_base & _ & Hmath).
        unfold dijkstra_heap_edge_loop_math_bridge_state.
        split.
        -- eapply dijkstra_heap_edge_loop_bridge_relax_update_push_result;
             eauto.
           eapply forward_star_next_0_lower_bound; eauto.
        -- do 3 (split; [eassumption |]).
           split.
           ++ eapply forward_star_next_0_nil_or_chain; eauto.
           ++ finish_heap_edge_math_done dijkstra_edge_math_state_relax_update.
  - unfold dijkstra_heap_edge_loop_math_model in Hpre.
    destruct Hpre as (dist_values & Hstate & Hcur_finite & Hbridge).
    pose_dijkstra_heap_edge_loop_current_facts
      edge_count cur_vertex edge head_values next_values
      Hsize Hmodel Hedge_not_nil Hbridge.
    pose proof Hstate as ((_ & Hsafe & _) & _).
    assert (Hcandidate_bounds :
      0 <= cur_distance + Znth edge weight_values 0 <
        DijkstraGraph.infinity)
      by (solve_heap_edge_loop_candidate_bounds
        visited_before cur_vertex cur_distance edge base_dist_values
        Hbridge Hcur_finite Hcur_valid Hneighbor_valid Hstep Hweight).
    assert (Hskip_cell :
      dist_cell dist_values (Znth edge to_values 0) <=
        cur_distance + Znth edge weight_values 0)
      by (eapply dijkstra_skip_assume_to_dist_cell; eauto).
    unfold dijkstra_heap_edge_loop_math_model.
    exists dist_values.
    split; [exact Hstate |].
    split; [exact Hcur_finite |].
    unfold dijkstra_heap_edge_loop_math_bridge_state in Hbridge.
    destruct Hbridge as
      (Hedge_bridge & Hvisited_valid & Hvisit_add & Hcur_base
       & _ & Hmath).
    unfold dijkstra_heap_edge_loop_math_bridge_state.
    split.
    + eapply dijkstra_heap_edge_loop_bridge_next; eauto.
      eapply forward_star_next_0_lower_bound; eauto.
    + do 3 (split; [eassumption |]).
      split.
      * eapply forward_star_next_0_nil_or_chain; eauto.
      * finish_heap_edge_math_done dijkstra_edge_math_state_relax_skip.
Qed.

End HeapLoopMathProofs.

Section HeapProgramProofs.

Context (g : DijkstraGraph.G)
        (vertex_count edge_count src : Z)
        (head_values to_values weight_values next_values : list Z).

Hypothesis Hsize : graph_has_size g vertex_count.
Hypothesis Hsrc : vertex_valid g src.
Hypothesis Hnonneg : nonnegative_edges g.
Hypothesis Hmodel :
  forward_star_model g edge_count
    head_values to_values weight_values next_values.
Hypothesis Hno_overflow :
  shortest_path_relaxation_bounded g src DijkstraGraph.infinity.

Local Notation done_edges :=
  (forward_star_done_edge_set
    head_values to_values weight_values next_values).

Lemma dijkstra_heap_lfs_edge_loop_after_pop_equal_math :
  forall queue_set_before queue_set_after cur_vertex cur_distance,
    Hoare
      (fun s =>
        exists visited_before dist_values s_before,
          s = set_state_visited cur_vertex s_before /\
          cur_distance = state_distance_cell cur_vertex s_before /\
          index_queue_pop_result
            queue_set_before queue_set_after cur_vertex cur_distance /\
          graph_state_model g visited_before dist_values s_before /\
          dijkstra_heap_loop_math_bridge_state
            g src visited_before dist_values queue_set_before)
      (dijkstra_heap_lfs_edge_loop
        head_values to_values weight_values next_values
        cur_vertex cur_distance (Znth cur_vertex head_values 0)
        queue_set_after)
      (fun queue_set_done s =>
        dijkstra_heap_loop_math_model g src queue_set_done s).
Proof.
  intros queue_set_before queue_set_after cur_vertex cur_distance.
  apply Hoare_pre_ex.
  intros visited_before.
  apply Hoare_pre_ex.
  intros dist_values.
  apply Hoare_pre_ex.
  intros s_before.
  eapply Hoare_conseq_pre.
  2: {
    unfold dijkstra_heap_lfs_edge_loop.
    eapply Hoare_repeat_break with
      (P := fun acc =>
        dijkstra_heap_edge_loop_math_model
          g src visited_before (fun v => visited_before v \/ v = cur_vertex)
          cur_vertex cur_distance (fst acc) dist_values (snd acc)
          head_values to_values weight_values next_values).
    intros [edge0 queue_set0].
    cbn [fst snd].
    eapply dijkstra_heap_lfs_edge_body_math_step; eauto.
  }
  intros s Hpre.
  destruct Hpre as
    (Hvisit & Heq_dist & Hpop & Hstate & Hmath_bridge).
  subst s.
  unfold dijkstra_heap_loop_math_bridge_state in Hmath_bridge.
  destruct Hmath_bridge as
    (Hloop_bridge & Hvisited_valid & Hmath).
  unfold dijkstra_heap_loop_bridge_state in Hloop_bridge.
  destruct Hloop_bridge as (Hloop_state & Hrefines).
  assert (Hcur_valid : vertex_valid g cur_vertex).
  {
    pose proof
      (dijkstra_heap_pop_result_bounds
        g vertex_count src visited_before dist_values queue_set_before
        queue_set_after cur_vertex cur_distance Hsize Hloop_state Hpop)
      as (_ & Hcur_bounds & _).
    unfold vertex_valid, DijkstraGraph.vertex_valid.
    unfold graph_has_size in Hsize; lia.
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
    - unfold heap_queue_refines_unvisited_dist,
        priority_queue_refines_unvisited_dist in Hrefines.
      destruct Hrefines as (_ & _ & _ & Hfinite & _).
      pose proof Hpop as Hpop_in.
      unfold index_queue_pop_result in Hpop_in.
      destruct Hpop_in as (popped & Hpopped & (Hin & _) & _).
      subst popped.
      apply (Hfinite cur_distance cur_vertex).
      exact Hin.
  }
  unfold dijkstra_heap_edge_loop_math_model.
  exists dist_values.
  assert (Hafter_pop_bridge :
    dijkstra_heap_after_pop_bridge_state
      g src visited_before dist_values queue_set_before queue_set_after
      cur_vertex cur_distance).
  {
    eapply dijkstra_heap_loop_bridge_state_pop_result.
    - unfold dijkstra_heap_loop_bridge_state.
      exact (conj Hloop_state Hrefines).
    - exact Hpop.
  }
  split.
  - apply graph_state_model_visit_state
      with (visited_set := visited_before);
      auto using visited_set_add_cons.
  - split; [exact Hcur_finite |].
    unfold dijkstra_heap_edge_loop_math_bridge_state.
    split.
    + pose proof Hafter_pop_bridge as Hafter_pop_bridge_copy.
      unfold dijkstra_heap_after_pop_bridge_state
        in Hafter_pop_bridge_copy.
      destruct Hafter_pop_bridge_copy as
        (Hloop_after & Hrefines_before & Hpop_before).
      unfold dijkstra_heap_edge_loop_bridge_state.
      split.
      * unfold dijkstra_heap_edge_loop_state.
        split; [exact Hloop_after |].
        split; [exact Hcur_valid |].
        split; [symmetry; exact Hcur_dist |].
        eapply forward_star_head_0_lower_bound; eauto.
      * assert (Hvisit_cons :
          visited_set_add visited_before cur_vertex
            (fun v => visited_before v \/ v = cur_vertex))
          by (unfold visited_set_add; tauto).
        pose proof
          (heap_queue_refines_unvisited_dist_pop_visit
            g visited_before (fun v => visited_before v \/ v = cur_vertex)
            dist_values queue_set_before queue_set_after cur_vertex cur_distance
            Hcur_valid Hvisit_cons Hrefines_before Hpop_before Hcur_dist)
          as Hrefines_after.
        exact Hrefines_after.
    + split; [exact Hvisited_valid |].
      assert (Hvisit_cons2 :
        visited_set_add visited_before cur_vertex
          (fun v => visited_before v \/ v = cur_vertex))
        by (unfold visited_set_add; tauto).
      split; [exact Hvisit_cons2 |].
      split; [exact Hcur_dist |].
      split.
      * eapply forward_star_head_0_nil_or_chain; eauto.
      * assert (Hselected :
          dijkstra_selected_min g visited_before dist_values cur_vertex).
        {
          eapply dijkstra_heap_pop_selected_min; eauto.
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
           assert (Hvisit_cons3 :
             visited_set_add visited_before cur_vertex
               (fun v => visited_before v \/ v = cur_vertex))
             by (unfold visited_set_add; tauto).
           split; [exact Hvisit_cons3 |].
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

Lemma dijkstra_heap_lfs_loop_body_math_step :
  forall queue_set,
    Hoare
      (dijkstra_heap_loop_math_model g src queue_set)
      (dijkstra_heap_lfs_loop_body
        head_values to_values weight_values next_values queue_set)
      (fun result s =>
        match result with
        | by_continue queue_set_next =>
            dijkstra_heap_loop_math_model g src queue_set_next s
        | by_break _ =>
            dijkstra_heap_loop_math_model
              g src (list_to_multiset (@nil (Z * Z))) s
        end).
Proof.
  intros queue_set.
  dijkstra_heap_loop_body_hoare.
  - eapply dijkstra_heap_loop_math_model_empty_canonical; eauto.
  - eapply Hoare_conseq_pre.
    2: {
      apply (dijkstra_heap_lfs_edge_loop_after_pop_equal_math
        queue_set queue_set_after cur_vertex cur_distance).
    }
    intros s Hpost.
    destruct Hpost as (s0 & Hvisit & Heq_dist & Hpop & _Hnonempty & Hpre).
    unfold dijkstra_heap_loop_math_model in Hpre.
    destruct Hpre as
      (visited_before & dist_values & Hstate & Hmath_bridge).
    exists visited_before, dist_values, s0.
    do 4 (split; [eassumption |]); eassumption.
  - unfold dijkstra_heap_loop_math_model in Hpre.
    destruct Hpre as
      (visited_set & dist_values & Hstate & Hmath_bridge).
    unfold dijkstra_heap_loop_math_bridge_state in Hmath_bridge.
    destruct Hmath_bridge as
      (Hloop_bridge & Hvisited_valid & Hmath).
    unfold dijkstra_heap_loop_bridge_state in Hloop_bridge.
    destruct Hloop_bridge as (Hloop_state & Hrefines).
    assert (Hcur_valid : vertex_valid g cur_vertex).
    {
      pose proof
        (dijkstra_heap_pop_result_bounds
          g vertex_count src visited_set dist_values queue_set
          queue_set_after cur_vertex cur_distance Hsize Hloop_state Hpop)
        as (_ & Hcur_bounds & _).
      unfold vertex_valid, DijkstraGraph.vertex_valid.
      unfold graph_has_size in Hsize; lia.
    }
    assert (Hstale :
      cur_distance <> dist_cell dist_values cur_vertex).
    {
      intro Heq.
      apply Hneq_dist.
      erewrite graph_state_model_dist_cell by eauto.
      exact Heq.
    }
    unfold dijkstra_heap_loop_math_model.
    exists visited_set, dist_values.
    split; [exact Hstate |].
    unfold dijkstra_heap_loop_math_bridge_state.
    split.
    + eapply dijkstra_heap_after_pop_bridge_state_stale_to_loop_bridge; eauto.
      eapply dijkstra_heap_loop_bridge_state_pop_result; eauto.
      unfold dijkstra_heap_loop_bridge_state.
      exact (conj Hloop_state Hrefines).
    + split; assumption.
Qed.

Lemma dijkstra_heap_lfs_initial_loop_body_math_step :
    Hoare
      (eq (initial_state src))
      (dijkstra_heap_lfs_loop_body
        head_values to_values weight_values next_values
        (singleton_source_queue src))
      (fun result s =>
        match result with
        | by_continue queue_set_next =>
            dijkstra_heap_loop_math_model g src queue_set_next s
        | by_break _ => False
        end).
Proof.
  dijkstra_heap_loop_body_hoare.
  - unfold singleton_source_queue, multiset_insert, list_to_multiset
      in Hempty.
    simpl in Hempty. discriminate Hempty.
  - apply Hoare_state_intro.
    intros s Hpost.
    destruct Hpost as (s0 & Hvisit & Heq_dist & Hpop & _Hnonempty & Hinitial).
    subst s0.
    pose proof
      (index_queue_pop_result_singleton_source
        src queue_set_after cur_vertex cur_distance Hpop)
      as (Hqueue_empty & Hcur_vertex & Hcur_distance).
    subst queue_set_after cur_vertex cur_distance.
    rewrite Hcur_distance in *.
    subst s.
    eapply Hoare_conseq_pre.
    2: {
      unfold dijkstra_heap_lfs_edge_loop.
      eapply Hoare_repeat_break with
        (P := fun acc =>
          dijkstra_heap_first_edge_loop_math_model
            g src (fst acc) (snd acc)
            head_values to_values weight_values next_values).
      intros [edge0 queue_set0]; cbn [fst snd].
      eapply dijkstra_heap_lfs_first_edge_body_math_step; eauto.
    }
    intros s Hcurrent.
    subst s.
    apply (initial_heap_first_edge_loop_math_model
      g vertex_count edge_count src
      head_values to_values weight_values next_values
      Hsize Hsrc Hnonneg Hmodel).
  - subst s.
    pose proof
      (index_queue_pop_result_singleton_source
        src queue_set_after cur_vertex cur_distance Hpop)
      as (Hqueue_empty & Hcur_vertex & Hcur_distance).
    subst queue_set_after cur_vertex cur_distance.
    exfalso.
    apply Hneq_dist.
    symmetry.
    apply initial_state_source_distance_cell.
Qed.

Lemma dijkstra_heap_loop_math_model_empty_to_shortest :
  forall dist_out s,
    graph_dist_model g dist_out s ->
    dijkstra_heap_loop_math_model
      g src (list_to_multiset (@nil (Z * Z))) s ->
    dijkstra_shortest_dist g src dist_out.
Proof.
  intros dist_out s Hdist_out Hloop.
  assert (Hlist_loop : dijkstra_loop_math_model g src nil s).
  {
    unfold dijkstra_heap_loop_math_model in Hloop.
    destruct Hloop as
      (visited_set & dist_values & Hstate & Hbridge_math).
    exists visited_set, dist_values.
    split; [exact Hstate |].
    unfold dijkstra_heap_loop_math_bridge_state in Hbridge_math.
    destruct Hbridge_math as (Hbridge & Hvisited_valid & Hmath).
    unfold dijkstra_heap_loop_bridge_state in Hbridge.
    destruct Hbridge as (Hheap_loop & Hheap_refines).
    unfold dijkstra_loop_math_bridge_state.
    split.
    - unfold dijkstra_loop_bridge_state.
      split.
      + unfold dijkstra_heap_loop_state in Hheap_loop.
        destruct Hheap_loop as
          (Hwf & Hsrc_valid & Hnonneg_valid & Hshape & Hsafe & _).
        unfold dijkstra_loop_state.
        split; [exact Hwf |].
        split; [exact Hsrc_valid |].
        split; [exact Hnonneg_valid |].
        split; [exact Hshape |].
        split; [exact Hsafe |].
        split; [simpl; exact I |].
        unfold priority_queue_vertices_valid.
        intros item Hin; contradiction.
      + unfold heap_queue_refines_unvisited_dist in Hheap_refines.
        unfold list_to_multiset in Hheap_refines.
        simpl in Hheap_refines.
        exact Hheap_refines.
    - split; assumption.
  }
  eapply dijkstra_loop_math_model_nil_to_shortest; eauto.
Qed.

Lemma dijkstra_heap_lfs_program_correct :
  forall dist_values,
    safeExec (graph_dist_model g dist_values)
      (return tt)
      (result_state (eq (initial_state src))
        (dijkstra_heap_lfs_program
          src head_values to_values weight_values next_values)) ->
    dijkstra_shortest_dist g src dist_values.
Proof.
  intros dist_values Hsafe.
  apply safeExec_ret in Hsafe as (s & Hstate & Hresult).
  unfold result_state in Hresult; sets_unfold in Hresult.
  destruct Hresult as (s_initial & Hinitial & Hrun_lfs).
  subst s_initial.
  assert (Hhoare :
    Hoare
      (eq (initial_state src))
      (dijkstra_heap_lfs_program
        src head_values to_values weight_values next_values)
      (fun _ s =>
        dijkstra_heap_loop_math_model
          g src (list_to_multiset (@nil (Z * Z))) s)).
  {
    unfold dijkstra_heap_lfs_program, dijkstra_heap_lfs_loop.
    eapply Hoare_proequiv.
    - symmetry.
      apply (repeat_break_unfold
        (dijkstra_heap_lfs_loop_body
          head_values to_values weight_values next_values)).
    - eapply Hoare_bind
        with (Q := fun result s =>
          match result with
          | by_continue queue_set_next =>
              dijkstra_heap_loop_math_model g src queue_set_next s
          | by_break _ => False
          end).
      + apply dijkstra_heap_lfs_initial_loop_body_math_step.
      + intros [queue_set_next | []].
        * unfold dijkstra_heap_lfs_loop.
          eapply Hoare_repeat_break with
            (P := dijkstra_heap_loop_math_model g src).
          intros queue_set0.
          eapply dijkstra_heap_lfs_loop_body_math_step; eauto.
        * unfold Hoare; contradiction.
  }
  eapply dijkstra_heap_loop_math_model_empty_to_shortest; eauto.
  exact (Hhoare (initial_state src) tt s eq_refl Hrun_lfs).
Qed.

End HeapProgramProofs.

End DijkstraIndexQueue.
