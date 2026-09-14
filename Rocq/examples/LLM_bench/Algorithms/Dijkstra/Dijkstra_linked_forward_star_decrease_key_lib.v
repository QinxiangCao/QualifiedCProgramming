Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.micromega.Lia.
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
Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_lib.

Export MonadNotation.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope monad.
Local Open Scope sac.

Import DijkstraGraph.
Import DijkstraLinkedForwardStar.

Module DijkstraDecreaseKey.

Ltac dijkstra_dk_min_epath_refl :=
  eapply (@dijkstra.min_value_weight_epath_refl DijkstraGraph.G DijkstraGraph.V
    DijkstraGraph.E DijkstraGraph.graph_instance DijkstraGraph.gvalid_instance
    _ DijkstraGraph.PathData DijkstraGraph.path_instance
    DijkstraGraph.empty_path_instance DijkstraGraph.single_path_instance
    DijkstraGraph.concat_path_instance DijkstraGraph.destruct1n_path_instance
    DijkstraGraph.weight_instance); eauto.

Definition partial_map_empty : partial_map := fun _ => None.

Definition partial_map_is_empty (M : partial_map) : Prop :=
  forall data_x key_x, ~ partial_map_present M data_x key_x.

Definition dk_map_queue_push_result
    (before after : partial_map) (vertex distance : Z) : Prop :=
  after = partial_map_add before vertex distance.

Definition dk_map_queue_pop_result
    (before after : partial_map) (vertex distance : Z) : Prop :=
  partial_map_minimum before (heap_item distance vertex) /\
  after = partial_map_remove before vertex.

Definition dk_map_queue_update_or_push_result
    (before after : partial_map)
    (size_before size_after vertex distance : Z) : Prop :=
  partial_map_update_or_add_size
    before size_before size_after vertex distance /\
  after = partial_map_update_or_add before vertex distance.

Definition dk_map_queue_update_or_push_result_any
    (before after : partial_map) (vertex distance : Z) : Prop :=
  exists size_before size_after,
    dk_map_queue_update_or_push_result
      before after size_before size_after vertex distance.

Lemma partial_map_empty_absent :
  forall data_x,
    partial_map_absent partial_map_empty data_x.
Proof.
  intros data_x.
  unfold partial_map_absent, partial_map_get, partial_map_empty.
  reflexivity.
Qed.

Lemma partial_map_empty_is_empty :
  partial_map_is_empty partial_map_empty.
Proof.
  unfold partial_map_is_empty, partial_map_present,
    partial_map_get, partial_map_empty.
  intros data_x key_x H; discriminate.
Qed.

Lemma partial_map_add_present_same :
  forall M data_x key_x,
    partial_map_present
      (partial_map_add M data_x key_x) data_x key_x.
Proof.
  intros M data_x key_x.
  unfold partial_map_present, partial_map_get, partial_map_add.
  destruct (Z.eq_dec data_x data_x); congruence.
Qed.

Lemma partial_map_add_present_other :
  forall M data_x key_x query old_key,
    query <> data_x ->
    partial_map_present M query old_key ->
    partial_map_present
      (partial_map_add M data_x key_x) query old_key.
Proof.
  intros M data_x key_x query old_key Hneq Hpresent.
  unfold partial_map_present, partial_map_get, partial_map_add in *.
  destruct (Z.eq_dec query data_x); congruence.
Qed.

Lemma partial_map_add_present_inv :
  forall M data_x key_x query value,
    partial_map_present
      (partial_map_add M data_x key_x) query value ->
    (query = data_x /\ value = key_x) \/
    (query <> data_x /\ partial_map_present M query value).
Proof.
  intros M data_x key_x query value Hpresent.
  unfold partial_map_present, partial_map_get, partial_map_add in *.
  destruct (Z.eq_dec query data_x) as [Heq | Hneq].
  - left. subst query. injection Hpresent as Hvalue. subst value.
    split; reflexivity.
  - right. split; congruence.
Qed.

Lemma partial_map_update_or_add_present_same :
  forall M data_x key_x,
    partial_map_present
      (partial_map_update_or_add M data_x key_x) data_x key_x.
Proof.
  intros.
  unfold partial_map_update_or_add, partial_map_update.
  apply partial_map_add_present_same.
Qed.

Lemma partial_map_update_or_add_present_other :
  forall M data_x key_x query old_key,
    query <> data_x ->
    partial_map_present M query old_key ->
    partial_map_present
      (partial_map_update_or_add M data_x key_x) query old_key.
Proof.
  intros.
  unfold partial_map_update_or_add, partial_map_update.
  eapply partial_map_add_present_other; eauto.
Qed.

Lemma partial_map_update_or_add_present_inv :
  forall M data_x key_x query value,
    partial_map_present
      (partial_map_update_or_add M data_x key_x) query value ->
    (query = data_x /\ value = key_x) \/
    (query <> data_x /\ partial_map_present M query value).
Proof.
  intros.
  unfold partial_map_update_or_add, partial_map_update in *.
  eapply partial_map_add_present_inv; eauto.
Qed.

Lemma partial_map_remove_present_other :
  forall M data_x query key_x,
    query <> data_x ->
    partial_map_present M query key_x ->
    partial_map_present
      (partial_map_remove M data_x) query key_x.
Proof.
  intros M data_x query key_x Hneq Hpresent.
  unfold partial_map_present, partial_map_get, partial_map_remove in *.
  destruct (Z.eq_dec query data_x); congruence.
Qed.

Lemma partial_map_remove_present_inv :
  forall M data_x query key_x,
    partial_map_present
      (partial_map_remove M data_x) query key_x ->
    query <> data_x /\ partial_map_present M query key_x.
Proof.
  intros M data_x query key_x Hpresent.
  unfold partial_map_present, partial_map_get, partial_map_remove in *.
  destruct (Z.eq_dec query data_x); [discriminate |].
  split; congruence.
Qed.

Lemma partial_map_remove_absent_same :
  forall M data_x,
    partial_map_absent (partial_map_remove M data_x) data_x.
Proof.
  intros M data_x.
  unfold partial_map_absent, partial_map_get, partial_map_remove.
  destruct (Z.eq_dec data_x data_x); congruence.
Qed.

Lemma partial_map_add_not_empty :
  forall M data_x key_x,
    ~ partial_map_is_empty (partial_map_add M data_x key_x).
Proof.
  intros M data_x key_x Hempty.
  specialize (Hempty data_x key_x).
  apply Hempty.
  apply partial_map_add_present_same.
Qed.

Definition map_queue_items_valid
    (g : DijkstraGraph.G) (M : partial_map) : Prop :=
  forall data_x key_x,
    partial_map_present M data_x key_x ->
    vertex_valid g data_x /\
    0 <= key_x <= DijkstraGraph.infinity.

Definition map_queue_exact_unvisited_dist
    (g : DijkstraGraph.G) (visited_set : Z -> Prop)
    (dist_values : list Z) (M : partial_map) : Prop :=
  (forall data_x key_x,
    partial_map_present M data_x key_x ->
    vertex_valid g data_x /\
    ~ visited_set data_x /\
    key_x = dist_cell dist_values data_x /\
    0 <= key_x < DijkstraGraph.infinity) /\
  (forall v,
    vertex_valid g v ->
    ~ visited_set v ->
    dist_cell dist_values v < DijkstraGraph.infinity ->
    partial_map_present M v (dist_cell dist_values v)).

Definition dijkstra_dk_map_loop_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (M : partial_map) : Prop :=
  DijkstraGraph.graph_wf g /\
  vertex_valid g src /\
  nonnegative_edges g /\
  vector_shape dist_values /\
  dist_values_safe dist_values /\
  map_queue_items_valid g M.

Definition dijkstra_dk_map_edge_loop_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (cur_vertex cur_distance edge : Z) (dist_values : list Z)
    (M : partial_map) : Prop :=
  dijkstra_dk_map_loop_state g src visited_set dist_values M /\
  vertex_valid g cur_vertex /\
  dist_cell dist_values cur_vertex = cur_distance /\
  -1 <= edge.

Definition dk_map_queue_pop_choice
    (M : partial_map) : program state ((partial_map * Z) * Z) :=
  get (fun _ result =>
    dk_map_queue_pop_result
      M
      (fst (fst result))
      (snd (fst result))
      (snd result)).

Definition dk_map_queue_update_or_push_choice
    (M : partial_map) (vertex distance : Z)
    : program state partial_map :=
  get (fun _ M_after =>
    dk_map_queue_update_or_push_result_any
      M M_after vertex distance).

Definition dijkstra_dk_lfs_edge_body
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance : Z)
    (acc : Z * partial_map)
    : program state
        (CntOrBrk (Z * partial_map) partial_map) :=
  let edge := fst acc in
  let M := snd acc in
  choice
    (assume (fun _ => edge = -1);;
     ret (by_break M))
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
        M_after <-
          dk_map_queue_update_or_push_choice M neighbor candidate;;
        ret (by_continue (next_edge, M_after)))
       (assume (fun s =>
          edge_weight < 0 \/
          cur_distance > DijkstraGraph.infinity - edge_weight \/
          candidate >= state_distance_cell neighbor s);;
        ret (by_continue (next_edge, M)))).

Definition dijkstra_dk_lfs_edge_loop
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance edge : Z)
    (M : partial_map) : program state partial_map :=
  repeat_break
    (dijkstra_dk_lfs_edge_body
      head_values to_values weight_values next_values
      cur_vertex cur_distance)
    (edge, M).

Definition dijkstra_dk_lfs_loop_body
    (head_values to_values weight_values next_values : list Z)
    (M : partial_map)
    : program state (CntOrBrk partial_map unit) :=
  choice
    (assume (fun _ => partial_map_is_empty M);;
     ret (by_break tt))
    (assume (fun _ => ~ partial_map_is_empty M);;
     pop_result <- dk_map_queue_pop_choice M;;
     let M_after := fst (fst pop_result) in
     let cur_vertex := snd (fst pop_result) in
     let cur_distance := snd pop_result in
     update' (set_state_visited cur_vertex);;
     M_after_edges <-
       dijkstra_dk_lfs_edge_loop
         head_values to_values weight_values next_values
         cur_vertex cur_distance
         (Znth cur_vertex head_values 0)
         M_after;;
     ret (by_continue M_after_edges)).

Definition dijkstra_dk_lfs_loop
    (head_values to_values weight_values next_values : list Z)
    (M : partial_map) : program state unit :=
  repeat_break
    (dijkstra_dk_lfs_loop_body
      head_values to_values weight_values next_values)
    M.

Definition singleton_source_map (src : Z) : partial_map :=
  partial_map_add partial_map_empty src 0.

Definition dijkstra_dk_lfs_program
    (src : Z)
    (head_values to_values weight_values next_values : list Z)
    : program state unit :=
  dijkstra_dk_lfs_loop head_values to_values weight_values next_values
    (singleton_source_map src).

Definition dijkstra_dk_lfs_edge_loop_after_body_cont
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance : Z)
    (step_result :
      CntOrBrk (Z * partial_map) partial_map)
    : program state unit :=
  M_after <-
    match step_result with
    | by_continue edge_state =>
        repeat_break
          (dijkstra_dk_lfs_edge_body
            head_values to_values weight_values next_values
            cur_vertex cur_distance)
          edge_state
    | by_break M_done => ret M_done
    end;;
  dijkstra_dk_lfs_loop
    head_values to_values weight_values next_values
    M_after.

Definition dijkstra_dk_lfs_edge_loop_cont
    (head_values to_values weight_values next_values : list Z)
    (cur_vertex cur_distance edge : Z)
    (M : partial_map) : program state unit :=
  M_after <-
    dijkstra_dk_lfs_edge_loop
      head_values to_values weight_values next_values
      cur_vertex cur_distance edge M;;
  dijkstra_dk_lfs_loop
    head_values to_values weight_values next_values
    M_after.

Definition dijkstra_dk_lfs_after_pop_cont
    (head_values to_values weight_values next_values : list Z)
    (M_after : partial_map)
    (cur_vertex cur_distance : Z) : program state unit :=
  step_result <-
    (update' (set_state_visited cur_vertex);;
     M_after_edges <-
       dijkstra_dk_lfs_edge_loop
         head_values to_values weight_values next_values
         cur_vertex cur_distance
         (Znth cur_vertex head_values 0)
         M_after;;
     ret (by_continue M_after_edges));;
  match step_result with
  | by_continue M_next =>
      dijkstra_dk_lfs_loop
        head_values to_values weight_values next_values
        M_next
  | by_break done => ret done
  end.

Definition dijkstra_dk_map_loop_phase_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (M : partial_map) : Prop :=
  (visited_set_empty visited_set /\
   dijkstra_init_dist (DijkstraGraph.vertex_count g) src dist_values /\
   shortest_path_relaxation_bounded g src DijkstraGraph.infinity /\
   M = singleton_source_map src) \/
  (visited_set_valid g visited_set /\
   shortest_path_relaxation_bounded g src DijkstraGraph.infinity /\
   dijkstra_math_invariant g src visited_set dist_values).

Definition dijkstra_dk_map_edge_phase_state
    (g : DijkstraGraph.G) (src cur_vertex cur_distance edge : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (_M : partial_map) : Prop :=
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

Definition dijkstra_dk_map_loop_refines
    (g : DijkstraGraph.G) (src : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (M : partial_map) (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (dijkstra_dk_lfs_loop head_values to_values weight_values next_values M)
    X /\
  map_queue_exact_unvisited_dist g visited_set dist_values M /\
  dijkstra_dk_map_loop_phase_state g src visited_set dist_values M.

Definition dijkstra_dk_map_after_pop_refines
    (g : DijkstraGraph.G) (src : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (M_after : partial_map) (cur_vertex cur_distance : Z)
    (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (dijkstra_dk_lfs_after_pop_cont head_values to_values weight_values
      next_values M_after cur_vertex cur_distance)
    X /\
  exists M_before,
    dijkstra_dk_map_loop_state g src visited_set dist_values M_before /\
    map_queue_exact_unvisited_dist g visited_set dist_values M_before /\
    dk_map_queue_pop_result M_before M_after cur_vertex cur_distance /\
    dijkstra_dk_map_loop_phase_state
      g src visited_set dist_values M_before.

Definition dijkstra_dk_map_edge_loop_refines
    (g : DijkstraGraph.G) (src cur_vertex cur_distance edge : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (M : partial_map) (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (dijkstra_dk_lfs_edge_loop_cont head_values to_values weight_values
      next_values cur_vertex cur_distance edge M)
    X /\
  map_queue_exact_unvisited_dist g visited_set dist_values M /\
  dijkstra_dk_map_edge_phase_state
    g src cur_vertex cur_distance edge
    head_values to_values weight_values next_values
    visited_set dist_values M.

Definition dijkstra_dk_lfs_initial_refines
    (g : DijkstraGraph.G) (src : Z)
    (head_values to_values weight_values next_values : list Z)
    (X : unit -> state -> Prop) : Prop :=
  safeExec (eq (initial_state src))
    (dijkstra_dk_lfs_program
      src head_values to_values weight_values next_values)
    X /\
  shortest_path_relaxation_bounded g src DijkstraGraph.infinity.

Definition dijkstra_dk_map_after_relax_refines
    (g : DijkstraGraph.G) (src cur_vertex cur_distance edge
       neighbor candidate : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (dist_values : list Z)
    (M : partial_map) (X : unit -> state -> Prop) : Prop :=
  safeExec (graph_state_model g visited_set dist_values)
    (M_after <-
       dk_map_queue_update_or_push_choice M neighbor candidate;;
     dijkstra_dk_lfs_edge_loop_cont head_values to_values weight_values
       next_values cur_vertex cur_distance
       (Znth edge next_values 0) M_after)
    X /\
  forall M_after,
    dk_map_queue_update_or_push_result_any
      M M_after neighbor candidate ->
    map_queue_exact_unvisited_dist
      g visited_set dist_values M_after /\
    dijkstra_dk_map_edge_phase_state
      g src cur_vertex cur_distance (Znth edge next_values 0)
      head_values to_values weight_values next_values
      visited_set dist_values M_after.

Lemma map_queue_exact_items_valid :
  forall g visited_set dist_values M,
    map_queue_exact_unvisited_dist g visited_set dist_values M ->
    map_queue_items_valid g M.
Proof.
  intros g visited_set dist_values M Hexact data_x key_x Hpresent.
  destruct Hexact as (Hitem & _).
  specialize (Hitem data_x key_x Hpresent)
    as (Hvalid & _ & _ & Hfinite).
  split; [exact Hvalid | lia].
Qed.

Lemma map_queue_exact_singleton_source :
  forall g vertex_count src visited_set dist_values,
    graph_has_size g vertex_count ->
    vertex_valid g src ->
    visited_set_empty visited_set ->
    dijkstra_init_dist vertex_count src dist_values ->
    map_queue_exact_unvisited_dist
      g visited_set dist_values (singleton_source_map src).
Proof.
  intros g vertex_count src visited_set dist_values
    Hsize Hsrc Hempty Hinit.
  destruct Hinit as (_Hshape & _Hsafe & _Hcount & Hsrc_bounds & Hcell).
  unfold map_queue_exact_unvisited_dist.
  split.
  - intros data_x key_x Hpresent.
    apply partial_map_add_present_inv in Hpresent.
    destruct Hpresent as [(Hdata & Hkey) | (_ & Hempty_present)].
    + subst data_x key_x.
      split; [exact Hsrc |].
      split.
      * intro Hvisited. exact (Hempty src Hvisited).
      * split.
        -- rewrite Hcell by exact Hsrc_bounds.
           destruct (Z.eq_dec src src); congruence.
        -- unfold DijkstraGraph.infinity; lia.
    + unfold partial_map_empty, partial_map_present,
        partial_map_get in Hempty_present.
      discriminate.
  - intros v Hvalid Hunvisited Hfinite.
    pose proof
      (graph_has_size_vertex_valid_bounds g vertex_count v Hsize Hvalid)
      as (_ & Hv_bounds).
    rewrite Hcell in Hfinite by exact Hv_bounds.
    destruct (Z.eq_dec v src) as [Heq | Hneq].
    + subst v.
      rewrite Hcell by exact Hsrc_bounds.
      destruct (Z.eq_dec src src); [| contradiction].
      apply partial_map_add_present_same.
    + unfold DijkstraGraph.infinity in Hfinite; lia.
Qed.

Lemma map_queue_exact_update_or_push_pre :
  forall g visited_set dist_values M neighbor candidate,
    vertex_valid g neighbor ->
    ~ visited_set neighbor ->
    map_queue_exact_unvisited_dist g visited_set dist_values M ->
    candidate < dist_cell dist_values neighbor ->
    partial_map_update_or_add_pre M neighbor candidate.
Proof.
  intros g visited_set dist_values M neighbor candidate
    Hvalid Hunvisited Hexact Hrelax.
  unfold partial_map_update_or_add_pre, update_or_push_pre.
  destruct Hexact as (Hitem & Hcovers).
  destruct (classic (dist_cell dist_values neighbor <
    DijkstraGraph.infinity)) as [Hfinite | Hnot_finite].
  - right.
    unfold partial_map_decrease_key_pre, decrease_key_pre, heap_key_of.
    exists (dist_cell dist_values neighbor).
    split; [apply Hcovers; auto | lia].
  - left.
    unfold heap_data_absent, partial_map_absent, partial_map_get.
    destruct (M neighbor) as [old_key |] eqn:Hpresent; [| reflexivity].
    exfalso.
    specialize (Hitem neighbor old_key Hpresent)
      as (_ & _ & Hold_eq & Hold_finite).
    lia.
Qed.

Lemma map_queue_exact_update_or_push :
  forall g vertex_count visited_set dist_values M M_after
         neighbor candidate,
    graph_has_size g vertex_count ->
    vector_shape dist_values ->
    storage_index neighbor ->
    vertex_valid g neighbor ->
    ~ visited_set neighbor ->
    candidate < dist_cell dist_values neighbor ->
    0 <= candidate < DijkstraGraph.infinity ->
    map_queue_exact_unvisited_dist g visited_set dist_values M ->
    dk_map_queue_update_or_push_result_any
      M M_after neighbor candidate ->
    map_queue_exact_unvisited_dist
      g visited_set (replace_Znth neighbor candidate dist_values)
      M_after.
Proof.
  intros g vertex_count visited_set dist_values M M_after
    neighbor candidate Hsize Hshape Hneighbor_storage Hneighbor_valid
    Hneighbor_unvisited Hrelax Hcandidate_bounds Hexact Hresult.
  destruct Hresult as (size_before & size_after & Hresult).
  unfold dk_map_queue_update_or_push_result in Hresult.
  destruct Hresult as (_Hsize & Hafter).
  subst M_after.
  destruct Hexact as (Hitem & Hcovers).
  unfold map_queue_exact_unvisited_dist.
  split.
  - intros data_x key_x Hpresent.
    apply partial_map_update_or_add_present_inv in Hpresent.
    destruct Hpresent as [(Hdata & Hkey) | (Hneq & Hold)].
    + subst data_x key_x.
      split; [exact Hneighbor_valid |].
      split; [exact Hneighbor_unvisited |].
      split.
      * symmetry. apply dist_cell_replace_Znth_same; auto.
      * exact Hcandidate_bounds.
    + specialize (Hitem data_x key_x Hold)
        as (Hvalid & Hunvisited & Hdist & Hfinite).
      split; [exact Hvalid |].
      split; [exact Hunvisited |].
      split.
      * pose proof
          (graph_has_size_vertex_valid_storage
            g vertex_count data_x Hsize Hvalid) as Hstorage.
        rewrite dist_cell_replace_Znth_diff by auto.
        exact Hdist.
      * exact Hfinite.
  - intros v Hvalid Hunvisited Hfinite.
    destruct (Z.eq_dec v neighbor) as [Heq | Hneq].
    + subst v.
      rewrite dist_cell_replace_Znth_same by auto.
      apply partial_map_update_or_add_present_same.
    + pose proof
        (graph_has_size_vertex_valid_storage
          g vertex_count v Hsize Hvalid) as Hv_storage.
      rewrite dist_cell_replace_Znth_diff in Hfinite |- * by auto.
      eapply partial_map_update_or_add_present_other.
      * exact Hneq.
      * apply Hcovers; auto.
Qed.

Lemma map_queue_exact_pop_item :
  forall g visited_set dist_values M_before M_after
         cur_vertex cur_distance,
    map_queue_exact_unvisited_dist g visited_set dist_values M_before ->
    dk_map_queue_pop_result M_before M_after cur_vertex cur_distance ->
    vertex_valid g cur_vertex /\
    ~ visited_set cur_vertex /\
    cur_distance = dist_cell dist_values cur_vertex /\
    0 <= cur_distance < DijkstraGraph.infinity.
Proof.
  intros g visited_set dist_values M_before M_after
    cur_vertex cur_distance Hexact Hpop.
  destruct Hexact as (Hitem & _).
  unfold dk_map_queue_pop_result, partial_map_minimum,
    partial_map_item in Hpop.
  destruct Hpop as ((Hpresent & _Hmin) & _Hafter).
  exact (Hitem cur_vertex cur_distance Hpresent).
Qed.

Lemma map_queue_exact_pop_visit :
  forall g visited_before visited_after dist_values M_before M_after
         cur_vertex cur_distance,
    vertex_valid g cur_vertex ->
    visited_set_add visited_before cur_vertex visited_after ->
    map_queue_exact_unvisited_dist g visited_before dist_values M_before ->
    dk_map_queue_pop_result M_before M_after cur_vertex cur_distance ->
    cur_distance = dist_cell dist_values cur_vertex ->
    map_queue_exact_unvisited_dist g visited_after dist_values M_after.
Proof.
  intros g visited_before visited_after dist_values M_before M_after
    cur_vertex cur_distance Hcur_valid Hvisit_add Hexact Hpop Hcur_dist.
  destruct Hexact as (Hitem & Hcovers).
  unfold dk_map_queue_pop_result in Hpop.
  destruct Hpop as (_Hmin & Hafter).
  subst M_after.
  unfold map_queue_exact_unvisited_dist.
  split.
  - intros data_x key_x Hpresent_after.
    apply partial_map_remove_present_inv in Hpresent_after
      as (Hneq & Hpresent_before).
    specialize (Hitem data_x key_x Hpresent_before)
      as (Hvalid & Hunvisited_before & Hdist & Hfinite).
    split; [exact Hvalid |].
    split.
    + intro Hvisited_after.
      unfold visited_set_add in Hvisit_add.
      apply Hvisit_add in Hvisited_after.
      destruct Hvisited_after as [Hvisited_before | Heq].
      * exact (Hunvisited_before Hvisited_before).
      * subst data_x. contradiction.
    + split; assumption.
  - intros v Hvalid Hunvisited_after Hfinite.
    assert (~ visited_before v) as Hunvisited_before.
    {
      intro Hvisited_before.
      apply Hunvisited_after.
      unfold visited_set_add in Hvisit_add.
      apply Hvisit_add; left; exact Hvisited_before.
    }
    apply partial_map_remove_present_other.
    + intro Heq. subst v.
      apply Hunvisited_after.
      unfold visited_set_add in Hvisit_add.
      apply Hvisit_add; right; reflexivity.
    + apply Hcovers; auto.
Qed.

Lemma map_queue_pop_selected_min :
  forall g vertex_count src visited_set dist_values M_before
         M_after cur_vertex cur_distance,
    graph_has_size g vertex_count ->
    dijkstra_dk_map_loop_state g src visited_set dist_values M_before ->
    map_queue_exact_unvisited_dist g visited_set dist_values M_before ->
    dk_map_queue_pop_result M_before M_after cur_vertex cur_distance ->
    cur_distance = dist_cell dist_values cur_vertex ->
    0 <= cur_distance < DijkstraGraph.infinity ->
    dijkstra_selected_min g visited_set dist_values cur_vertex.
Proof.
  intros g vertex_count src visited_set dist_values M_before
    M_after cur_vertex cur_distance Hsize Hloop Hexact Hpop
    Hcur_dist Hcur_finite.
  unfold dijkstra_selected_min.
  destruct Hexact as (Hitem & Hcovers).
  unfold dk_map_queue_pop_result, partial_map_minimum,
    partial_map_item in Hpop.
  destruct Hpop as ((Hpopped_present & Hminimum) & _Hafter).
  assert (Hcur_valid : vertex_valid g cur_vertex).
  {
    specialize (Hitem cur_vertex cur_distance Hpopped_present)
      as (Hvalid & _).
    exact Hvalid.
  }
  assert (Hcur_unvisited_set : ~ visited_set cur_vertex).
  {
    specialize (Hitem cur_vertex cur_distance Hpopped_present)
      as (_ & Hunvisited & _).
    exact Hunvisited.
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
        destruct (Z_lt_ge_dec
          (dist_cell dist_values v) DijkstraGraph.infinity)
          as [Hfinite_v | Hinf].
        - pose proof (Hcovers v Hvalid Hunvisited_set Hfinite_v)
            as Hpresent_v.
          specialize (Hminimum v (dist_cell dist_values v) Hpresent_v).
          simpl in Hminimum.
          exact Hminimum.
        - assert (Hsafe : dist_values_safe dist_values)
            by (unfold dijkstra_dk_map_loop_state in Hloop; tauto).
          pose proof
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

Lemma dijkstra_dk_map_pop_result_bounds :
  forall g vertex_count src visited_set dist_values M_before
         M_after cur_vertex cur_distance,
    graph_has_size g vertex_count ->
    dijkstra_dk_map_loop_state g src visited_set dist_values M_before ->
    dk_map_queue_pop_result M_before M_after cur_vertex cur_distance ->
    storage_index cur_vertex /\
    0 <= cur_vertex < vertex_count /\
    0 <= cur_distance <= DijkstraGraph.infinity.
Proof.
  intros g vertex_count src visited_set dist_values M_before
    M_after cur_vertex cur_distance Hsize Hstate Hpop.
  unfold dk_map_queue_pop_result, partial_map_minimum,
    partial_map_item in Hpop.
  destruct Hpop as ((Hpresent & _Hmin) & _Hafter).
  unfold dijkstra_dk_map_loop_state, map_queue_items_valid in Hstate.
  destruct Hstate as (_ & _ & _ & _ & _ & Hvalid).
  specialize (Hvalid cur_vertex cur_distance Hpresent)
    as (Hvertex & Hdistance).
  pose proof
    (graph_has_size_vertex_valid_storage g vertex_count cur_vertex
      Hsize Hvertex) as Hstorage.
  pose proof
    (graph_has_size_vertex_valid_bounds g vertex_count cur_vertex
      Hsize Hvertex) as (_ & Hbounds).
  split; [exact Hstorage |].
  split; [exact Hbounds | exact Hdistance].
Qed.

Lemma dijkstra_dk_map_loop_state_pop :
  forall g src visited_set dist_values M_before M_after
         cur_vertex cur_distance,
    dijkstra_dk_map_loop_state g src visited_set dist_values M_before ->
    map_queue_exact_unvisited_dist g visited_set dist_values M_before ->
    dk_map_queue_pop_result M_before M_after cur_vertex cur_distance ->
    dijkstra_dk_map_loop_state g src visited_set dist_values M_after.
Proof.
  intros g src visited_set dist_values M_before M_after
    cur_vertex cur_distance Hstate Hexact Hpop.
  unfold dijkstra_dk_map_loop_state in *.
  destruct Hstate as (Hwf & Hsrc & Hnonneg & Hshape & Hsafe & Hitems).
  do 5 (split; [assumption |]).
  unfold map_queue_items_valid in *.
  intros data_x key_x Hpresent_after.
  unfold dk_map_queue_pop_result in Hpop.
  destruct Hpop as (_Hmin & Hafter).
  subst M_after.
  apply partial_map_remove_present_inv in Hpresent_after
    as (_ & Hpresent_before).
  apply Hitems. exact Hpresent_before.
Qed.

Lemma dijkstra_dk_initial_loop_state :
  forall g vertex_count edge_count src visited_set dist_values
         head_values to_values weight_values next_values,
    graph_has_size g vertex_count ->
    vertex_valid g src ->
    nonnegative_edges g ->
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    visited_set_empty visited_set ->
    dijkstra_init_dist vertex_count src dist_values ->
    dijkstra_dk_map_loop_state
      g src visited_set dist_values
      (partial_map_add partial_map_empty src 0).
Proof.
  intros g vertex_count edge_count src visited_set dist_values
    head_values to_values weight_values next_values
    Hsize Hsrc Hnonneg Hmodel _Hempty Hinit.
  destruct Hinit as (Hshape & Hsafe & _Hcount & _Hsrc_bounds & _Hcell).
  unfold dijkstra_dk_map_loop_state.
  split; [eapply forward_star_model_graph_wf; eauto |].
  split; [exact Hsrc |].
  split; [exact Hnonneg |].
  split; [exact Hshape |].
  split; [exact Hsafe |].
  unfold map_queue_items_valid.
  intros data_x key_x Hpresent.
  apply partial_map_add_present_inv in Hpresent.
  destruct Hpresent as [(Hdata & Hkey) | (_ & Hempty_present)].
  - subst data_x key_x.
    split; [exact Hsrc |].
    unfold DijkstraGraph.infinity; lia.
  - unfold partial_map_empty, partial_map_present,
      partial_map_get in Hempty_present.
    discriminate.
Qed.

Lemma dijkstra_dk_map_edge_loop_to_loop_state :
  forall g src visited_set cur_vertex cur_distance edge dist_values M,
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values M ->
    dijkstra_dk_map_loop_state g src visited_set dist_values M.
Proof.
  unfold dijkstra_dk_map_edge_loop_state; tauto.
Qed.

Lemma dijkstra_dk_map_edge_loop_next_state :
  forall g src visited_set cur_vertex cur_distance edge next_edge
         dist_values M,
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values M ->
    -1 <= next_edge ->
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance next_edge dist_values M.
Proof.
  unfold dijkstra_dk_map_edge_loop_state; intros; tauto.
Qed.

Lemma dijkstra_dk_map_edge_loop_state_relax_update :
  forall g vertex_count src visited_set cur_vertex cur_distance edge
         neighbor edge_weight candidate dist_values M,
    graph_has_size g vertex_count ->
    vertex_valid g neighbor ->
    storage_index neighbor ->
    0 <= candidate < DijkstraGraph.infinity ->
    0 <= edge_weight ->
    candidate = cur_distance + edge_weight ->
    candidate < dist_cell dist_values neighbor ->
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values M ->
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge
      (replace_Znth neighbor candidate dist_values) M.
Proof.
  intros g vertex_count src visited_set cur_vertex cur_distance edge
    neighbor edge_weight candidate dist_values M
    Hsize Hneighbor_valid Hneighbor_storage Hcandidate_bounds
    Hweight_nonneg Hcandidate Hrelax Hedge.
  unfold dijkstra_dk_map_edge_loop_state in *.
  destruct Hedge as (Hloop & Hcur_valid & Hcur_dist & Hedge_nonneg).
  assert (Hshape_loop : vector_shape dist_values)
    by (unfold dijkstra_dk_map_loop_state in Hloop; tauto).
  assert (Hneighbor_ne_cur : neighbor <> cur_vertex)
    by (intro Hsame; subst neighbor;
        rewrite Hcur_dist in Hrelax; subst candidate; lia).
  split.
  - unfold dijkstra_dk_map_loop_state in *.
    destruct Hloop as
      (Hwf & Hsrc & Hnonneg & Hshape & Hsafe & Hqueue_valid).
    split; [exact Hwf |].
    split; [exact Hsrc |].
    split; [exact Hnonneg |].
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

Lemma dijkstra_dk_map_after_relax_update_edge_loop_state :
  forall g edge_count src cur_vertex cur_distance edge neighbor candidate
         head_values to_values weight_values next_values visited_set dist_values
         M M_after size_before size_after X,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_index edge_count edge ->
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values M ->
    dk_map_queue_update_or_push_result
      M M_after size_before size_after neighbor candidate ->
    dijkstra_dk_map_after_relax_refines
      g src cur_vertex cur_distance edge neighbor candidate
      head_values to_values weight_values next_values
      visited_set dist_values M X ->
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance
      (Znth edge next_values 0) dist_values M_after.
Proof.
  intros g edge_count src cur_vertex cur_distance edge neighbor candidate
    head_values to_values weight_values next_values visited_set dist_values
    M M_after size_before size_after X Hmodel Hedge_index Hedge_state
    Hupdate Hafter_relax.
  assert (Hnext_case :
    Znth edge next_values 0 = -1 \/
    edge_index edge_count (Znth edge next_values 0)).
  { eapply forward_star_model_next_case_0; eauto. }
  assert (Hnext_nonneg : -1 <= Znth edge next_values 0)
    by (destruct Hnext_case as [Hnil | Hedge];
        [rewrite Hnil | unfold edge_index in Hedge]; lia).
  unfold dijkstra_dk_map_after_relax_refines in Hafter_relax.
  destruct Hafter_relax as (_Hsafe & Hafter).
  assert (Hupdate_any :
    dk_map_queue_update_or_push_result_any M M_after neighbor candidate)
    by (exists size_before, size_after; exact Hupdate).
  specialize (Hafter M_after Hupdate_any).
  destruct Hafter as (Hexact_after & _Hphase_after).
  pose proof
    (map_queue_exact_items_valid g visited_set dist_values M_after
      Hexact_after) as Hitems_after.
  unfold dijkstra_dk_map_edge_loop_state in *.
  destruct Hedge_state as
    (Hloop & Hcur_valid & Hcur_dist & Hedge_nonneg).
  unfold dijkstra_dk_map_loop_state in Hloop.
  destruct Hloop as (Hwf & Hsrc & Hnonneg & Hshape & Hsafe & _Hitems_old).
  split.
  - unfold dijkstra_dk_map_loop_state.
    split; [exact Hwf |].
    split; [exact Hsrc |].
    split; [exact Hnonneg |].
    split; [exact Hshape |].
    split; [exact Hsafe | exact Hitems_after].
  - split; [exact Hcur_valid |].
    split; [exact Hcur_dist | exact Hnext_nonneg].
Qed.

Lemma dk_store_heap_size_bounds :
  forall key data pos data_bound capacity M size,
    store_heap key data pos data_bound capacity M size |--
      “ 0 <= size /\ size <= heap_capacity ” &&
      store_heap key data pos data_bound capacity M size.
Proof.
  intros key data pos data_bound capacity M size.
  unfold store_heap at 1.
  Intros key_values.
  Intros data_values.
  Intros pos_values.
  match goal with
  | Hrep : heap_representation
      M key_values data_values pos_values data_bound size |- _ =>
      pose proof Hrep as Hrep_keep;
      destruct Hrep as (Hsize_nonneg & Hsize_cap & _)
  end.
  split_pure_spatial.
  - unfold store_heap.
    Exists key_values data_values pos_values.
    split_pure_spatial.
    + cancel (IntArray.full key size key_values).
      cancel (IntArray.undef_seg key size capacity).
      cancel (IntArray.full data size data_values).
      cancel (IntArray.undef_seg data size capacity).
      cancel (IntArray.full pos data_bound pos_values).
    + split_pures; dump_pre_spatial; exact Hrep_keep.
  - dump_pre_spatial; split; assumption.
Qed.

Lemma dijkstra_dk_Forall_range_incl_seq :
  forall values bound,
    0 <= bound ->
    Forall (fun value : Z => 0 <= value < bound) values ->
    incl values (map Z.of_nat (seq 0 (Z.to_nat bound))).
Proof.
  intros values bound Hbound HFor.
  unfold incl.
  intros value Hin.
  apply Forall_forall with (x := value) in HFor; [| exact Hin].
  apply in_map_iff.
  exists (Z.to_nat value).
  split.
  - apply Z2Nat.id. lia.
  - apply in_seq.
    split; [lia |].
    rewrite Nat.add_0_l.
    apply Z2Nat.inj_lt; lia.
Qed.

Lemma dijkstra_dk_NoDup_Forall_range_Zlength_le :
  forall values bound,
    0 <= bound ->
    NoDup values ->
    Forall (fun value : Z => 0 <= value < bound) values ->
    Zlength values <= bound.
Proof.
  intros values bound Hbound Hnodup HFor.
  pose proof
    (dijkstra_dk_Forall_range_incl_seq values bound Hbound HFor)
    as Hincl.
  pose proof (NoDup_incl_length Hnodup Hincl) as Hlen.
  rewrite length_map, length_seq in Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite Zlength_correct.
  rewrite Z2Nat.id in Hlen by lia.
  lia.
Qed.

Lemma dijkstra_dk_heap_data_unique_NoDup :
  forall data_values size,
    Zlength data_values = size ->
    heap_data_unique data_values size ->
    NoDup data_values.
Proof.
  intros data_values size Hlen Hunique.
  apply NoDup_nth_error.
  intros i j Hi Hnth.
  assert (Hj : (j < length data_values)%nat).
  {
    apply nth_error_Some.
    rewrite <- Hnth.
    apply nth_error_Some.
    exact Hi.
  }
  assert (HiZ : 0 <= Z.of_nat i < size)
    by (rewrite <- Hlen, Zlength_correct; lia).
  assert (HjZ : 0 <= Z.of_nat j < size)
    by (rewrite <- Hlen, Zlength_correct; lia).
  apply Nat2Z.inj.
  apply Hunique; try assumption.
  unfold Znth.
  rewrite !Nat2Z.id.
  assert (Hi_some : nth_error data_values i <> None).
  { apply nth_error_Some. exact Hi. }
  destruct (nth_error data_values i) as [value |] eqn:Hierr.
  - assert (Hjerr : nth_error data_values j = Some value).
    { symmetry. exact Hnth. }
    rewrite (@nth_error_nth Z data_values i value 0 Hierr).
    rewrite (@nth_error_nth Z data_values j value 0 Hjerr).
    reflexivity.
  - contradiction.
Qed.

Lemma dijkstra_dk_heap_data_valid_size_bound :
  forall data_values data_bound size,
    0 <= data_bound ->
    Zlength data_values = size ->
    heap_data_unique data_values size ->
    heap_data_valid data_values data_bound size ->
    size <= data_bound.
Proof.
  intros data_values data_bound size Hbound Hlen Hunique Hvalid.
  assert (Hnodup : NoDup data_values)
    by (eapply dijkstra_dk_heap_data_unique_NoDup; eauto).
  assert (HFor :
    Forall (fun value : Z => 0 <= value < data_bound) data_values).
  {
    apply Forall_forall.
    intros value Hin.
    apply In_nth_error in Hin as [index Hnth].
    assert (Hindex_bound : (index < length data_values)%nat).
    {
      apply nth_error_Some.
      rewrite Hnth.
      discriminate.
    }
    assert (Hindex_Z : 0 <= Z.of_nat index < size)
      by (rewrite <- Hlen, Zlength_correct; lia).
    specialize (Hvalid (Z.of_nat index) Hindex_Z).
    unfold Znth in Hvalid.
    rewrite Nat2Z.id in Hvalid.
    rewrite (@nth_error_nth Z data_values index value 0 Hnth) in Hvalid.
    exact Hvalid.
  }
  pose proof
    (dijkstra_dk_NoDup_Forall_range_Zlength_le
      data_values data_bound Hbound Hnodup HFor) as Hle.
  lia.
Qed.

Lemma dk_store_heap_size_data_bound :
  forall key data pos data_bound capacity M size,
    store_heap key data pos data_bound capacity M size |--
      “ 0 <= size /\ size <= data_bound /\ size <= heap_capacity ” &&
      store_heap key data pos data_bound capacity M size.
Proof.
  intros key data pos data_bound capacity M size.
  unfold store_heap at 1.
  Intros key_values.
  Intros data_values.
  Intros pos_values.
  match goal with
  | Hrep : heap_representation
      M key_values data_values pos_values data_bound size |- _ =>
      pose proof Hrep as Hrep_keep;
      pose proof Hrep as Hrep_full
  end.
  destruct Hrep_keep as (Hsize_nonneg & Hsize_cap & Hmap & _ & Hpos).
  destruct Hmap as (_Hkey_len & Hdata_len & Hunique & _).
  destruct Hpos as (Hbound & _Hpos_len & Hdata_valid & _).
  pose proof
    (dijkstra_dk_heap_data_valid_size_bound
      data_values data_bound size Hbound Hdata_len Hunique Hdata_valid)
    as Hsize_data_bound.
  split_pure_spatial.
  - unfold store_heap.
    Exists key_values data_values pos_values.
    split_pure_spatial.
    + cancel (IntArray.full key size key_values).
      cancel (IntArray.undef_seg key size capacity).
      cancel (IntArray.full data size data_values).
      cancel (IntArray.undef_seg data size capacity).
      cancel (IntArray.full pos data_bound pos_values).
    + split_pures; dump_pre_spatial; exact Hrep_full.
  - dump_pre_spatial.
    repeat split; assumption.
Qed.

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

Lemma singleton_source_map_pop :
  forall src M_after cur_vertex cur_distance,
    dk_map_queue_pop_result
      (singleton_source_map src) M_after cur_vertex cur_distance ->
    M_after = partial_map_empty /\
    cur_vertex = src /\
    cur_distance = 0.
Proof.
  intros src M_after cur_vertex cur_distance Hpop.
  unfold dk_map_queue_pop_result, partial_map_minimum,
    partial_map_item, singleton_source_map in Hpop.
  destruct Hpop as ((Hpresent & _Hmin) & Hafter).
  apply partial_map_add_present_inv in Hpresent.
  destruct Hpresent as [(Hcur & Hdist) | (_ & Hempty)].
  - unfold heap_item, item_data, item_key in Hcur, Hdist; simpl in Hcur, Hdist.
    subst M_after.
    split.
    + apply functional_extensionality.
      intro query.
      unfold partial_map_remove, partial_map_add, partial_map_empty.
      destruct (Z.eq_dec query cur_vertex) as [Hquery | Hquery].
      * subst query.
        destruct (Z.eq_dec cur_vertex src); [reflexivity | congruence].
      * destruct (Z.eq_dec query src) as [Hquery_src | Hquery_src].
        -- subst query. congruence.
        -- reflexivity.
    + split; assumption.
  - unfold partial_map_empty, partial_map_present,
      partial_map_get in Hempty.
    discriminate.
Qed.

Lemma dijkstra_dk_lfs_edge_loop_cont_unfold :
  forall head_values to_values weight_values next_values
         cur_vertex cur_distance edge (queue_map : partial_map),
    Sets.equiv
      (dijkstra_dk_lfs_edge_loop_cont
        head_values to_values weight_values next_values
        cur_vertex cur_distance edge queue_map)
      (step_result <-
        dijkstra_dk_lfs_edge_body
          head_values to_values weight_values next_values
          cur_vertex cur_distance (edge, queue_map);;
       dijkstra_dk_lfs_edge_loop_after_body_cont
        head_values to_values weight_values next_values
        cur_vertex cur_distance step_result).
Proof.
  intros.
  unfold dijkstra_dk_lfs_edge_loop_cont,
    dijkstra_dk_lfs_edge_loop_after_body_cont,
    dijkstra_dk_lfs_edge_loop.
  rewrite (repeat_break_unfold
    (dijkstra_dk_lfs_edge_body
      head_values to_values weight_values next_values
      cur_vertex cur_distance)
    (edge, queue_map)), bind_assoc.
  reflexivity.
Qed.

Lemma dijkstra_dk_lfs_initial_to_loop_refines :
  forall g vertex_count src head_values to_values weight_values next_values
         visited_set dist_values M X,
    graph_has_size g vertex_count ->
    vertex_valid g src ->
    visited_set_empty visited_set ->
    dijkstra_init_dist vertex_count src dist_values ->
    dk_map_queue_push_result partial_map_empty M src 0 ->
    dijkstra_dk_lfs_initial_refines
      g src head_values to_values weight_values next_values X ->
    dijkstra_dk_map_loop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values M X.
Proof.
  intros g vertex_count src head_values to_values weight_values next_values
    visited_set dist_values M X Hsize Hsrc Hempty Hinit Hpush
    Hrefines.
  unfold dk_map_queue_push_result in Hpush.
  subst M.
  unfold dijkstra_dk_lfs_initial_refines in Hrefines.
  destruct Hrefines as (Hrefines & Hno_overflow).
  unfold dijkstra_dk_lfs_program in Hrefines.
  unfold dijkstra_dk_map_loop_refines.
  split.
  - eapply safeExec_conseq.
    + exact Hrefines.
    + intros s Hs.
      subst s.
      apply dijkstra_init_dist_graph_state_model_initial
        with (vertex_count := vertex_count); auto.
  - split.
    + eapply map_queue_exact_singleton_source; eauto.
    + left.
      split; [exact Hempty |].
      split.
      * destruct Hsize as (Hvertex_count & _).
        rewrite Hvertex_count.
        exact Hinit.
      * split; [exact Hno_overflow | reflexivity].
Qed.

Lemma dijkstra_dk_map_loop_refines_empty_to_return :
  forall g src head_values to_values weight_values next_values
         visited_set dist_values M X,
    partial_map_is_empty M ->
    dijkstra_dk_map_loop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values M X ->
    safeExec (graph_state_model g visited_set dist_values) (return tt) X.
Proof.
  intros g src head_values to_values weight_values next_values
    visited_set dist_values M X Hempty Hrefines.
  unfold dijkstra_dk_map_loop_refines in Hrefines.
  destruct Hrefines as (Hrefines & _Hheap & _Hphase).
  unfold dijkstra_dk_lfs_loop in Hrefines.
  eapply safeExec_proequiv in Hrefines.
  2: { apply repeat_break_unfold. }
  unfold dijkstra_dk_lfs_loop_body in Hrefines.
  eapply safeExec_bind_reta with (a := by_break tt) in Hrefines.
  - simpl in Hrefines. exact Hrefines.
  - intros Xbody Hbody.
    apply safeExec_choice_l in Hbody.
    eapply safeExec_testst_bind in Hbody.
    + exact Hbody.
    + intros s _. exact Hempty.
Qed.

Lemma dijkstra_dk_map_loop_refines_pop :
  forall g src head_values to_values weight_values next_values
         visited_set dist_values M M_after cur_vertex cur_distance X,
    dk_map_queue_pop_result M M_after cur_vertex cur_distance ->
    dijkstra_dk_map_loop_state g src visited_set dist_values M ->
    dijkstra_dk_map_loop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values M X ->
    dijkstra_dk_map_after_pop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values M_after cur_vertex cur_distance X.
Proof.
  intros g src head_values to_values weight_values next_values
    visited_set dist_values M M_after cur_vertex cur_distance X
    Hpop Hloop_state Hrefines.
  assert (Hnot_empty : ~ partial_map_is_empty M).
  {
    intro Hempty.
    unfold dk_map_queue_pop_result, partial_map_minimum,
      partial_map_item in Hpop.
    destruct Hpop as ((Hpresent & _Hminimum) & _Hafter).
    unfold partial_map_is_empty in Hempty.
    eapply Hempty; exact Hpresent.
  }
  unfold dijkstra_dk_map_loop_refines in Hrefines.
  destruct Hrefines as (Hrefines & Hheap_refines & Hphase).
  unfold dijkstra_dk_map_after_pop_refines.
  split.
  - unfold dijkstra_dk_lfs_loop in Hrefines.
    eapply safeExec_proequiv in Hrefines.
    2: { apply repeat_break_unfold. }
    unfold dijkstra_dk_lfs_loop_body in Hrefines.
    lfs_prog_nf Hrefines.
    apply safeExec_choice_r in Hrefines.
    lfs_prog_nf Hrefines.
    eapply safeExec_testst_bind in Hrefines.
    2: { intros s _. exact Hnot_empty. }
    lfs_prog_nf Hrefines.
    unfold dk_map_queue_pop_choice in Hrefines.
    lfs_prog_nf Hrefines.
    eapply safeExec_get_bind with
      (a := ((M_after, cur_vertex), cur_distance)) in Hrefines.
    2: { intros s _. exact Hpop. }
    cbn in Hrefines.
    lfs_prog_nf Hrefines.
    unfold dijkstra_dk_lfs_after_pop_cont.
    unfold dijkstra_dk_lfs_loop.
    unfold dijkstra_dk_lfs_loop_body.
    unfold dk_map_queue_pop_choice.
    cbn.
    eapply safeExec_proequiv.
    2: { exact Hrefines. }
    symmetry.
    repeat rewrite bind_assoc; reflexivity.
  - exists M.
    split; [exact Hloop_state |].
    split; [exact Hheap_refines |].
    split; [exact Hpop | exact Hphase].
Qed.

Lemma dijkstra_dk_map_after_pop_edge_loop_state :
  forall g edge_count src head_values to_values weight_values next_values
         visited_set visited_set' dist_values M_after
         cur_vertex cur_distance X,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    vertex_valid g cur_vertex ->
    visited_set_add visited_set cur_vertex visited_set' ->
    dijkstra_dk_map_after_pop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values M_after cur_vertex cur_distance X ->
    dijkstra_dk_map_edge_loop_state
      g src visited_set' cur_vertex cur_distance
      (Znth cur_vertex head_values 0) dist_values M_after.
Proof.
  intros g edge_count src head_values to_values weight_values next_values
    visited_set visited_set' dist_values M_after cur_vertex cur_distance X
    Hmodel Hcur_valid _Hvisit_add Hrefines.
  unfold dijkstra_dk_map_after_pop_refines in Hrefines.
  destruct Hrefines as
    (_Hrefines & M_before & Hloop_before & Hexact_before & Hpop & _Hphase).
  assert (Hloop_after :
    dijkstra_dk_map_loop_state g src visited_set dist_values M_after).
  {
    eapply dijkstra_dk_map_loop_state_pop; eauto.
  }
  assert (Hcur_dist : dist_cell dist_values cur_vertex = cur_distance).
  {
    unfold dk_map_queue_pop_result, partial_map_minimum,
      partial_map_item in Hpop.
    destruct Hpop as ((Hpresent & _Hminimum) & _Hafter).
    unfold map_queue_exact_unvisited_dist in Hexact_before.
    destruct Hexact_before as (Hitems & _Hcover).
    specialize (Hitems cur_vertex cur_distance Hpresent)
      as (_Hvalid & _Hunvisited & Hdist & _Hfinite).
    symmetry. exact Hdist.
  }
  assert (Hsize_head : graph_has_size g (Zlength head_values)).
  {
    unfold forward_star_model in Hmodel.
    tauto.
  }
  assert (Hhead_lower : -1 <= Znth cur_vertex head_values 0).
  {
    eapply forward_star_head_0_lower_bound; eauto.
  }
  unfold dijkstra_dk_map_edge_loop_state.
  split; [exact Hloop_after |].
  split; [exact Hcur_valid |].
  split; [exact Hcur_dist | exact Hhead_lower].
Qed.

Lemma dijkstra_dk_map_after_pop_refines_to_edge_loop :
  forall g edge_count src head_values to_values weight_values next_values
         visited_set visited_set' dist_values M_after
         cur_vertex cur_distance X,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    vertex_valid g cur_vertex ->
    visited_set_add visited_set cur_vertex visited_set' ->
    dijkstra_dk_map_after_pop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values M_after cur_vertex cur_distance X ->
    dijkstra_dk_map_edge_loop_refines
      g src cur_vertex cur_distance (Znth cur_vertex head_values 0)
      head_values to_values weight_values next_values
      visited_set' dist_values M_after X.
Proof.
  intros g edge_count src head_values to_values weight_values next_values
    visited_set visited_set' dist_values M_after
    cur_vertex cur_distance X Hmodel Hvalid Hvisit_add Hrefines.
  unfold dijkstra_dk_map_after_pop_refines in Hrefines.
  destruct Hrefines as
    (Hrefines & M_before & Hloop_before & Hexact_before & Hpop & Hphase_before).
  pose proof
    (map_queue_exact_pop_item
      g visited_set dist_values M_before M_after cur_vertex cur_distance
      Hexact_before Hpop)
    as (_Hcur_valid_from_pop & Hunvisited & Hcur_dist_forward & Hcur_finite).
  assert (Hdist : dist_cell dist_values cur_vertex = cur_distance)
    by (symmetry; exact Hcur_dist_forward).
  assert (Hwf : DijkstraGraph.graph_wf g)
    by (unfold dijkstra_dk_map_loop_state in Hloop_before; tauto).
  assert (Hsize_self : graph_has_size g (DijkstraGraph.vertex_count g)).
  {
    unfold graph_has_size.
    split; [reflexivity |].
    destruct Hwf as (Hcount_bound & _).
    exact Hcount_bound.
  }
  assert (Hchain_loc :
    Znth cur_vertex head_values 0 = -1 \/
    next_chain next_values (Znth cur_vertex head_values (-1))
      (Znth cur_vertex head_values 0)).
  {
    eapply forward_star_head_0_nil_or_chain; eauto.
  }
  unfold dijkstra_dk_lfs_after_pop_cont in Hrefines.
  lfs_prog_nf Hrefines.
  apply safeExec_update'_bind in Hrefines.
  lfs_prog_nf Hrefines.
  unfold dijkstra_dk_map_edge_loop_refines.
  split.
  - unfold dijkstra_dk_lfs_edge_loop_cont.
    unfold dijkstra_dk_lfs_loop.
    eapply safeExec_conseq.
    + eapply safeExec_proequiv.
      2: { exact Hrefines. }
      lfs_finish_equiv.
    + intros s (s0 & Hs & Hstate_model).
      subst s.
      apply graph_state_model_visit_state with (visited_set := visited_set);
        auto.
  - split.
    + eapply map_queue_exact_pop_visit; eauto.
    + destruct Hphase_before as
        [(Hempty & Hinit & Hno_overflow & Hsingleton) |
         (Hvisited_valid & Hno_overflow & Hmath)].
      * pose proof Hpop as Hpop_singleton.
        rewrite Hsingleton in Hpop_singleton.
        pose proof
          (singleton_source_map_pop
            src M_after cur_vertex cur_distance Hpop_singleton)
          as (_Hmap_empty & Hcur_vertex & Hcur_distance).
        subst cur_vertex cur_distance.
        split; [unfold DijkstraGraph.infinity; lia |].
        left.
        split.
        -- intro v.
           unfold visited_set_add in Hvisit_add.
           split.
           ++ intro Hv.
              apply Hvisit_add in Hv as [Hv_old | Hv_src].
              ** exfalso. apply (Hempty v). exact Hv_old.
              ** exact Hv_src.
           ++ intro Hv.
              apply Hvisit_add. right. exact Hv.
        -- split; [exact Hno_overflow |].
           split; [reflexivity |].
           split; [exact Hcur_distance |].
           split; [exact Hchain_loc |].
           eapply dijkstra_first_step_math_state_done_equiv.
           ++ intros e_abs.
              symmetry.
              eapply forward_star_done_edge_set_head_empty_equiv; eauto.
           ++ eapply dijkstra_init_dist_first_step_math_state_empty;
                eauto.
      * split; [exact Hcur_finite |].
        right.
        exists visited_set, dist_values.
        split; [exact Hvisited_valid |].
        split; [exact Hno_overflow |].
        split; [exact Hvisit_add |].
        split; [exact Hcur_dist_forward |].
        split; [exact Hchain_loc |].
        assert (Hselected :
          dijkstra_selected_min g visited_set dist_values cur_vertex).
        {
          eapply map_queue_pop_selected_min
            with (vertex_count := DijkstraGraph.vertex_count g)
                 (M_after := M_after);
            eauto;
            try exact Hsize_self;
            try exact Hcur_dist_forward;
            try exact Hcur_finite.
        }
        eapply (dijkstra_edge_math_state_done_equiv
          g src visited_set visited_set' cur_vertex dist_values
          (fun _ : DijkstraGraph.E => False)
          (forward_star_done_edge_set
            head_values to_values weight_values next_values
            cur_vertex (Znth cur_vertex head_values 0))
          dist_values).
        -- intros e_abs.
           symmetry.
           eapply forward_star_done_edge_set_head_empty_equiv; eauto.
        -- unfold dijkstra_edge_math_state, Dijkstra.relax_step_invariant.
           split; [exact Hvisit_add |].
           split; [exact Hmath |].
           split; [exact Hselected |].
           split.
           ++ unfold dijkstra_after_visit_state, set_state_visited,
                dijkstra_array_state; simpl; sets_unfold.
              intro v; split.
              ** intros [Hvalid_after Hvisited_after].
                 unfold visited_set_add in Hvisit_add.
                 apply Hvisit_add in Hvisited_after as
                   [Hvisited_before | Heq].
                 { left; split; [apply Hvisited_valid |];
                   exact Hvisited_before. }
                 { right; symmetry; exact Heq. }
              ** intros [[Hvalid_before Hvisited_before] | Heq];
                   subst.
                 { split; [exact Hvalid_before |].
                   unfold visited_set_add in Hvisit_add.
                   apply Hvisit_add; left; exact Hvisited_before. }
                 { split; [exact Hvalid |].
                   unfold visited_set_add in Hvisit_add.
                   apply Hvisit_add; right; reflexivity. }
           ++ split; [reflexivity |].
              split.
              ** intros v e _ Hfalse _. contradiction.
              ** intros v _ _.
                 unfold dijkstra_after_visit_state, set_state_visited,
                   dijkstra_array_state; simpl.
                 destruct (vertex_valid_dec g v); reflexivity.
Qed.

Lemma dijkstra_dk_map_edge_phase_relax_update :
  forall g vertex_count edge_count src cur_vertex cur_distance edge
         neighbor edge_weight candidate
         head_values to_values weight_values next_values
         visited_set dist_values M,
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
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values M ->
    dijkstra_dk_map_edge_phase_state
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values M ->
    dijkstra_dk_map_edge_phase_state
      g src cur_vertex cur_distance (Znth edge next_values 0)
      head_values to_values weight_values next_values
      visited_set (replace_Znth neighbor candidate dist_values) M.
Proof.
  intros g vertex_count edge_count src cur_vertex cur_distance edge
    neighbor edge_weight candidate head_values to_values weight_values
    next_values visited_set dist_values M Hsize Hmodel Hedge_index
    Hedge_not_nil Hneighbor Hweight Hcandidate Hneighbor_valid
    Hneighbor_storage Hunvisited Hcandidate_bounds Hweight_nonneg Hrelax
    Hedge_state Hphase.
  subst neighbor edge_weight candidate.
  assert (Hcur_valid : vertex_valid g cur_vertex)
    by (unfold dijkstra_dk_map_edge_loop_state in Hedge_state; tauto).
  assert (Hnonneg : nonnegative_edges g)
    by (unfold dijkstra_dk_map_edge_loop_state,
          dijkstra_dk_map_loop_state in Hedge_state; tauto).
  assert (Hloop_state :
    dijkstra_dk_map_loop_state g src visited_set dist_values M)
    by (eapply dijkstra_dk_map_edge_loop_to_loop_state; eauto).
  assert (Hshape : vector_shape dist_values)
    by (unfold dijkstra_dk_map_loop_state in Hloop_state; tauto).
  assert (Hsafe : dist_values_safe dist_values)
    by (unfold dijkstra_dk_map_loop_state in Hloop_state; tauto).
  assert (Hcur_dist : dist_cell dist_values cur_vertex = cur_distance)
    by (unfold dijkstra_dk_map_edge_loop_state in Hedge_state; tauto).
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
    assert (Hhead_edge :
      next_chain next_values (Znth src head_values (-1)) edge)
      by (destruct Hchain as [Hnil | Hchain];
          [contradiction | exact Hchain]).
    pose proof
      (forward_star_current_edge_facts
        g vertex_count edge_count head_values to_values weight_values
        next_values src edge Hsize Hmodel Hcur_valid Hhead_edge
        Hedge_index)
      as (_Hchain_wf & _Hsrc_storage & _Hedge_to & _Hedge_next
          & _Hneighbor_valid0 & _Hneighbor_storage0 & Hstep
          & Hweight_edge & _Hnext_eq).
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
      by (destruct Hchain as [Hnil | Hchain];
          [contradiction | exact Hchain]).
    pose proof
      (forward_star_current_edge_facts
        g vertex_count edge_count head_values to_values weight_values
        next_values cur_vertex edge Hsize Hmodel Hcur_valid Hhead_edge
        Hedge_index)
      as (_Hchain_wf & _Hcur_storage0 & _Hedge_to & _Hedge_next
          & Hneighbor_valid0 & Hneighbor_storage0 & Hstep
          & Hweight_edge & _Hnext_eq).
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

Lemma dijkstra_dk_map_edge_phase_candidate_bounds :
  forall g vertex_count edge_count src cur_vertex cur_distance edge
         head_values to_values weight_values next_values
         visited_set dist_values M,
    graph_has_size g vertex_count ->
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_index edge_count edge ->
    edge <> -1 ->
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values M ->
    dijkstra_dk_map_edge_phase_state
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values M ->
    0 <= cur_distance + Znth edge weight_values 0 <
      DijkstraGraph.infinity.
Proof.
  intros g vertex_count edge_count src cur_vertex cur_distance edge
    head_values to_values weight_values next_values visited_set dist_values
    M Hsize Hmodel Hedge_index Hedge_not_nil Hedge_state Hphase.
  assert (Hcur_valid : vertex_valid g cur_vertex)
    by (unfold dijkstra_dk_map_edge_loop_state in Hedge_state; tauto).
  assert (Hnonneg : nonnegative_edges g)
    by (unfold dijkstra_dk_map_edge_loop_state,
          dijkstra_dk_map_loop_state in Hedge_state; tauto).
  destruct Hphase as
    (Hcur_finite_phase &
    [(Hvisited_src & Hno_overflow & Hcur_src & Hcur_zero & Hchain & _Hfirst) |
     (visited_before & base_dist_values & _Hvisited_valid & Hno_overflow
      & _Hvisit_add & Hcur_base & Hchain & Hmath)]).
  - subst cur_vertex cur_distance.
    assert (Hhead_edge :
      next_chain next_values (Znth src head_values (-1)) edge)
      by (destruct Hchain as [Hnil | Hchain];
          [contradiction | exact Hchain]).
    pose proof
      (forward_star_current_edge_facts
        g vertex_count edge_count head_values to_values weight_values
        next_values src edge Hsize Hmodel Hcur_valid Hhead_edge
        Hedge_index)
      as (_ & _ & _ & _ & Hneighbor_valid & _ & Hstep & Hweight & _).
    apply (Hno_overflow src (Znth edge to_values 0)
      (src, Znth edge to_values 0) 0 (Znth edge weight_values 0));
      [exact Hcur_valid | exact Hneighbor_valid | exact Hstep
      | dijkstra_dk_min_epath_refl;
        eauto using forward_star_model_graph_wf
      | exact Hweight].
  - assert (Hhead_edge :
      next_chain next_values (Znth cur_vertex head_values (-1)) edge)
      by (destruct Hchain as [Hnil | Hchain];
          [contradiction | exact Hchain]).
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
        ltac:(unfold dijkstra_dk_map_edge_loop_state,
               dijkstra_dk_map_loop_state in Hedge_state; tauto)
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

Lemma dijkstra_dk_map_skip_assume_to_dist_cell_pure :
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

Lemma dijkstra_dk_map_edge_phase_skip_update :
  forall g edge_count src cur_vertex cur_distance edge
         head_values to_values weight_values next_values
         visited_set dist_values M,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_index edge_count edge ->
    edge <> -1 ->
    vertex_valid g (Znth edge to_values 0) ->
    Znth edge weight_values 0 < 0 \/
      cur_distance > DijkstraGraph.infinity - Znth edge weight_values 0 \/
      cur_distance + Znth edge weight_values 0 >=
        dist_cell dist_values (Znth edge to_values 0) ->
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values M ->
    dijkstra_dk_map_edge_phase_state
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values M ->
    dijkstra_dk_map_edge_phase_state
      g src cur_vertex cur_distance (Znth edge next_values 0)
      head_values to_values weight_values next_values
      visited_set dist_values M.
Proof.
  intros g edge_count src cur_vertex cur_distance edge
    head_values to_values weight_values next_values visited_set dist_values
    M Hmodel Hedge_index Hedge_not_nil Hneighbor_valid Hskip
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
    by (unfold dijkstra_dk_map_edge_loop_state in Hedge_state; tauto).
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
    as (_Hchain_wf & _Hcur_storage & _Hedge_to & _Hedge_next
        & Hneighbor_valid0 & _Hneighbor_storage & Hstep & Hweight
        & _Hnext_eq).
  pose proof Hphase as Hphase_full.
  pose proof
    (dijkstra_dk_map_edge_phase_candidate_bounds
      g (DijkstraGraph.vertex_count g) edge_count src cur_vertex
      cur_distance edge head_values to_values weight_values next_values
      visited_set dist_values M
      Hsize_self Hmodel Hedge_index Hedge_not_nil Hedge_state Hphase_full)
    as Hcandidate_bounds.
  assert (Hskip_cell :
    dist_cell dist_values (Znth edge to_values 0) <=
      cur_distance + Znth edge weight_values 0)
    by (eapply dijkstra_dk_map_skip_assume_to_dist_cell_pure; eauto).
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
        -- unfold dijkstra_dk_map_edge_loop_state,
             dijkstra_dk_map_loop_state in Hedge_state; tauto.
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

Lemma dijkstra_dk_map_edge_phase_relax_neighbor_unvisited :
  forall g vertex_count edge_count src cur_vertex cur_distance edge
         head_values to_values weight_values next_values
         visited_set dist_values M,
    graph_has_size g vertex_count ->
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_index edge_count edge ->
    edge <> -1 ->
    cur_distance + Znth edge weight_values 0 <
      dist_cell dist_values (Znth edge to_values 0) ->
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values M ->
    dijkstra_dk_map_edge_phase_state
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values M ->
    ~ visited_set (Znth edge to_values 0).
Proof.
  intros g vertex_count edge_count src cur_vertex cur_distance edge
    head_values to_values weight_values next_values visited_set dist_values
    M Hsize Hmodel Hedge_index Hedge_not_nil Hrelax Hedge_state Hphase.
  assert (Hcur_valid : vertex_valid g cur_vertex)
    by (unfold dijkstra_dk_map_edge_loop_state in Hedge_state; tauto).
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
    by (unfold dijkstra_dk_map_edge_loop_state in Hedge_state; tauto).
  assert (Hnonneg : nonnegative_edges g)
    by (unfold dijkstra_dk_map_edge_loop_state,
          dijkstra_dk_map_loop_state in Hedge_state; tauto).
  destruct Hphase as
    (Hcur_finite &
    [(Hvisited_src & _Hno_overflow & Hcur_src & _Hcur_zero & _ & _Hfirst) |
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

Lemma dijkstra_dk_map_edge_loop_refines_relax_to_after_relax :
  forall g vertex_count edge_count src cur_vertex cur_distance edge neighbor
         edge_weight candidate
         head_values to_values weight_values next_values visited_set dist_values
         M X,
    graph_has_size g vertex_count ->
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_index edge_count edge ->
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values M ->
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
    dijkstra_dk_map_edge_loop_refines
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values M X ->
    dijkstra_dk_map_after_relax_refines
      g src cur_vertex cur_distance edge neighbor candidate
      head_values to_values weight_values next_values
      visited_set (replace_Znth neighbor candidate dist_values) M X.
Proof.
  intros g vertex_count edge_count src cur_vertex cur_distance edge neighbor
    edge_weight candidate head_values to_values weight_values next_values
    visited_set dist_values M X Hsize Hmodel Hedge_index Hedge_state
    Hedge_not_nil Hneighbor Hweight Hcandidate Hvalid Hstorage
    Hcandidate_bounds Hweight_nonneg Hoverflow Hrelax Hrefines.
  subst neighbor edge_weight candidate.
  unfold dijkstra_dk_map_edge_loop_refines in Hrefines.
  destruct Hrefines as (Hrefines & Hexact & Hphase).
  assert (Hunvisited : ~ visited_set (Znth edge to_values 0))
    by (eapply dijkstra_dk_map_edge_phase_relax_neighbor_unvisited; eauto).
  eapply safeExec_proequiv in Hrefines.
  2: {
    apply dijkstra_dk_lfs_edge_loop_cont_unfold.
  }
  unfold dijkstra_dk_lfs_edge_body in Hrefines.
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
  unfold dijkstra_dk_lfs_edge_loop_after_body_cont in Hrefines.
  change (safeExec
    (fun s : state =>
       exists s0 : state,
         s = set_state_distance (Znth edge to_values 0)
               (cur_distance + Znth edge weight_values 0) s0 /\
         graph_state_model g visited_set dist_values s0)
    (M_after <-
       dk_map_queue_update_or_push_choice M (Znth edge to_values 0)
         (cur_distance + Znth edge weight_values 0);;
     dijkstra_dk_lfs_edge_loop_cont head_values to_values weight_values
       next_values cur_vertex cur_distance (Znth edge next_values 0)
       M_after)
    X) in Hrefines.
  unfold dijkstra_dk_map_after_relax_refines.
  split.
  - eapply safeExec_conseq.
    + exact Hrefines.
    + intros s (s0 & Hs & Hstate_model).
      subst s.
      eapply graph_state_model_replace_Znth_set_state_distance; eauto.
  - intros M_after Hupdate_any.
    assert (Hshape_old : vector_shape dist_values)
      by (unfold dijkstra_dk_map_edge_loop_state,
            dijkstra_dk_map_loop_state in Hedge_state; tauto).
    split.
    + eapply map_queue_exact_update_or_push.
      * exact Hsize.
      * exact Hshape_old.
      * exact Hstorage.
      * exact Hvalid.
      * exact Hunvisited.
      * exact Hrelax.
      * lia.
      * exact Hexact.
      * exact Hupdate_any.
    + eapply (dijkstra_dk_map_edge_phase_relax_update
        g vertex_count edge_count src cur_vertex cur_distance edge
        (Znth edge to_values 0) (Znth edge weight_values 0)
        (cur_distance + Znth edge weight_values 0)
        head_values to_values weight_values next_values
        visited_set dist_values M); eauto.
Qed.

Lemma dijkstra_dk_map_after_relax_refines_update_to_edge_loop :
  forall g edge_count src cur_vertex cur_distance edge neighbor candidate
         head_values to_values weight_values next_values visited_set dist_values
         M M_after size_before size_after X,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    vertex_valid g cur_vertex ->
    edge_index edge_count edge ->
    neighbor = Znth edge to_values 0 ->
    dk_map_queue_update_or_push_result
      M M_after size_before size_after neighbor candidate ->
    dijkstra_dk_map_after_relax_refines
      g src cur_vertex cur_distance edge neighbor candidate
      head_values to_values weight_values next_values
      visited_set dist_values M X ->
    dijkstra_dk_map_edge_loop_refines
      g src cur_vertex cur_distance (Znth edge next_values 0)
      head_values to_values weight_values next_values
      visited_set dist_values M_after X.
Proof.
  intros g edge_count src cur_vertex cur_distance edge neighbor candidate
    head_values to_values weight_values next_values visited_set dist_values
    M M_after size_before size_after X _Hmodel _Hcur_valid _Hedge_index
    _Hneighbor Hupdate Hrefines.
  assert (Hupdate_any :
    dk_map_queue_update_or_push_result_any M M_after neighbor candidate).
  {
    unfold dk_map_queue_update_or_push_result_any.
    exists size_before, size_after.
    exact Hupdate.
  }
  unfold dijkstra_dk_map_after_relax_refines in Hrefines.
  destruct Hrefines as (Hrefines & Hafter).
  unfold dijkstra_dk_map_edge_loop_refines.
  split.
  - unfold dk_map_queue_update_or_push_choice in Hrefines.
    lfs_prog_nf Hrefines.
    eapply safeExec_get_bind with (a := M_after) in Hrefines.
    2: { intros s _. exact Hupdate_any. }
    cbn in Hrefines.
    exact Hrefines.
  - exact (Hafter M_after Hupdate_any).
Qed.

Lemma dijkstra_dk_map_edge_loop_refines_no_relax_to_next :
  forall g edge_count src cur_vertex cur_distance edge neighbor edge_weight
         head_values to_values weight_values next_values visited_set dist_values
         M X,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge_index edge_count edge ->
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values M ->
    edge <> -1 ->
    neighbor = Znth edge to_values 0 ->
    edge_weight = Znth edge weight_values 0 ->
    vertex_valid g neighbor ->
    (edge_weight < 0 \/
      cur_distance > DijkstraGraph.infinity - edge_weight \/
      cur_distance + edge_weight >= dist_cell dist_values neighbor) ->
    dijkstra_dk_map_edge_loop_refines
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values M X ->
    dijkstra_dk_map_edge_loop_refines
      g src cur_vertex cur_distance (Znth edge next_values 0)
      head_values to_values weight_values next_values
      visited_set dist_values M X.
Proof.
  intros g edge_count src cur_vertex cur_distance edge neighbor edge_weight
    head_values to_values weight_values next_values visited_set dist_values
    M X Hmodel Hedge_index Hedge_state Hedge_not_nil Hneighbor
    Hweight Hvalid Hskip Hrefines.
  subst neighbor edge_weight.
  pose proof Hrefines as Hrefines_full.
  unfold dijkstra_dk_map_edge_loop_refines in Hrefines_full.
  destruct Hrefines_full as (Hrefines_safe & Hexact & Hphase).
  assert (Hbody_step :
    graph_state_model g visited_set dist_values -@
      dijkstra_dk_lfs_edge_body
        head_values to_values weight_values next_values
        cur_vertex cur_distance (edge, M)
      -⥅ graph_state_model g visited_set dist_values
      ♯ by_continue (Znth edge next_values 0, M)).
  {
    unfold dijkstra_dk_lfs_edge_body.
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
  unfold dijkstra_dk_map_edge_loop_refines,
    dijkstra_dk_lfs_edge_loop_cont, dijkstra_dk_lfs_edge_loop.
  split.
  - change (safeExec (graph_state_model g visited_set dist_values)
      (dijkstra_dk_lfs_edge_loop_after_body_cont head_values to_values
        weight_values next_values cur_vertex cur_distance
        (by_continue (Znth edge next_values 0, M))) X).
    eapply highstepbind_derive; eauto.
    eapply safeExec_proequiv.
    + apply dijkstra_dk_lfs_edge_loop_cont_unfold.
    + exact Hrefines_safe.
  - split; [exact Hexact |].
    eapply dijkstra_dk_map_edge_phase_skip_update; eauto.
Qed.

Lemma dijkstra_dk_map_edge_loop_refines_after_body :
  forall g src cur_vertex cur_distance edge
         head_values to_values weight_values next_values
         visited_set dist_values M X result Q,
    graph_state_model g visited_set dist_values -@
      dijkstra_dk_lfs_edge_body
        head_values to_values weight_values next_values
        cur_vertex cur_distance (edge, M)
      -⥅ Q ♯ result ->
    dijkstra_dk_map_edge_loop_refines
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values M X ->
    safeExec Q
      (dijkstra_dk_lfs_edge_loop_after_body_cont
        head_values to_values weight_values next_values
        cur_vertex cur_distance result)
      X.
Proof.
  intros g src cur_vertex cur_distance edge
    head_values to_values weight_values next_values
    visited_set dist_values M X result Q Hbody Hrefines.
  unfold dijkstra_dk_map_edge_loop_refines in Hrefines.
  destruct Hrefines as (Hrefines & _Hexact & _Hphase).
  eapply highstepbind_derive; eauto.
  eapply safeExec_proequiv.
  - apply dijkstra_dk_lfs_edge_loop_cont_unfold.
  - exact Hrefines.
Qed.

Lemma dijkstra_dk_map_edge_phase_finish_to_loop_phase :
  forall g edge_count src cur_vertex cur_distance edge
         head_values to_values weight_values next_values visited_set dist_values
         M,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values M ->
    edge = -1 ->
    dijkstra_dk_map_edge_phase_state
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values M ->
    dijkstra_dk_map_loop_phase_state g src visited_set dist_values M.
Proof.
  intros g edge_count src cur_vertex cur_distance edge
    head_values to_values weight_values next_values visited_set dist_values
    M Hmodel Hedge_state Hedge_nil Hphase.
  unfold dijkstra_dk_map_edge_loop_state in Hedge_state.
  destruct Hedge_state as (Hloop_state & Hcur_valid & _Hcur_dist & _).
  unfold dijkstra_dk_map_loop_state in Hloop_state.
  destruct Hloop_state as (Hwf & Hsrc_valid & Hnonneg & _).
  unfold dijkstra_dk_map_edge_phase_state in Hphase.
  destruct Hphase as (_Hcur_finite & Hphase).
  right.
  destruct Hphase as [Hinitial | Hnormal].
  - destruct Hinitial as
      (Hvisited_src & Hbounded & Hcur_src & _Hcur_zero
       & _Hchain & Hfirst).
    subst cur_vertex edge.
    assert (Hvisited_eq : visited_set = source_visited_set src).
    {
      apply functional_extensionality.
      intro v.
      apply propositional_extensionality.
      exact (Hvisited_src v).
    }
    split.
    + unfold visited_set_valid.
      intros v Hv.
      apply Hvisited_src in Hv.
      subst v.
      exact Hsrc_valid.
    + split; [exact Hbounded |].
      rewrite Hvisited_eq.
      eapply dijkstra_first_step_full_done_to_math; eauto.
      eapply dijkstra_first_step_math_state_done_equiv.
      * intros e.
        eapply forward_star_done_edge_set_minus_one_equiv_step_aux; eauto.
      * exact Hfirst.
  - destruct Hnormal as
      (visited_before & base_dist_values & Hvisited_before_valid
       & Hbounded & Hvisit_add & _Hcur_distance & _Hchain & Hedge_math).
    subst edge.
    split.
    + unfold visited_set_valid.
      intros v Hv.
      unfold visited_set_add in Hvisit_add.
      apply Hvisit_add in Hv as [Hvisited_before | Heq].
      * exact (Hvisited_before_valid v Hvisited_before).
      * subst v. exact Hcur_valid.
    + split; [exact Hbounded |].
      eapply dijkstra_edge_math_state_full_done_to_math; eauto.
      intros e.
      eapply forward_star_done_edge_set_minus_one_equiv_step_aux; eauto.
Qed.

Lemma dijkstra_dk_map_edge_loop_refines_break_to_loop :
  forall g edge_count src cur_vertex cur_distance edge
         head_values to_values weight_values next_values visited_set dist_values
         M X,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values M ->
    edge = -1 ->
    dijkstra_dk_map_edge_loop_refines
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values M X ->
    dijkstra_dk_map_loop_refines
      g src head_values to_values weight_values next_values
      visited_set dist_values M X.
Proof.
  intros g edge_count src cur_vertex cur_distance edge
    head_values to_values weight_values next_values visited_set dist_values
    M X Hmodel Hedge_state Hedge_nil Hrefines.
  pose proof Hrefines as Hrefines_full.
  unfold dijkstra_dk_map_edge_loop_refines in Hrefines_full.
  destruct Hrefines_full as (_Hrefines_safe & Hexact & Hphase).
  assert (Hbody_step :
    graph_state_model g visited_set dist_values -@
      dijkstra_dk_lfs_edge_body
        head_values to_values weight_values next_values
        cur_vertex cur_distance (edge, M)
      -⥅ graph_state_model g visited_set dist_values
      ♯ by_break M).
  {
    unfold dijkstra_dk_lfs_edge_body.
    apply hsevalchoice_left_derive.
    eapply hsevalbind_derive'.
    + apply hs_eval_assume_state.
      intros s _.
      exact Hedge_nil.
    + apply highret_eval2.
  }
  unfold dijkstra_dk_map_loop_refines.
  split.
  - eapply safeExec_proequiv.
    2: { eapply dijkstra_dk_map_edge_loop_refines_after_body; eauto. }
    unfold dijkstra_dk_lfs_edge_loop_after_body_cont.
    rewrite ret_equiv.
    reflexivity.
  - split; [exact Hexact |].
    eapply dijkstra_dk_map_edge_phase_finish_to_loop_phase; eauto.
Qed.

Definition dijkstra_dk_map_loop_math_bridge_state
    (g : DijkstraGraph.G) (src : Z) (visited_set : Z -> Prop)
    (dist_values : list Z) (M : partial_map) : Prop :=
  dijkstra_dk_map_loop_state g src visited_set dist_values M /\
  map_queue_exact_unvisited_dist g visited_set dist_values M /\
  visited_set_valid g visited_set /\
  dijkstra_math_invariant g src visited_set dist_values.

Definition dijkstra_dk_map_loop_math_model
    (g : DijkstraGraph.G) (src : Z)
    (M : partial_map) (s : state) : Prop :=
  exists visited_set dist_values,
    graph_state_model g visited_set dist_values s /\
    dijkstra_dk_map_loop_math_bridge_state
      g src visited_set dist_values M.

Lemma dijkstra_dk_map_loop_math_model_empty_to_shortest :
  forall g vertex_count src dist_out M s,
    graph_has_size g vertex_count ->
    vertex_valid g src ->
    graph_dist_model g dist_out s ->
    partial_map_is_empty M ->
    dijkstra_dk_map_loop_math_model g src M s ->
    dijkstra_shortest_dist g src dist_out.
Proof.
  intros g vertex_count src dist_out M s Hsize Hsrc Hdist_out
    Hempty Hloop.
  assert (Hlist_loop : dijkstra_loop_math_model g src nil s).
  {
    unfold dijkstra_dk_map_loop_math_model in Hloop.
    destruct Hloop as
      (visited_set & dist_values & Hstate & Hbridge_math).
    exists visited_set, dist_values.
    split; [exact Hstate |].
    unfold dijkstra_dk_map_loop_math_bridge_state in Hbridge_math.
    destruct Hbridge_math as
      (Hloop_state & Hexact & Hvisited_valid & Hmath).
    unfold dijkstra_loop_math_bridge_state.
    split.
    - unfold dijkstra_loop_bridge_state.
      split.
      + unfold dijkstra_dk_map_loop_state in Hloop_state.
        destruct Hloop_state as
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
      + unfold priority_queue_refines_unvisited_dist.
        destruct Hexact as (_Hitems & Hcovers).
        repeat split.
        * intros v Hvalid Hunvisited Hfinite.
          exfalso.
          pose proof (Hcovers v Hvalid Hunvisited Hfinite) as Hpresent.
          unfold partial_map_is_empty in Hempty.
          exact (Hempty v (dist_cell dist_values v) Hpresent).
        * intros d v Hin _; contradiction.
        * intros d v Hin; contradiction.
        * intros d v Hin; contradiction.
        * constructor.
    - split; assumption.
  }
  eapply dijkstra_loop_math_model_nil_to_shortest; eauto.
Qed.

Lemma partial_map_is_empty_ext :
  forall M,
    partial_map_is_empty M ->
    M = partial_map_empty.
Proof.
  intros M Hempty.
  apply functional_extensionality.
  intro data_x.
  unfold partial_map_empty.
  destruct (M data_x) as [key_x |] eqn:Hget; [| reflexivity].
  exfalso.
  unfold partial_map_is_empty in Hempty.
  apply (Hempty data_x key_x).
  unfold partial_map_present, partial_map_get.
  exact Hget.
Qed.

Lemma map_queue_exact_empty_after_source_initial :
  forall g vertex_count src,
    graph_has_size g vertex_count ->
    vertex_valid g src ->
    map_queue_exact_unvisited_dist
      g (source_visited_set src) (initial_dist_values src)
      partial_map_empty.
Proof.
  intros g vertex_count src Hsize Hsrc.
  assert (Hsrc_storage : storage_index src)
    by (eapply graph_has_size_vertex_valid_storage; eauto).
  unfold map_queue_exact_unvisited_dist.
  split.
  - intros data_x key_x Hpresent.
    unfold partial_map_present, partial_map_get, partial_map_empty
      in Hpresent.
    discriminate.
  - intros v Hvalid Hunvisited Hfinite.
    exfalso.
    pose proof
      (graph_has_size_vertex_valid_storage g vertex_count v Hsize Hvalid)
      as Hv_storage.
    rewrite initial_dist_values_cell in Hfinite
      by (exact Hsrc_storage || exact Hv_storage).
    destruct (Z.eq_dec v src) as [Heq | _Hneq].
    + apply Hunvisited.
      unfold source_visited_set.
      exact Heq.
    + unfold DijkstraGraph.infinity in Hfinite; lia.
Qed.

Definition dijkstra_dk_map_edge_loop_math_model
    (g : DijkstraGraph.G) (src cur_vertex cur_distance edge : Z)
    (head_values to_values weight_values next_values : list Z)
    (visited_set : Z -> Prop) (M : partial_map)
    (s : state) : Prop :=
  exists dist_values,
    graph_state_model g visited_set dist_values s /\
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values M /\
    map_queue_exact_unvisited_dist g visited_set dist_values M /\
    dijkstra_dk_map_edge_phase_state
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values M.

Lemma dijkstra_dk_map_edge_phase_current_chain :
  forall g src cur_vertex cur_distance edge
         head_values to_values weight_values next_values
         visited_set dist_values M,
    edge <> -1 ->
    dijkstra_dk_map_edge_phase_state
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values M ->
    next_chain next_values (Znth cur_vertex head_values (-1)) edge.
Proof.
  intros g src cur_vertex cur_distance edge
    head_values to_values weight_values next_values
    visited_set dist_values M Hedge_not_nil Hphase.
  unfold dijkstra_dk_map_edge_phase_state in Hphase.
  destruct Hphase as
    (_ & [(Hvisited_src & _ & Hcur_src & _ & Hchain & _) |
          (visited_before & base_dist_values & _ & _ & _ & _
           & Hchain & _)]).
  - subst cur_vertex.
    destruct Hchain as [Hnil | Hchain].
    + contradiction.
    + exact Hchain.
  - destruct Hchain as [Hnil | Hchain].
    + contradiction.
    + exact Hchain.
Qed.

Lemma dijkstra_dk_map_edge_loop_math_finish :
  forall g edge_count src cur_vertex cur_distance edge
         head_values to_values weight_values next_values visited_set
         dist_values M s,
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    edge = -1 ->
    graph_state_model g visited_set dist_values s ->
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values M ->
    map_queue_exact_unvisited_dist g visited_set dist_values M ->
    dijkstra_dk_map_edge_phase_state
      g src cur_vertex cur_distance edge
      head_values to_values weight_values next_values
      visited_set dist_values M ->
    dijkstra_dk_map_loop_math_model g src M s.
Proof.
  intros g edge_count src cur_vertex cur_distance edge
    head_values to_values weight_values next_values visited_set
    dist_values M s Hmodel Hedge_nil Hstate Hedge_state Hexact Hphase.
  unfold dijkstra_dk_map_loop_math_model.
  exists visited_set, dist_values.
  split; [exact Hstate |].
  unfold dijkstra_dk_map_loop_math_bridge_state.
  unfold dijkstra_dk_map_edge_loop_state in Hedge_state.
  destruct Hedge_state as (Hloop_state & Hcur_valid & _Hcur_dist & _).
  split; [exact Hloop_state |].
  split; [exact Hexact |].
  unfold dijkstra_dk_map_edge_phase_state in Hphase.
  destruct Hphase as
    (_Hcur_finite &
    [(Hvisited_src & Hbounded & Hcur_src & _Hcur_zero
       & _Hchain & Hfirst) |
     (visited_before & base_dist_values & Hvisited_before_valid
      & Hbounded & Hvisit_add & _Hcur_base & _Hchain & Hedge_math)]).
  - subst cur_vertex edge.
    split.
    + unfold visited_set_valid.
      intros v Hv.
      apply Hvisited_src in Hv.
      subst v.
      unfold dijkstra_dk_map_loop_state in Hloop_state; tauto.
    + assert (Hvisited_eq : visited_set = source_visited_set src).
      {
        apply functional_extensionality.
        intro v.
        apply propositional_extensionality.
        exact (Hvisited_src v).
      }
      rewrite Hvisited_eq.
      eapply dijkstra_first_step_full_done_to_math; eauto.
      * unfold dijkstra_dk_map_loop_state in Hloop_state; tauto.
      * unfold dijkstra_dk_map_loop_state in Hloop_state; tauto.
      * eapply dijkstra_first_step_math_state_done_equiv.
        -- intros e_abs.
           eapply forward_star_done_edge_set_minus_one_equiv_step_aux;
             eauto.
        -- exact Hfirst.
  - subst edge.
    split.
    + unfold visited_set_valid.
      intros v Hv.
      unfold visited_set_add in Hvisit_add.
      apply Hvisit_add in Hv as [Hv_before | Heq].
      * apply Hvisited_before_valid; exact Hv_before.
      * subst v. exact Hcur_valid.
    + eapply dijkstra_edge_math_state_full_done_to_math.
      * unfold dijkstra_dk_map_loop_state in Hloop_state; tauto.
      * unfold dijkstra_dk_map_loop_state in Hloop_state; tauto.
      * intros e_abs.
        eapply forward_star_done_edge_set_minus_one_equiv_step_aux; eauto.
      * exact Hedge_math.
Qed.

Lemma dijkstra_dk_map_edge_loop_state_with_items :
  forall g src visited_set cur_vertex cur_distance edge dist_values M,
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values M ->
    map_queue_items_valid g M ->
    dijkstra_dk_map_edge_loop_state
      g src visited_set cur_vertex cur_distance edge dist_values M.
Proof.
  intros; exact H.
Qed.

Section DijkstraDecreaseKeyProgramProofs.

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

Ltac dijkstra_dk_edge_body_hoare :=
  unfold dijkstra_dk_lfs_edge_body;
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
        | intros M_after;
          apply Hoare_ret';
          intros s Hpost;
          destruct Hpost as (Hupdate & s0 & Hset & Hpre);
          destruct Hpre as (Hrelax_assume & Hedge_not_nil & Hpre);
          cbn [fst snd] in Hupdate, Hrelax_assume, Hedge_not_nil;
          subst s ] ]
    | apply Hoare_assume_bind;
      apply Hoare_ret';
      intros s [Hskip [Hedge_not_nil Hpre]];
      cbn [fst snd] in Hskip, Hedge_not_nil ] ].

Ltac pose_dk_edge_current_facts edge cur_vertex Hphase Hedge_state Hedge_not_nil :=
  let Hcur_valid := fresh "Hcur_valid" in
  let Hhead_edge := fresh "Hhead_edge" in
  let Hedge_index := fresh "Hedge_index" in
  assert (Hcur_valid : vertex_valid g cur_vertex)
    by (unfold dijkstra_dk_map_edge_loop_state in Hedge_state; tauto);
  assert (Hhead_edge :
    next_chain next_values (Znth cur_vertex head_values (-1)) edge)
    by (eapply dijkstra_dk_map_edge_phase_current_chain; eauto);
  assert (Hedge_index : edge_index edge_count edge)
    by (eapply forward_star_next_chain_edge_index; eauto);
  pose proof
    (forward_star_current_edge_facts
      g vertex_count edge_count head_values to_values weight_values
      next_values cur_vertex edge Hsize Hmodel Hcur_valid Hhead_edge
      Hedge_index)
    as (_Hchain_wf & _Hcur_storage & _Hedge_to & _Hedge_next
        & Hneighbor_valid & Hneighbor_storage & Hstep & Hweight
        & _Hnext_eq).

Lemma dijkstra_dk_lfs_edge_body_math_step :
  forall cur_vertex cur_distance edge visited_set M,
    Hoare
      (dijkstra_dk_map_edge_loop_math_model
        g src cur_vertex cur_distance edge
        head_values to_values weight_values next_values
        visited_set M)
      (dijkstra_dk_lfs_edge_body
        head_values to_values weight_values next_values
        cur_vertex cur_distance (edge, M))
      (fun result s =>
        match result with
        | by_continue acc =>
            dijkstra_dk_map_edge_loop_math_model
              g src cur_vertex cur_distance (fst acc)
              head_values to_values weight_values next_values
              visited_set (snd acc) s
        | by_break M_done =>
            dijkstra_dk_map_loop_math_model g src M_done s
        end).
Proof.
  intros cur_vertex cur_distance edge visited_set M.
  dijkstra_dk_edge_body_hoare.
  - subst edge.
    unfold dijkstra_dk_map_edge_loop_math_model in Hpre.
    destruct Hpre as (dist_values & Hstate & Hedge_state & Hexact & Hphase).
    eapply dijkstra_dk_map_edge_loop_math_finish; eauto.
  - destruct Hrelax_assume as
      (Hweight_nonneg & Hoverflow & Hrelax_state).
    unfold dijkstra_dk_map_edge_loop_math_model in Hpre.
    destruct Hpre as (dist_values & Hstate & Hedge_state & Hexact & Hphase).
    pose proof Hphase as Hphase_for_facts.
    pose_dk_edge_current_facts edge cur_vertex Hphase_for_facts
      Hedge_state Hedge_not_nil.
    assert (Hcandidate_bounds :
      0 <= cur_distance + Znth edge weight_values 0 <
        DijkstraGraph.infinity)
      by (eapply dijkstra_dk_map_edge_phase_candidate_bounds; eauto).
    erewrite graph_state_model_dist_cell in Hrelax_state by eauto.
    assert (Hunvisited :
      ~ visited_set (Znth edge to_values 0))
      by (eapply dijkstra_dk_map_edge_phase_relax_neighbor_unvisited;
          eauto).
    assert (Hexact_after :
      map_queue_exact_unvisited_dist
        g visited_set
        (replace_Znth (Znth edge to_values 0)
          (cur_distance + Znth edge weight_values 0) dist_values)
        M_after).
    {
      assert (Hshape_old : vector_shape dist_values)
        by (unfold dijkstra_dk_map_edge_loop_state,
              dijkstra_dk_map_loop_state in Hedge_state; tauto).
      eapply map_queue_exact_update_or_push.
      - exact Hsize.
      - exact Hshape_old.
      - exact Hneighbor_storage.
      - exact Hneighbor_valid.
      - exact Hunvisited.
      - exact Hrelax_state.
      - exact Hcandidate_bounds.
      - exact Hexact.
      - exact Hupdate.
    }
    unfold dijkstra_dk_map_edge_loop_math_model.
    exists (replace_Znth (Znth edge to_values 0)
      (cur_distance + Znth edge weight_values 0) dist_values).
    split.
    + eapply graph_state_model_replace_Znth_set_state_distance; eauto.
    + split.
      * assert (Hitems_after :
          map_queue_items_valid g M_after)
          by (eapply map_queue_exact_items_valid; exact Hexact_after).
        assert (Hnext_nonneg : -1 <= Znth edge next_values 0)
          by (eapply forward_star_next_0_lower_bound; eauto).
        assert (Hcur_dist_keep :
          dist_cell dist_values cur_vertex = cur_distance)
          by (unfold dijkstra_dk_map_edge_loop_state in Hedge_state; tauto).
        unfold dijkstra_dk_map_edge_loop_state in *.
        destruct Hedge_state as
          (Hloop_state & Hcur_valid0 & Hcur_dist & _Hedge_nonneg).
        unfold dijkstra_dk_map_loop_state in *.
        destruct Hloop_state as
          (Hwf & Hsrc_valid & Hnonneg_valid & Hshape & Hsafe & _Hitems).
        split.
        -- unfold dijkstra_dk_map_loop_state.
           split; [exact Hwf |].
           split; [exact Hsrc_valid |].
           split; [exact Hnonneg_valid |].
           split.
           ++ unfold vector_shape in *.
              rewrite Zlength_replace_Znth.
              exact Hshape.
           ++ split.
              ** eapply dist_values_safe_replace_Znth; eauto.
              ** exact Hitems_after.
        -- split; [exact Hcur_valid0 |].
           split.
           ++ assert (Hcur_ne_neighbor :
                cur_vertex <> Znth edge to_values 0).
              {
                intro Hsame.
                rewrite Hsame in Hcur_dist_keep.
                rewrite Hcur_dist_keep in Hrelax_state.
                lia.
              }
              rewrite dist_cell_replace_Znth_diff by eauto.
              exact Hcur_dist_keep.
           ++ exact Hnext_nonneg.
      * split; [exact Hexact_after |].
        eapply (dijkstra_dk_map_edge_phase_relax_update
          g vertex_count edge_count src cur_vertex cur_distance edge
          (Znth edge to_values 0) (Znth edge weight_values 0)
          (cur_distance + Znth edge weight_values 0)
          head_values to_values weight_values next_values
          visited_set dist_values M); eauto.
  - unfold dijkstra_dk_map_edge_loop_math_model in Hpre.
    destruct Hpre as (dist_values & Hstate & Hedge_state & Hexact & Hphase).
    pose proof Hphase as Hphase_for_facts.
    pose_dk_edge_current_facts edge cur_vertex Hphase_for_facts
      Hedge_state Hedge_not_nil.
    assert (Hcandidate_bounds :
      0 <= cur_distance + Znth edge weight_values 0 <
        DijkstraGraph.infinity)
      by (eapply dijkstra_dk_map_edge_phase_candidate_bounds; eauto).
    assert (Hskip_pure :
      Znth edge weight_values 0 < 0 \/
        cur_distance > DijkstraGraph.infinity - Znth edge weight_values 0 \/
        cur_distance + Znth edge weight_values 0 >=
          dist_cell dist_values (Znth edge to_values 0)).
    {
      destruct Hskip as [Hskip | [Hskip | Hskip]].
      - left; exact Hskip.
      - right; left; exact Hskip.
      - right; right.
        erewrite graph_state_model_dist_cell in Hskip by eauto.
        exact Hskip.
    }
    assert (Hskip_cell :
      dist_cell dist_values (Znth edge to_values 0) <=
        cur_distance + Znth edge weight_values 0)
      by (eapply dijkstra_skip_assume_to_dist_cell; eauto).
    unfold dijkstra_dk_map_edge_loop_math_model.
    exists dist_values.
    split; [exact Hstate |].
    split.
    + eapply dijkstra_dk_map_edge_loop_next_state; eauto.
      eapply forward_star_next_0_lower_bound; eauto.
    + split; [exact Hexact |].
      eapply dijkstra_dk_map_edge_phase_skip_update; eauto.
Qed.

Lemma dijkstra_dk_lfs_edge_loop_math :
  forall cur_vertex cur_distance edge visited_set M,
    Hoare
      (dijkstra_dk_map_edge_loop_math_model
        g src cur_vertex cur_distance edge
        head_values to_values weight_values next_values
        visited_set M)
      (dijkstra_dk_lfs_edge_loop
        head_values to_values weight_values next_values
        cur_vertex cur_distance edge M)
      (fun M_done s =>
        dijkstra_dk_map_loop_math_model g src M_done s).
Proof.
  intros cur_vertex cur_distance edge visited_set M.
  unfold dijkstra_dk_lfs_edge_loop.
  change (Hoare
    ((fun acc =>
      dijkstra_dk_map_edge_loop_math_model
        g src cur_vertex cur_distance (fst acc)
        head_values to_values weight_values next_values
        visited_set (snd acc)) (edge, M))
    (repeat_break
      (dijkstra_dk_lfs_edge_body
        head_values to_values weight_values next_values
        cur_vertex cur_distance) (edge, M))
    (fun M_done s =>
      dijkstra_dk_map_loop_math_model g src M_done s)).
  eapply Hoare_repeat_break with
    (P := fun acc =>
      dijkstra_dk_map_edge_loop_math_model
        g src cur_vertex cur_distance (fst acc)
        head_values to_values weight_values next_values
        visited_set (snd acc))
    (Q := fun M_done s =>
      dijkstra_dk_map_loop_math_model g src M_done s).
  intros [edge0 M0].
  cbn [fst snd].
  apply dijkstra_dk_lfs_edge_body_math_step.
Qed.

Lemma dijkstra_dk_map_loop_math_pop_to_edge_model :
  forall visited_before dist_values s_before M M_after
         cur_vertex cur_distance,
    graph_state_model g visited_before dist_values s_before ->
    dijkstra_dk_map_loop_math_bridge_state
      g src visited_before dist_values M ->
    dk_map_queue_pop_result M M_after cur_vertex cur_distance ->
    dijkstra_dk_map_edge_loop_math_model
      g src cur_vertex cur_distance (Znth cur_vertex head_values 0)
      head_values to_values weight_values next_values
      (fun v => visited_before v \/ v = cur_vertex) M_after
      (set_state_visited cur_vertex s_before).
Proof.
  intros visited_before dist_values s_before M M_after
    cur_vertex cur_distance Hstate Hbridge Hpop.
  unfold dijkstra_dk_map_loop_math_bridge_state in Hbridge.
  destruct Hbridge as
    (Hloop_state & Hexact & Hvisited_valid & Hmath).
  pose proof
    (map_queue_exact_pop_item
      g visited_before dist_values M M_after cur_vertex cur_distance
      Hexact Hpop)
    as (Hcur_valid & Hunvisited & Hcur_dist_forward & Hcur_finite).
  assert (Hcur_dist : dist_cell dist_values cur_vertex = cur_distance)
    by (symmetry; exact Hcur_dist_forward).
  assert (Hvisit_add :
    visited_set_add visited_before cur_vertex
      (fun v => visited_before v \/ v = cur_vertex))
    by (unfold visited_set_add; tauto).
  unfold dijkstra_dk_map_edge_loop_math_model.
  exists dist_values.
  split.
  - apply graph_state_model_visit_state
      with (visited_set := visited_before); auto.
  - split.
    + assert (Hloop_after :
        dijkstra_dk_map_loop_state
          g src visited_before dist_values M_after)
        by (eapply dijkstra_dk_map_loop_state_pop; eauto).
      assert (Hitems_after :
        map_queue_items_valid g M_after).
      {
        eapply map_queue_exact_items_valid.
        eapply map_queue_exact_pop_visit; eauto.
      }
      unfold dijkstra_dk_map_edge_loop_state.
      split.
      * unfold dijkstra_dk_map_loop_state in *.
        destruct Hloop_after as
          (Hwf & Hsrc_valid & Hnonneg_valid & Hshape & Hsafe & _).
        split; [exact Hwf |].
        split; [exact Hsrc_valid |].
        split; [exact Hnonneg_valid |].
        split; [exact Hshape |].
        split; [exact Hsafe | exact Hitems_after].
      * split; [exact Hcur_valid |].
        split; [exact Hcur_dist |].
        eapply forward_star_head_0_lower_bound; eauto.
    + split.
      * eapply map_queue_exact_pop_visit; eauto.
      * split; [exact Hcur_finite |].
        right.
        exists visited_before, dist_values.
        split; [exact Hvisited_valid |].
        split; [exact Hno_overflow |].
        split; [exact Hvisit_add |].
        split; [exact Hcur_dist_forward |].
        split.
        -- eapply forward_star_head_0_nil_or_chain; eauto.
        -- assert (Hselected :
             dijkstra_selected_min
               g visited_before dist_values cur_vertex).
           {
             eapply map_queue_pop_selected_min
               with (vertex_count := vertex_count)
                    (M_after := M_after); eauto.
           }
           eapply (dijkstra_edge_math_state_done_equiv
             g src visited_before
             (fun v => visited_before v \/ v = cur_vertex)
             cur_vertex dist_values
             (fun _ : DijkstraGraph.E => False)
             (forward_star_done_edge_set
               head_values to_values weight_values next_values
               cur_vertex (Znth cur_vertex head_values 0))
             dist_values).
           ++ intros e_abs.
              symmetry.
              eapply forward_star_done_edge_set_head_empty_equiv; eauto.
           ++ unfold dijkstra_edge_math_state,
                Dijkstra.relax_step_invariant.
              split; [exact Hvisit_add |].
              split; [exact Hmath |].
              split; [exact Hselected |].
              split.
              ** unfold dijkstra_after_visit_state, set_state_visited,
                   dijkstra_array_state; simpl; sets_unfold.
                 intro v; split.
                 --- intros [Hvalid_after Hvisited_after].
                     destruct Hvisited_after as [Hvisited_before | Heq];
                     [ left; split; [apply Hvisited_valid |];
                       exact Hvisited_before
                     | right; symmetry; exact Heq ].
                 --- intros [[Hvalid_before Hvisited_before] | Heq];
                       subst;
                     [ split; [exact Hvalid_before |];
                       left; exact Hvisited_before
                     | split; [exact Hcur_valid |];
                       right; reflexivity ].
              ** split; [reflexivity |].
                 split.
                 --- intros v e _ Hfalse _. contradiction.
                 --- intros v _ _.
                     unfold dijkstra_after_visit_state, set_state_visited,
                       dijkstra_array_state; simpl.
                     destruct (vertex_valid_dec g v); reflexivity.
Qed.

Lemma dijkstra_dk_lfs_edge_loop_after_pop_math :
  forall M_before M_after cur_vertex cur_distance,
    Hoare
      (fun s =>
        exists visited_before dist_values s_before,
          s = set_state_visited cur_vertex s_before /\
          dk_map_queue_pop_result
            M_before M_after cur_vertex cur_distance /\
          graph_state_model g visited_before dist_values s_before /\
          dijkstra_dk_map_loop_math_bridge_state
            g src visited_before dist_values M_before)
      (dijkstra_dk_lfs_edge_loop
        head_values to_values weight_values next_values
        cur_vertex cur_distance (Znth cur_vertex head_values 0)
        M_after)
      (fun M_done s =>
        dijkstra_dk_map_loop_math_model g src M_done s).
Proof.
  intros M_before M_after cur_vertex cur_distance.
  apply Hoare_pre_ex.
  intros visited_before.
  apply Hoare_pre_ex.
  intros dist_values.
  apply Hoare_pre_ex.
  intros s_before.
  eapply Hoare_conseq_pre.
  2: {
    eapply dijkstra_dk_lfs_edge_loop_math.
  }
  intros s Hpre.
  destruct Hpre as (Hvisit & Hpop & Hstate & Hbridge).
  subst s.
  eapply dijkstra_dk_map_loop_math_pop_to_edge_model; eauto.
Qed.

Lemma dijkstra_dk_lfs_loop_body_math_step :
  forall M,
    Hoare
      (dijkstra_dk_map_loop_math_model g src M)
      (dijkstra_dk_lfs_loop_body
        head_values to_values weight_values next_values M)
      (fun result s =>
        match result with
        | by_continue M_next =>
            dijkstra_dk_map_loop_math_model g src M_next s
        | by_break _ =>
            dijkstra_dk_map_loop_math_model g src partial_map_empty s
        end).
Proof.
  intros M.
  unfold dijkstra_dk_lfs_loop_body.
  apply Hoare_choice.
  - apply Hoare_assume_bind.
    apply Hoare_ret'.
    intros s [Hempty Hpre].
    rewrite (partial_map_is_empty_ext M Hempty) in Hpre.
    exact Hpre.
  - apply Hoare_assume_bind.
    eapply Hoare_bind.
    + apply Hoare_get.
    + intros [[M_after cur_vertex] cur_distance].
      cbn [fst snd].
      eapply Hoare_bind.
      * apply Hoare_update.
      * intros [].
        eapply Hoare_bind
          with (Q := fun M_done s =>
            dijkstra_dk_map_loop_math_model g src M_done s).
        -- eapply Hoare_conseq_pre.
           2: {
             apply (dijkstra_dk_lfs_edge_loop_after_pop_math
               M M_after cur_vertex cur_distance).
           }
           intros s Hpost.
           destruct Hpost as (s_before & Hvisit & Hrest).
           destruct Hrest as (Hpop & (_Hnonempty & Hpre)).
           unfold dijkstra_dk_map_loop_math_model in Hpre.
           destruct Hpre as
             (visited_before & dist_values & Hstate & Hbridge).
           exists visited_before, dist_values, s_before.
           split; [exact Hvisit |].
           split; [exact Hpop |].
           split; [exact Hstate |].
           exact Hbridge.
        -- intros M_done.
           apply Hoare_ret'.
           intros s Hdone.
           exact Hdone.
Qed.

Lemma dijkstra_dk_initial_edge_loop_math_model :
  dijkstra_dk_map_edge_loop_math_model
    g src src 0 (Znth src head_values 0)
    head_values to_values weight_values next_values
    (source_visited_set src) partial_map_empty
    (set_state_visited src (initial_state src)).
Proof.
  pose proof
    (graph_has_size_vertex_valid_bounds g vertex_count src Hsize Hsrc)
    as (Hcount & Hsrc_bounds).
  pose proof
    (graph_has_size_vertex_valid_storage g vertex_count src Hsize Hsrc)
    as Hsrc_storage.
  unfold dijkstra_dk_map_edge_loop_math_model.
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
  - split.
    + unfold dijkstra_dk_map_edge_loop_state.
      split.
      * unfold dijkstra_dk_map_loop_state.
        split; [eapply forward_star_model_graph_wf; eauto |].
        split; [exact Hsrc |].
        split; [exact Hnonneg |].
        split; [apply initial_dist_values_shape; exact Hsrc_storage |].
        split; [apply initial_dist_values_safe; exact Hsrc_storage |].
        unfold map_queue_items_valid.
        intros data_x key_x Hpresent.
        unfold partial_map_present, partial_map_get, partial_map_empty
          in Hpresent.
        discriminate.
      * split; [exact Hsrc |].
        split.
        -- rewrite initial_dist_values_cell by
             (exact Hsrc_storage || exact Hsrc_storage).
           destruct (Z.eq_dec src src); [reflexivity | contradiction].
        -- eapply forward_star_head_0_lower_bound; eauto.
    + split.
      * eapply map_queue_exact_empty_after_source_initial; eauto.
      * split; [unfold DijkstraGraph.infinity; lia |].
        left.
        split.
        -- unfold source_visited_set; tauto.
        -- split; [exact Hno_overflow |].
           split; [reflexivity |].
           split; [reflexivity |].
           split.
           ++ eapply forward_star_head_0_nil_or_chain; eauto.
           ++ eapply dijkstra_first_step_math_state_done_equiv.
              ** intros e_abs.
                 symmetry.
                 eapply forward_star_done_edge_set_head_empty_equiv; eauto.
              ** apply initial_first_step_math_state_empty
                   with (vertex_count := vertex_count); auto.
Qed.

Lemma dijkstra_dk_lfs_initial_loop_body_math_step :
  Hoare
    (eq (initial_state src))
    (dijkstra_dk_lfs_loop_body
      head_values to_values weight_values next_values
      (singleton_source_map src))
    (fun result s =>
      match result with
      | by_continue M_next =>
          dijkstra_dk_map_loop_math_model g src M_next s
      | by_break _ => False
      end).
Proof.
  unfold dijkstra_dk_lfs_loop_body.
  apply Hoare_choice.
  - apply Hoare_assume_bind.
    apply Hoare_ret'.
    intros s [Hempty _Hinitial].
    exfalso.
    unfold singleton_source_map in Hempty.
    exact (partial_map_add_not_empty partial_map_empty src 0 Hempty).
  - apply Hoare_assume_bind.
    eapply Hoare_bind.
    + apply Hoare_get.
    + intros [[M_after cur_vertex] cur_distance].
      cbn [fst snd].
      eapply Hoare_bind.
      * apply Hoare_update.
      * intros [].
        eapply Hoare_bind
          with (Q := fun M_done s =>
            dijkstra_dk_map_loop_math_model g src M_done s).
        -- eapply Hoare_conseq_pre.
           2: {
             eapply dijkstra_dk_lfs_edge_loop_math.
           }
           intros s Hpost.
           destruct Hpost as (s_before & Hvisit & Hrest).
           destruct Hrest as (Hpop & (_Hnonempty & Hinitial)).
           subst s_before.
           pose proof
             (singleton_source_map_pop
               src M_after cur_vertex cur_distance Hpop)
             as (Hmap_empty & Hcur_vertex & Hcur_distance).
           rewrite Hmap_empty.
           subst cur_vertex cur_distance.
           subst s.
           exact dijkstra_dk_initial_edge_loop_math_model.
        -- intros M_done.
           apply Hoare_ret'.
           intros s Hdone.
           exact Hdone.
Qed.

End DijkstraDecreaseKeyProgramProofs.

Lemma dijkstra_dk_lfs_program_correct :
  forall g vertex_count edge_count src
         head_values to_values weight_values next_values dist_values,
    graph_has_size g vertex_count ->
    vertex_valid g src ->
    nonnegative_edges g ->
    forward_star_model g edge_count
      head_values to_values weight_values next_values ->
    shortest_path_relaxation_bounded g src DijkstraGraph.infinity ->
    safeExec (graph_dist_model g dist_values)
      (return tt)
      (result_state (eq (initial_state src))
        (dijkstra_dk_lfs_program
          src head_values to_values weight_values next_values)) ->
    dijkstra_shortest_dist g src dist_values.
Proof.
  intros g vertex_count edge_count src
    head_values to_values weight_values next_values dist_values
    Hsize Hsrc Hnonneg Hmodel Hno_overflow Hsafe.
  apply safeExec_ret in Hsafe as (s & Hdist_state & Hresult).
  unfold result_state in Hresult; sets_unfold in Hresult.
  destruct Hresult as (s_initial & Hinitial & Hrun_lfs).
  subst s_initial.
  assert (Hhoare :
    Hoare
      (eq (initial_state src))
      (dijkstra_dk_lfs_program
        src head_values to_values weight_values next_values)
      (fun _ s =>
        dijkstra_dk_map_loop_math_model g src partial_map_empty s)).
  {
    unfold dijkstra_dk_lfs_program, dijkstra_dk_lfs_loop.
    eapply Hoare_proequiv.
    - symmetry.
      apply (repeat_break_unfold
        (dijkstra_dk_lfs_loop_body
          head_values to_values weight_values next_values)).
    - eapply Hoare_bind
        with (Q := fun result s =>
          match result with
          | by_continue M_next =>
              dijkstra_dk_map_loop_math_model g src M_next s
          | by_break _ => False
          end).
      + eapply dijkstra_dk_lfs_initial_loop_body_math_step; eauto.
      + intros [M_next | []].
        * unfold dijkstra_dk_lfs_loop.
          eapply Hoare_repeat_break
            with (P := dijkstra_dk_map_loop_math_model g src)
                 (Q := fun _ s =>
                   dijkstra_dk_map_loop_math_model
                     g src partial_map_empty s).
          intros M0.
          eapply dijkstra_dk_lfs_loop_body_math_step; eauto.
        * unfold Hoare; contradiction.
  }
  eapply dijkstra_dk_map_loop_math_model_empty_to_shortest
    with (M := partial_map_empty) (s := s); eauto.
  - apply partial_map_empty_is_empty.
  - exact (Hhoare (initial_state src) tt s eq_refl Hrun_lfs).
Qed.

End DijkstraDecreaseKey.
