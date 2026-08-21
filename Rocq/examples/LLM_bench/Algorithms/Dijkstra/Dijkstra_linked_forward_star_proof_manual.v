  Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.Dijkstra Require Import Dijkstra_linked_forward_star_goal.
From SimpleC.EE.LLM_bench.Algorithms.Dijkstra Require Import Dijkstra_linked_forward_star_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.StateRelMonad Require Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Require Import Algorithms.Dijkstra.Dijkstra.
Require Import SimpleC.EE.LLM_bench.Algorithms.Dijkstra.Dijkstra_linked_forward_star_lib.
Import DijkstraGraph.
Import DijkstraLinkedForwardStar.
Local Open Scope sac.

Lemma proof_of_dijkstra_linked_forward_star_init_entail_wit_1_split_goal_1 : dijkstra_linked_forward_star_init_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply dist_init_loop_start; auto.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_init_entail_wit_1 : dijkstra_linked_forward_star_init_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_dijkstra_linked_forward_star_init_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_init_entail_wit_2_split_goal_1 : dijkstra_linked_forward_star_init_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply dist_init_loop_step; auto.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_init_entail_wit_2 : dijkstra_linked_forward_star_init_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_dijkstra_linked_forward_star_init_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_init_entail_wit_3_split_goal_1 : dijkstra_linked_forward_star_init_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace i with 10 in * by lia; auto.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_init_entail_wit_3 : dijkstra_linked_forward_star_init_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_dijkstra_linked_forward_star_init_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_init_return_wit_1_split_goal_1 : dijkstra_linked_forward_star_init_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply dist_init_loop_to_dijkstra_init_dist; auto.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_init_return_wit_1 : dijkstra_linked_forward_star_init_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_dijkstra_linked_forward_star_init_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_entail_wit_2 : dijkstra_linked_forward_star_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists ((0, source_pre) :: nil) vertices1 distances1
    (fun _ : Z => False) dist_init_2.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
    cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
    cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
    cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
    cancel (IntArray.full dist_pre 10 dist_init_2).
    cancel (IntArray.full &( "priority_queue_vertex") 200005 vertices1).
    cancel (IntArray.full &( "priority_queue_distance") 200005 distances1).
    cancel (&( "priority_queue_size") # Int |-> 0).
  - split_pures; dump_pre_spatial; auto.
    + unfold visited_set_empty; tauto.
    + unfold priority_queue_push_result; reflexivity.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_entail_wit_3 : dijkstra_linked_forward_star_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (priority_queue_model_size_bounds
      vertices1 distances1 (0 + 1) queue_items_initial_after PreH1)
    as (_ & Hqueue_len).
  Exists distances1 vertices1 visited_init dist_init queue_items_initial_after.
  replace (Zlength queue_items_initial_after) with (0 + 1) by lia.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec). 
    cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
    cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
    cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
    cancel (IntArray.full dist_pre 10 dist_init).
    cancel (IntArray.full &( "priority_queue_vertex") 200005 vertices1).
    cancel (IntArray.full &( "priority_queue_distance") 200005 distances1).
    cancel (&( "priority_queue_size") # Int |-> (0 + 1)).
  - split_pures; dump_pre_spatial; auto.
    + eapply dijkstra_init_dist_loop_state; 
      eauto using priority_queue_push_result_nil_vertices_valid.
    + eapply dijkstra_lfs_initial_to_loop_refines; eauto.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_entail_wit_4 : dijkstra_linked_forward_star_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct (priority_queue_pop_result_exists
    queue_vertices_2 queue_distances_2 queue_items_2
    PreH2 PreH4)
    as (queue_items_after & pop_vertex & pop_distance & Hpop).
  Exists queue_vertices_2 queue_distances_2 queue_items_after
    pop_vertex pop_distance visited_cur_2 dist_cur_2 queue_items_2.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre
      head_values_low_level_spec);
    cancel (IntArray.full to_pre edge_count_pre
      to_values_low_level_spec);
    cancel (IntArray.full weight_pre edge_count_pre
      weight_values_low_level_spec);
    cancel (IntArray.full next_pre edge_count_pre
      next_values_low_level_spec);
    cancel (IntArray.full dist_pre 10 dist_cur_2);
    cancel (IntArray.full &( "priority_queue_vertex") 200005
      queue_vertices_2);
    cancel (IntArray.full &( "priority_queue_distance") 200005
      queue_distances_2);
    cancel (&( "priority_queue_size") # Int |->
      Zlength queue_items_2).
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_entail_wit_5 : dijkstra_linked_forward_star_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (priority_queue_model_size_bounds
      vertices1 distances1 (Zlength queue_items_2 - 1)
      queue_items_after PreH1) as (_ & Hqueue_after_len).
  assert (Hqueue_after_model :
    priority_queue_model vertices1 distances1
      (Zlength queue_items_after) queue_items_after).
  {
    rewrite Hqueue_after_len.
    exact PreH1.
  }
  pose proof
    (priority_queue_pop_result_bounds
      queue_vertices_2 queue_distances_2 queue_items_2
      queue_items_after pop_vertex pop_distance PreH9 PreH8)
    as (Hpop_storage & _ & Hpop_distance_bounds).
  pose proof
    (priority_queue_pop_result_vertex_valid
      g_low_level_spec source_pre visited_cur_2 dist_cur_2 queue_items_2
      queue_items_after pop_vertex pop_distance PreH6 PreH8)
    as Hpop_vertex_valid.
  assert (Hpop_vertex_bounds : 0 <= pop_vertex < vertex_count_pre).
  {
    unfold vertex_valid, DijkstraGraph.vertex_valid in Hpop_vertex_valid.
    pose proof PreH2 as Hsize.
    unfold graph_has_size in Hsize.
    lia.
  }
  assert (Hloop_after :
    dijkstra_loop_state g_low_level_spec source_pre
      visited_cur_2 dist_cur_2 queue_items_after).
  {
    apply (dijkstra_loop_state_pop
      g_low_level_spec source_pre visited_cur_2 dist_cur_2 queue_items_2
      queue_items_after pop_vertex pop_distance
      vertices1 distances1); auto.
  }
  Exists distances1 vertices1 visited_cur_2 dist_cur_2 queue_items_after.
  replace (Zlength queue_items_after) with (Zlength queue_items_2 - 1) by lia.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre
      head_values_low_level_spec);
    cancel (IntArray.full to_pre edge_count_pre
      to_values_low_level_spec);
    cancel (IntArray.full weight_pre edge_count_pre
      weight_values_low_level_spec);
    cancel (IntArray.full next_pre edge_count_pre
      next_values_low_level_spec);
    cancel (IntArray.full dist_pre 10 dist_cur_2);
    cancel (IntArray.full &( "priority_queue_vertex") 200005 vertices1);
    cancel (IntArray.full &( "priority_queue_distance") 200005 distances1);
    cancel (&( "priority_queue_size") # Int |->
      (Zlength queue_items_2 - 1)).
  - split_pures; dump_pre_spatial; auto.
    + lia.
    + lia.
    + unfold storage_index, DijkstraGraph.max_vertices in *; lia.
    + unfold DijkstraGraph.infinity in *; lia.
    + unfold DijkstraGraph.infinity in *; lia.
    + eapply dijkstra_loop_refines_pop; eauto.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_entail_wit_6 : dijkstra_linked_forward_star_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (forward_star_model_head_case_0
      g_low_level_spec vertex_count_pre edge_count_pre
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      cur_vertex PreH2 PreH5 ltac:(lia)) as Hhead.
  assert (Hcur_valid : vertex_valid g_low_level_spec cur_vertex).
  {
    unfold vertex_valid, DijkstraGraph.vertex_valid.
    pose proof PreH2 as Hsize.
    unfold graph_has_size in Hsize.
    lia.
  }
  assert (Hdist : dist_cell dist_cur cur_vertex = cur_distance).
  {
    rewrite PreH1.
    apply dist_cell_Znth_0; auto.
    unfold dijkstra_loop_state in PreH6.
    tauto.
  }
  assert (Hedge_nonneg :
    -1 <= Znth cur_vertex head_values_low_level_spec 0).
  {
    destruct Hhead as [Hhead_nil | Hhead_edge].
    - rewrite Hhead_nil. lia.
      - unfold edge_index in Hhead_edge. lia.
  }
  pose (visited_edge_cur := fun v : Z => visited_cur_2 v \/ v = cur_vertex).
  assert (Hvisit_add :
    visited_set_add visited_cur_2 cur_vertex visited_edge_cur).
  {
    unfold visited_set_add, visited_edge_cur.
    tauto.
  }
  assert (Hedge_state :
    dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge_cur cur_vertex
      cur_distance (Znth cur_vertex head_values_low_level_spec 0)
      dist_cur queue_items_2).
  {
    unfold dijkstra_edge_loop_state.
    split; [exact PreH6 |].
    split; [exact Hcur_valid |].
    split; [exact Hdist |].
    exact Hedge_nonneg.
  }
  destruct Hhead as [Hhead_nil | Hhead_edge].
  - Left.
    Exists queue_distances_2 queue_vertices_2 dist_cur queue_items_2
      visited_cur_2 visited_edge_cur.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre
        head_values_low_level_spec);
      cancel (IntArray.full to_pre edge_count_pre
        to_values_low_level_spec);
      cancel (IntArray.full weight_pre edge_count_pre
        weight_values_low_level_spec);
      cancel (IntArray.full next_pre edge_count_pre
        next_values_low_level_spec);
      cancel (IntArray.full dist_pre 10 dist_cur);
      cancel (IntArray.full &( "priority_queue_vertex") 200005
        queue_vertices_2);
      cancel (IntArray.full &( "priority_queue_distance") 200005
        queue_distances_2);
      cancel (&( "priority_queue_size") # Int |->
        Zlength queue_items_2).
    + split_pures; dump_pre_spatial; auto.
      eapply dijkstra_after_pop_refines_equal_to_edge_loop; eauto.
  - Right.
    Exists queue_distances_2 queue_vertices_2 dist_cur queue_items_2
      visited_cur_2 visited_edge_cur.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre
        head_values_low_level_spec);
      cancel (IntArray.full to_pre edge_count_pre
        to_values_low_level_spec);
      cancel (IntArray.full weight_pre edge_count_pre
        weight_values_low_level_spec);
      cancel (IntArray.full next_pre edge_count_pre
        next_values_low_level_spec);
      cancel (IntArray.full dist_pre 10 dist_cur);
      cancel (IntArray.full &( "priority_queue_vertex") 200005
        queue_vertices_2);
      cancel (IntArray.full &( "priority_queue_distance") 200005
        queue_distances_2);
      cancel (&( "priority_queue_size") # Int |->
        Zlength queue_items_2).
    + split_pures; dump_pre_spatial; auto.
      * unfold edge_index in Hhead_edge; lia.
      * unfold edge_index in Hhead_edge; lia.
      * eapply dijkstra_after_pop_refines_equal_to_edge_loop; eauto.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_entail_wit_7 : dijkstra_linked_forward_star_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (forward_star_model_edge_bounds
      g_low_level_spec edge_count_pre head_values_low_level_spec
      to_values_low_level_spec weight_values_low_level_spec
      next_values_low_level_spec edge PreH5 ltac:(unfold edge_index; lia))
    as (Hto_graph & Hto_storage & Hweight_bounds & _).
  assert (Hto_vertex_count :
    0 <= Znth edge to_values_low_level_spec 0 < vertex_count_pre).
  {
    pose proof PreH2 as Hsize.
    unfold graph_has_size in Hsize.
    lia.
  }
  Exists queue_distances_2 queue_vertices_2 dist_edge_2 queue_items_2
    visited_cur_2 visited_edge_2.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre
      head_values_low_level_spec);
    cancel (IntArray.full to_pre edge_count_pre
      to_values_low_level_spec);
    cancel (IntArray.full weight_pre edge_count_pre
      weight_values_low_level_spec);
    cancel (IntArray.full next_pre edge_count_pre
      next_values_low_level_spec);
    cancel (IntArray.full dist_pre 10 dist_edge_2);
    cancel (IntArray.full &( "priority_queue_vertex") 200005
      queue_vertices_2);
    cancel (IntArray.full &( "priority_queue_distance") 200005
      queue_distances_2);
    cancel (&( "priority_queue_size") # Int |->
      Zlength queue_items_2).
  - split_pures; dump_pre_spatial; auto.
    + lia.
    + lia.
    + unfold storage_index, DijkstraGraph.max_vertices in Hto_storage; lia.
    + unfold DijkstraGraph.infinity in Hweight_bounds; lia.
    + unfold DijkstraGraph.infinity in Hweight_bounds; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_entail_wit_8 : dijkstra_linked_forward_star_entail_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hneighbor_valid : vertex_valid g_low_level_spec neighbor).
  {
    unfold vertex_valid, DijkstraGraph.vertex_valid.
    unfold graph_has_size in PreH4.
    lia.
  }
  assert (Hneighbor_storage : storage_index neighbor).
  {
    unfold storage_index, DijkstraGraph.max_vertices.
    lia.
  }
  assert (Hdist_cell_neighbor :
    dist_cell dist_edge neighbor = Znth neighbor dist_edge 0).
  {
    apply (dist_cell_Znth_0 dist_edge neighbor).
    - match goal with
      | H : dijkstra_edge_loop_state _ _ _ _ _ _ dist_edge queue_items |- _ =>
          pose proof H as Hstate_copy;
          unfold dijkstra_edge_loop_state in Hstate_copy;
          destruct Hstate_copy as [Hloop _]
      end.
      unfold dijkstra_loop_state in Hloop.
      tauto.
    - exact Hneighbor_storage.
  }
  assert (Hrelax_cell :
    cur_distance + edge_weight0 < dist_cell dist_edge neighbor).
  {
    rewrite Hdist_cell_neighbor.
    exact PreH1.
  }
  assert (Hcandidate_bounds :
    0 <= cur_distance + edge_weight0 < DijkstraGraph.infinity).
  {
    split; [lia |].
    match goal with
    | H : dijkstra_edge_loop_state _ _ _ _ _ _ dist_edge queue_items |- _ =>
        pose proof H as Hstate_copy;
        unfold dijkstra_edge_loop_state in Hstate_copy;
        destruct Hstate_copy as [Hloop _]
    end.
    unfold dijkstra_loop_state in Hloop.
    destruct Hloop as (_ & _ & _ & _ & Hsafe & _).
    specialize (Hsafe neighbor Hneighbor_storage).
    rewrite Hdist_cell_neighbor in Hsafe.
    lia.
  }
  assert (Hedge_after :
    dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex
      cur_distance edge
      (replace_Znth neighbor (cur_distance + edge_weight0) dist_edge)
      queue_items).
  {
    eapply dijkstra_edge_loop_state_relax_update; eauto.
  }
  assert (Hafter_relax :
    dijkstra_after_relax_refines g_low_level_spec source_pre
      cur_vertex cur_distance edge neighbor (cur_distance + edge_weight0)
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_edge_2
      (replace_Znth neighbor (cur_distance + edge_weight0) dist_edge)
      queue_items X_low_level_spec).
  {
    eapply dijkstra_edge_loop_refines_relax_to_after_relax.
    - exact PreH4.
    - lia.
    - exact PreH14.
    - exact PreH15.
    - reflexivity.
    - exact Hneighbor_valid.
    - exact Hneighbor_storage.
    - exact Hcandidate_bounds.
    - exact PreH19.
    - exact PreH2.
    - exact Hrelax_cell.
    - exact PreH23.
  }
  destruct (priority_queue_push_result_exists
    queue_items neighbor (cur_distance + edge_weight0))
    as [push_items_after Hpush].
  Exists queue_vertices_2 queue_distances_2 push_items_after
    (replace_Znth neighbor (cur_distance + edge_weight0) dist_edge)
    queue_items visited_cur_2 visited_edge_2.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre
      head_values_low_level_spec);
    cancel (IntArray.full to_pre edge_count_pre
      to_values_low_level_spec);
    cancel (IntArray.full weight_pre edge_count_pre
      weight_values_low_level_spec);
    cancel (IntArray.full next_pre edge_count_pre
      next_values_low_level_spec);
    cancel (IntArray.full dist_pre 10
      (replace_Znth neighbor (cur_distance + edge_weight0) dist_edge));
    cancel (IntArray.full &( "priority_queue_vertex") 200005
      queue_vertices_2);
    cancel (IntArray.full &( "priority_queue_distance") 200005
      queue_distances_2);
    cancel (&( "priority_queue_size") # Int |-> Zlength queue_items).
  - split_pures; dump_pre_spatial; auto.
    + unfold DijkstraGraph.infinity in Hcandidate_bounds; lia.
    + unfold DijkstraGraph.infinity in Hcandidate_bounds; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_entail_wit_9_1 : dijkstra_linked_forward_star_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (priority_queue_model_size_bounds
      vertices1 distances1 (Zlength queue_items_before + 1)
      push_items_after PreH1) as (_ & Hpush_len).
  assert (Hpush_model :
    priority_queue_model vertices1 distances1
      (Zlength push_items_after) push_items_after).
  {
    rewrite Hpush_len.
    exact PreH1.
  }
  assert (Hneighbor_valid : vertex_valid g_low_level_spec neighbor).
  {
    unfold vertex_valid, DijkstraGraph.vertex_valid.
    pose proof PreH2 as Hsize.
    unfold graph_has_size in Hsize.
    lia.
  }
  pose proof
    (dijkstra_edge_loop_to_loop_state
      g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge
      dist_after queue_items_before PreH23) as Hloop_before.
  assert (Hloop_push :
    dijkstra_loop_state g_low_level_spec source_pre
      visited_edge_2 dist_after push_items_after).
  {
    apply (dijkstra_loop_state_push
      g_low_level_spec source_pre visited_edge_2 dist_after queue_items_before
      push_items_after neighbor candidate vertices1 distances1);
      auto.
  }
  unfold dijkstra_edge_loop_state in PreH23.
  destruct PreH23 as (_ & Hcur_valid & Hdist & Hedge_nonneg_old).
  assert (Hedge_push :
    dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex
      cur_distance edge dist_after push_items_after).
  {
    unfold dijkstra_edge_loop_state.
    split; [exact Hloop_push |].
    split; [exact Hcur_valid |].
    split; [exact Hdist |].
    exact Hedge_nonneg_old.
  }
  pose proof
    (forward_star_model_next_case_0
      g_low_level_spec edge_count_pre head_values_low_level_spec
      to_values_low_level_spec weight_values_low_level_spec
      next_values_low_level_spec edge PreH5
      ltac:(unfold edge_index; lia)) as Hnext.
  assert (Hnext_nonneg : -1 <= Znth edge next_values_low_level_spec 0).
  {
    destruct Hnext as [Hnext_nil | Hnext_edge].
    - rewrite Hnext_nil. lia.
    - unfold edge_index in Hnext_edge. lia.
  }
  assert (Hedge_next :
    dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex
      cur_distance (Znth edge next_values_low_level_spec 0)
      dist_after push_items_after).
  {
    apply (dijkstra_edge_loop_next
      g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge);
      auto.
  }
  destruct Hnext as [Hnext_nil | Hnext_edge].
  - Left.
    Exists distances1 vertices1 dist_after push_items_after
      visited_cur_2 visited_edge_2.
    replace (Zlength push_items_after) with
      (Zlength queue_items_before + 1) by lia.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre
        head_values_low_level_spec);
      cancel (IntArray.full to_pre edge_count_pre
        to_values_low_level_spec);
      cancel (IntArray.full weight_pre edge_count_pre
        weight_values_low_level_spec);
      cancel (IntArray.full next_pre edge_count_pre
        next_values_low_level_spec);
      cancel (IntArray.full dist_pre 10 dist_after);
      cancel (IntArray.full &( "priority_queue_vertex") 200005
        vertices1);
      cancel (IntArray.full &( "priority_queue_distance") 200005
        distances1);
      cancel (&( "priority_queue_size") # Int |->
        (Zlength queue_items_before + 1)).
    + split_pures; dump_pre_spatial; auto.
      eapply dijkstra_after_relax_refines_push_to_edge_loop; eauto.
  - Right.
    Exists distances1 vertices1 dist_after push_items_after
      visited_cur_2 visited_edge_2.
    replace (Zlength push_items_after) with
      (Zlength queue_items_before + 1) by lia.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre
        head_values_low_level_spec);
      cancel (IntArray.full to_pre edge_count_pre
        to_values_low_level_spec);
      cancel (IntArray.full weight_pre edge_count_pre
        weight_values_low_level_spec);
      cancel (IntArray.full next_pre edge_count_pre
        next_values_low_level_spec);
      cancel (IntArray.full dist_pre 10 dist_after);
      cancel (IntArray.full &( "priority_queue_vertex") 200005
        vertices1);
      cancel (IntArray.full &( "priority_queue_distance") 200005
        distances1);
      cancel (&( "priority_queue_size") # Int |->
        (Zlength queue_items_before + 1)).
    + split_pures; dump_pre_spatial; auto.
      * unfold edge_index in Hnext_edge; lia.
      * unfold edge_index in Hnext_edge; lia.
      * eapply dijkstra_after_relax_refines_push_to_edge_loop; eauto.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_entail_wit_9_2 : dijkstra_linked_forward_star_entail_wit_9_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (forward_star_model_next_case_0
      g_low_level_spec edge_count_pre head_values_low_level_spec
      to_values_low_level_spec weight_values_low_level_spec
      next_values_low_level_spec edge PreH7
      ltac:(unfold edge_index; lia)) as Hnext.
  assert (Hnext_nonneg : -1 <= Znth edge next_values_low_level_spec 0).
  {
    destruct Hnext as [Hnext_nil | Hnext_edge].
    - rewrite Hnext_nil. lia.
    - unfold edge_index in Hnext_edge. lia.
  }
  assert (Hedge_next :
    dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex
      cur_distance (Znth edge next_values_low_level_spec 0)
      dist_edge_2 queue_items_2).
  {
    apply (dijkstra_edge_loop_next
      g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge);
      auto.
  }
  assert (Hneighbor_valid : vertex_valid g_low_level_spec neighbor).
  {
    unfold vertex_valid, DijkstraGraph.vertex_valid.
    unfold graph_has_size in PreH4.
    destruct PreH4 as [Hcount _].
    rewrite Hcount.
    lia.
  }
  assert (Hdist_cell_neighbor :
    dist_cell dist_edge_2 neighbor = Znth neighbor dist_edge_2 0).
  {
    apply (dist_cell_Znth_0 dist_edge_2 neighbor).
    - unfold dijkstra_edge_loop_state in PreH22.
      destruct PreH22 as [Hloop _].
      unfold dijkstra_loop_state in Hloop.
      tauto.
    - unfold storage_index, DijkstraGraph.max_vertices; lia.
  }
  assert (Hrefines_next :
    dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex
      cur_distance (Znth edge next_values_low_level_spec 0)
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_edge_2 dist_edge_2 queue_items_2 X_low_level_spec).
  {
    eapply dijkstra_edge_loop_refines_no_relax_to_next.
    - lia.
    - exact PreH14.
    - exact PreH15.
    - exact Hneighbor_valid.
    - right; right.
      rewrite Hdist_cell_neighbor.
      exact PreH1.
    - exact PreH23.
  }
  destruct Hnext as [Hnext_nil | Hnext_edge].
  - Left.
    Exists queue_distances_2 queue_vertices_2 dist_edge_2 queue_items_2
      visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre
        head_values_low_level_spec);
      cancel (IntArray.full to_pre edge_count_pre
        to_values_low_level_spec);
      cancel (IntArray.full weight_pre edge_count_pre
        weight_values_low_level_spec);
      cancel (IntArray.full next_pre edge_count_pre
        next_values_low_level_spec);
      cancel (IntArray.full dist_pre 10 dist_edge_2);
      cancel (IntArray.full &( "priority_queue_vertex") 200005
        queue_vertices_2);
      cancel (IntArray.full &( "priority_queue_distance") 200005
        queue_distances_2);
      cancel (&( "priority_queue_size") # Int |->
        Zlength queue_items_2).
    + split_pures; dump_pre_spatial; auto.
  - Right.
    Exists queue_distances_2 queue_vertices_2 dist_edge_2 queue_items_2
      visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre
        head_values_low_level_spec);
      cancel (IntArray.full to_pre edge_count_pre
        to_values_low_level_spec);
      cancel (IntArray.full weight_pre edge_count_pre
        weight_values_low_level_spec);
      cancel (IntArray.full next_pre edge_count_pre
        next_values_low_level_spec);
      cancel (IntArray.full dist_pre 10 dist_edge_2);
      cancel (IntArray.full &( "priority_queue_vertex") 200005
        queue_vertices_2);
      cancel (IntArray.full &( "priority_queue_distance") 200005
        queue_distances_2);
      cancel (&( "priority_queue_size") # Int |->
        Zlength queue_items_2).
    + split_pures; dump_pre_spatial; auto.
      * unfold edge_index in Hnext_edge; lia.
      * unfold edge_index in Hnext_edge; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_entail_wit_9_3 : dijkstra_linked_forward_star_entail_wit_9_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (forward_star_model_next_case_0
      g_low_level_spec edge_count_pre head_values_low_level_spec
      to_values_low_level_spec weight_values_low_level_spec
      next_values_low_level_spec edge PreH6
      ltac:(unfold edge_index; lia)) as Hnext.
  assert (Hnext_nonneg : -1 <= Znth edge next_values_low_level_spec 0).
  {
    destruct Hnext as [Hnext_nil | Hnext_edge].
    - rewrite Hnext_nil. lia.
    - unfold edge_index in Hnext_edge. lia.
  }
  assert (Hedge_next :
    dijkstra_edge_loop_state g_low_level_spec source_pre visited_edge_2 cur_vertex
      cur_distance (Znth edge next_values_low_level_spec 0)
      dist_edge_2 queue_items_2).
  {
    apply (dijkstra_edge_loop_next
      g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge);
      auto.
  }
  assert (Hneighbor_valid : vertex_valid g_low_level_spec neighbor).
  {
    unfold vertex_valid, DijkstraGraph.vertex_valid.
    unfold graph_has_size in PreH3.
    destruct PreH3 as [Hcount _].
    rewrite Hcount.
    lia.
  }
  assert (Hrefines_next :
    dijkstra_edge_loop_refines g_low_level_spec source_pre cur_vertex
      cur_distance (Znth edge next_values_low_level_spec 0)
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_edge_2 dist_edge_2 queue_items_2 X_low_level_spec).
  {
    eapply dijkstra_edge_loop_refines_no_relax_to_next.
    - lia.
    - exact PreH13.
    - exact PreH14.
    - exact Hneighbor_valid.
    - right; left; exact PreH1.
    - exact PreH22.
  }
  destruct Hnext as [Hnext_nil | Hnext_edge].
  - Left.
    Exists queue_distances_2 queue_vertices_2 dist_edge_2 queue_items_2
      visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre
        head_values_low_level_spec);
      cancel (IntArray.full to_pre edge_count_pre
        to_values_low_level_spec);
      cancel (IntArray.full weight_pre edge_count_pre
        weight_values_low_level_spec);
      cancel (IntArray.full next_pre edge_count_pre
        next_values_low_level_spec);
      cancel (IntArray.full dist_pre 10 dist_edge_2);
      cancel (IntArray.full &( "priority_queue_vertex") 200005
        queue_vertices_2);
      cancel (IntArray.full &( "priority_queue_distance") 200005
        queue_distances_2);
      cancel (&( "priority_queue_size") # Int |->
        Zlength queue_items_2).
    + split_pures; dump_pre_spatial; auto.
  - Right.
    Exists queue_distances_2 queue_vertices_2 dist_edge_2 queue_items_2
      visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre
        head_values_low_level_spec);
      cancel (IntArray.full to_pre edge_count_pre
        to_values_low_level_spec);
      cancel (IntArray.full weight_pre edge_count_pre
        weight_values_low_level_spec);
      cancel (IntArray.full next_pre edge_count_pre
        next_values_low_level_spec);
      cancel (IntArray.full dist_pre 10 dist_edge_2);
      cancel (IntArray.full &( "priority_queue_vertex") 200005
        queue_vertices_2);
      cancel (IntArray.full &( "priority_queue_distance") 200005
        queue_distances_2);
      cancel (&( "priority_queue_size") # Int |->
        Zlength queue_items_2).
    + split_pures; dump_pre_spatial; auto.
      * unfold edge_index in Hnext_edge; lia.
      * unfold edge_index in Hnext_edge; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_entail_wit_10_1 : dijkstra_linked_forward_star_entail_wit_10_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hloop_state :
    dijkstra_loop_state g_low_level_spec source_pre
      visited_edge dist_edge queue_items_2).
  {
    apply (dijkstra_edge_loop_to_loop_state
      g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge); auto.
  }
  assert (Hrefines_loop :
    dijkstra_loop_refines g_low_level_spec source_pre
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_edge dist_edge queue_items_2 X_low_level_spec).
  {
    eapply dijkstra_edge_loop_refines_break_to_loop; eauto.
  }
  Exists queue_distances_2 queue_vertices_2 visited_edge dist_edge queue_items_2.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre
      head_values_low_level_spec);
    cancel (IntArray.full to_pre edge_count_pre
      to_values_low_level_spec);
    cancel (IntArray.full weight_pre edge_count_pre
      weight_values_low_level_spec);
    cancel (IntArray.full next_pre edge_count_pre
      next_values_low_level_spec);
    cancel (IntArray.full dist_pre 10 dist_edge);
    cancel (IntArray.full &( "priority_queue_vertex") 200005
      queue_vertices_2);
    cancel (IntArray.full &( "priority_queue_distance") 200005
      queue_distances_2);
    cancel (&( "priority_queue_size") # Int |->
      Zlength queue_items_2).
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_entail_wit_10_2 : dijkstra_linked_forward_star_entail_wit_10_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hcur_valid : vertex_valid g_low_level_spec cur_vertex).
  {
    unfold vertex_valid, DijkstraGraph.vertex_valid.
    unfold graph_has_size in PreH2.
    lia.
  }
  assert (Hdist_cell_cur :
    dist_cell dist_cur_2 cur_vertex = Znth cur_vertex dist_cur_2 0).
  {
    apply (dist_cell_Znth_0 dist_cur_2 cur_vertex).
    - unfold dijkstra_loop_state in PreH6.
      tauto.
    - exact PreH7.
  }
  assert (Hdist_neq :
    cur_distance <> dist_cell dist_cur_2 cur_vertex).
  {
    rewrite Hdist_cell_cur.
    exact PreH1.
  }
  assert (Hrefines_loop :
    dijkstra_loop_refines g_low_level_spec source_pre
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_cur_2 dist_cur_2 queue_items_2 X_low_level_spec).
  {
    eapply dijkstra_after_pop_refines_not_equal_to_loop; eauto.
  }
  Exists queue_distances_2 queue_vertices_2 visited_cur_2 dist_cur_2 queue_items_2.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre
      head_values_low_level_spec);
    cancel (IntArray.full to_pre edge_count_pre
      to_values_low_level_spec);
    cancel (IntArray.full weight_pre edge_count_pre
      weight_values_low_level_spec);
    cancel (IntArray.full next_pre edge_count_pre
      next_values_low_level_spec);
    cancel (IntArray.full dist_pre 10 dist_cur_2);
    cancel (IntArray.full &( "priority_queue_vertex") 200005
      queue_vertices_2);
    cancel (IntArray.full &( "priority_queue_distance") 200005
      queue_distances_2);
    cancel (&( "priority_queue_size") # Int |->
      Zlength queue_items_2).
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_return_wit_1 : dijkstra_linked_forward_star_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hqueue_empty : queue_items = nil).
  {
    destruct queue_items as [| queue_item queue_items_tail].
    - reflexivity.
    - rewrite Zlength_cons in PreH4.
      pose proof (Zlength_nonneg queue_items_tail).
      lia.
  }
  assert (Hsafe_return :
    safeExec (graph_state_model g_low_level_spec visited_cur dist_cur)
      (return tt) X_low_level_spec).
  {
    eapply dijkstra_loop_refines_empty_to_return; eauto.
  }
  Exists queue_vertices queue_distances (Zlength queue_items) queue_items
    visited_cur dist_cur.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre
      head_values_low_level_spec);
    cancel (IntArray.full to_pre edge_count_pre
      to_values_low_level_spec);
    cancel (IntArray.full weight_pre edge_count_pre
      weight_values_low_level_spec);
    cancel (IntArray.full next_pre edge_count_pre
      next_values_low_level_spec);
    cancel (IntArray.full dist_pre 10 dist_cur);
    cancel (IntArray.full &( "priority_queue_vertex") 200005
      queue_vertices);
    cancel (IntArray.full &( "priority_queue_distance") 200005
      queue_distances);
    cancel (&( "priority_queue_size") # Int |->
      Zlength queue_items).
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_1_pure_split_goal_1 : dijkstra_linked_forward_star_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (graph_has_size_vertex_valid_bounds
      g_low_level_spec vertex_count_pre source_pre PreH9 PreH10)
    as ((Hvertex_count_pos & _) & _).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_1_pure_split_goal_2 : dijkstra_linked_forward_star_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (graph_has_size_bounds g_low_level_spec vertex_count_pre PreH9)
    as Hvertex_count_bounds.
  dump_pre_spatial.
  unfold DijkstraGraph.max_vertices in *; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_1_pure_split_goal_3 : dijkstra_linked_forward_star_partial_solve_wit_1_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (graph_has_size_vertex_valid_bounds
      g_low_level_spec vertex_count_pre source_pre PreH9 PreH10)
    as (_ & Hsource_bounds).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_1_pure_split_goal_4 : dijkstra_linked_forward_star_partial_solve_wit_1_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (graph_has_size_vertex_valid_bounds
      g_low_level_spec vertex_count_pre source_pre PreH9 PreH10)
    as (_ & Hsource_bounds).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_1_pure : dijkstra_linked_forward_star_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_dijkstra_linked_forward_star_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_dijkstra_linked_forward_star_partial_solve_wit_1_pure_split_goal_2.
  - Goal_apply proof_of_dijkstra_linked_forward_star_partial_solve_wit_1_pure_split_goal_3.
  - Goal_apply proof_of_dijkstra_linked_forward_star_partial_solve_wit_1_pure_split_goal_4.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_3_pure_split_goal_1 : dijkstra_linked_forward_star_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (graph_has_size_vertex_valid_bounds
      g_low_level_spec vertex_count_pre source_pre PreH9 PreH10)
    as (_ & Hsource_bounds).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_3_pure_split_goal_2 : dijkstra_linked_forward_star_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (graph_has_size_vertex_valid_bounds
      g_low_level_spec vertex_count_pre source_pre PreH9 PreH10)
    as ((Hvertex_count_pos & Hvertex_count_max) & Hsource_bounds).
  dump_pre_spatial.
  unfold DijkstraGraph.max_vertices in *; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_3_pure_split_goal_3 : dijkstra_linked_forward_star_partial_solve_wit_3_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_3_pure_split_goal_4 : dijkstra_linked_forward_star_partial_solve_wit_3_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_3_pure : dijkstra_linked_forward_star_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_dijkstra_linked_forward_star_partial_solve_wit_3_pure_split_goal_1.
  - Goal_apply proof_of_dijkstra_linked_forward_star_partial_solve_wit_3_pure_split_goal_2.
  - Goal_apply proof_of_dijkstra_linked_forward_star_partial_solve_wit_3_pure_split_goal_3.
  - Goal_apply proof_of_dijkstra_linked_forward_star_partial_solve_wit_3_pure_split_goal_4.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_5_pure_split_goal_1 : dijkstra_linked_forward_star_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold priority_queue_pop_result in PreH15.
  destruct PreH15 as (Hqueue_nonempty & _).
  destruct queue_items as [| queue_item queue_items_tail].
  - contradiction.
  - rewrite Zlength_cons.
    pose proof (Zlength_nonneg queue_items_tail).
    dump_pre_spatial; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_5_pure_split_goal_2 : dijkstra_linked_forward_star_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
      (priority_queue_model_size_bounds
      queue_vertices queue_distances (Zlength queue_items) queue_items PreH16)
    as (Hqueue_size_bounds & _).
  dump_pre_spatial.
  unfold max_priority_queue_size in *; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_5_pure : dijkstra_linked_forward_star_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_dijkstra_linked_forward_star_partial_solve_wit_5_pure_split_goal_1.
  - Goal_apply proof_of_dijkstra_linked_forward_star_partial_solve_wit_5_pure_split_goal_2.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_12_pure_split_goal_1 : dijkstra_linked_forward_star_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Zlength_nonneg queue_items_before).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_partial_solve_wit_12_pure : dijkstra_linked_forward_star_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_dijkstra_linked_forward_star_partial_solve_wit_12_pure_split_goal_1.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_derive_high_level_spec_by_low_level_spec : dijkstra_linked_forward_star_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  rename H into Hsize_high_level_spec.
  rename H0 into Hsource_valid_high_level_spec.
  rename H1 into Hnonnegative_high_level_spec.
  rename H2 into Hno_overflow_high_level_spec.
  rename H3 into Hedge_count_nonnegative_high_level_spec.
  rename H4 into Hedge_count_bound_high_level_spec.
  rename H5 into Hforward_star_high_level_spec.
  rename H6 into Hdist_shape_high_level_spec.
  rename H7 into Hqueue_model_high_level_spec.
  set (X_low_level_spec :=
    result_state (eq (initial_state source_pre))
      (dijkstra_lfs_program source_pre
        head_values_high_level_spec to_values_high_level_spec
        weight_values_high_level_spec next_values_high_level_spec)).
  assert (Hsafe_first :
    safeExec (eq (initial_state source_pre))
      (dijkstra_lfs_program source_pre
        head_values_high_level_spec to_values_high_level_spec
        weight_values_high_level_spec next_values_high_level_spec)
      X_low_level_spec).
  {
    unfold X_low_level_spec.
    apply safeExec_result_state.
    exists (initial_state source_pre).
    reflexivity.
  }
  assert (Hinitial_refines :
    dijkstra_lfs_initial_refines g_high_level_spec source_pre
      head_values_high_level_spec to_values_high_level_spec
      weight_values_high_level_spec next_values_high_level_spec
      X_low_level_spec).
  {
    unfold dijkstra_lfs_initial_refines.
    exact Hsafe_first.
  }
  Exists g_high_level_spec head_values_high_level_spec
    to_values_high_level_spec weight_values_high_level_spec
    next_values_high_level_spec dist0_high_level_spec
    queue_vertices0_high_level_spec queue_distances0_high_level_spec
    queue_size0_high_level_spec queue_items0_high_level_spec
    X_low_level_spec.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre
      head_values_high_level_spec);
    cancel (IntArray.full to_pre edge_count_pre
      to_values_high_level_spec);
    cancel (IntArray.full weight_pre edge_count_pre
      weight_values_high_level_spec);
    cancel (IntArray.full next_pre edge_count_pre
      next_values_high_level_spec);
    cancel (IntArray.full dist_pre 10 dist0_high_level_spec);
    cancel (IntArray.full &( "priority_queue_vertex") 200005
      queue_vertices0_high_level_spec);
    cancel (IntArray.full &( "priority_queue_distance") 200005
      queue_distances0_high_level_spec);
    cancel (&( "priority_queue_size") # Int |->
      queue_size0_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros queue_vertices1_2 queue_distances1_2 queue_size1_2
      queue_items1_2 visited_out dist_out_2.
    assert (Hsafe_dist :
      safeExec (graph_dist_model g_high_level_spec dist_out_2)
        (return tt) X_low_level_spec).
    {
      eapply safeExec_conseq.
      - match goal with
        | Hsafe : safeExec
            (graph_state_model g_high_level_spec visited_out dist_out_2)
            (return tt) X_low_level_spec |- _ =>
            exact Hsafe
        end.
      - intros s Hmodel.
        apply graph_state_model_to_graph_dist_model in Hmodel.
        exact Hmodel.
    }
    assert (Hshortest :
      dijkstra_shortest_dist g_high_level_spec source_pre dist_out_2).
    {
      unfold X_low_level_spec in Hsafe_dist.
      eapply (dijkstra_lfs_program_correct
        g_high_level_spec vertex_count_pre edge_count_pre source_pre
        head_values_high_level_spec to_values_high_level_spec
        weight_values_high_level_spec next_values_high_level_spec
        dist_out_2).
      - exact Hsize_high_level_spec.
      - exact Hsource_valid_high_level_spec.
      - exact Hnonnegative_high_level_spec.
      - exact Hforward_star_high_level_spec.
      - exact Hno_overflow_high_level_spec.
      - exact Hsafe_dist.
    }
    Exists queue_vertices1_2 queue_distances1_2 queue_size1_2
      queue_items1_2 dist_out_2.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre
        head_values_high_level_spec);
      cancel (IntArray.full to_pre edge_count_pre
        to_values_high_level_spec);
      cancel (IntArray.full weight_pre edge_count_pre
        weight_values_high_level_spec);
      cancel (IntArray.full next_pre edge_count_pre
        next_values_high_level_spec);
      cancel (IntArray.full dist_pre 10 dist_out_2);
      cancel (IntArray.full &( "priority_queue_vertex") 200005
        queue_vertices1_2);
      cancel (IntArray.full &( "priority_queue_distance") 200005
        queue_distances1_2);
      cancel (&( "priority_queue_size") # Int |-> queue_size1_2).
    + split_pures; dump_pre_spatial; auto.
  - split_pures; dump_pre_spatial; auto.
Qed.
