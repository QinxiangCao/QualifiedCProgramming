Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.Dijkstra Require Import Dijkstra_linked_forward_star_decrease_key_goal.
From SimpleC.EE.LLM_bench.Algorithms.Dijkstra Require Import Dijkstra_linked_forward_star_decrease_key_proof_auto.
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
Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_lib.
Require Import Algorithms.Dijkstra.Dijkstra.
From GraphLib Require Import Zweight.
Require Import SimpleC.EE.LLM_bench.Algorithms.Dijkstra.Dijkstra_linked_forward_star_decrease_key_lib.
Import DijkstraGraph.
Import DijkstraLinkedForwardStar.
Import DijkstraDecreaseKey.
Local Open Scope sac.

Lemma dijkstra_dk_local_undef_full_to_zero_seg :
  forall p n,
    IntArray.undef_full p n |--
    IntArray.undef_seg (p + 0 * sizeof(INT)) 0 n.
Proof.
  intros p n.
  replace (p + 0 * sizeof(INT)) with p by lia.
  apply IntArray.undef_full_to_undef_seg.
Qed.

Lemma dijkstra_dk_zero_seg_to_undef_full :
  forall p n,
    IntArray.undef_seg (p + 0 * sizeof(INT)) 0 n |--
    IntArray.undef_full p n.
Proof.
  intros p n.
  eapply derivable1_trans with (y :=
    IntArray.undef_full ((p + 0 * sizeof(INT)) + 0 * sizeof(INT)) (n - 0)).
  - apply IntArray.undef_seg_to_undef_full.
  - replace (((p + 0 * sizeof(INT)) + 0 * sizeof(INT))) with p by lia.
    replace (n - 0) with n by lia.
    apply derivable1_refl.
Qed.

Lemma dijkstra_dk_base_seg_to_undef_full :
  forall p n,
    IntArray.undef_seg p 0 n |--
    IntArray.undef_full p n.
Proof.
  intros p n.
  eapply derivable1_trans with
    (y := IntArray.undef_full (p + 0 * sizeof(INT)) (n - 0)).
  - apply IntArray.undef_seg_to_undef_full.
  - replace (p + 0 * sizeof(INT)) with p by lia.
    replace (n - 0) with n by lia.
    apply derivable1_refl.
Qed.

Lemma dijkstra_dk_queue_key_undef_seg_to_undef_full :
  IntArray.undef_seg ( &( "queue_key" ) ) 0 100000 |--
  IntArray.undef_full ( &( "queue_key" ) ) 100000.
Proof.
  apply dijkstra_dk_base_seg_to_undef_full.
Qed.

Lemma dijkstra_dk_queue_data_undef_seg_to_undef_full :
  IntArray.undef_seg ( &( "queue_data" ) ) 0 100000 |--
    IntArray.undef_full ( &( "queue_data" ) ) 100000.
Proof.
  apply dijkstra_dk_base_seg_to_undef_full.
Qed.

Lemma dijkstra_dk_heap_representation_empty :
  heap_representation
    partial_map_empty (@nil Z) (@nil Z) (repeat_Z (-1) 10) 10 0.
Proof.
  unfold heap_representation, heap_map_relation, heap_ordered,
    heap_pos_consistent, heap_data_valid, heap_data_unique,
    heap_pos_backlinks, heap_pos_forward_links.
  simpl.
  split; [unfold heap_capacity; lia |].
  split; [unfold heap_capacity; lia |].
  split.
  - split; [reflexivity |].
    split; [reflexivity |].
    split.
    + intros i j Hi Hj _; lia.
    + split.
      * intros index Hidx; lia.
      * intros data_x key_x Hpresent.
        unfold partial_map_present, partial_map_get,
          partial_map_empty in Hpresent.
        discriminate.
  - split.
    + intros child Hchild; lia.
    + split; [lia |].
      split.
      * unfold repeat_Z.
        rewrite Zlength_correct, repeat_length.
        simpl; lia.
      * split.
        -- intros index Hidx; lia.
        -- split.
           ++ intros index Hidx; lia.
           ++ intros data_x Hbound.
              left.
              unfold repeat_Z, absent.
              rewrite Znth_repeat.
              reflexivity.
Qed.

Lemma dijkstra_dk_store_heap_empty_from_arrays :
  forall key data pos,
    IntArray.undef_seg key 0 100000 **
    IntArray.undef_seg data 0 100000 **
    IntArray.full pos 10 (repeat_Z (-1) 10) |--
    store_heap key data pos 10 100000 partial_map_empty 0.
Proof.
  intros key data pos.
  unfold store_heap.
  Exists (@nil Z) (@nil Z) (repeat_Z (-1) 10).
  rewrite !IntArray.full_empty.
  split_pure_spatial.
  - cancel (IntArray.undef_seg key 0 100000).
    cancel (IntArray.undef_seg data 0 100000).
    cancel (IntArray.full pos 10 (repeat_Z (-1) 10)).
  - split_pures; dump_pre_spatial; auto.
    exact dijkstra_dk_heap_representation_empty.
Qed.

Lemma dijkstra_dk_store_heap_zero_to_undef_fulls :
  forall key data pos M,
    store_heap key data pos 10 100000 M 0 |--
    “ partial_map_is_empty M ” &&
    IntArray.undef_full key 100000 **
    IntArray.undef_full data 100000 **
    IntArray.undef_full pos 10.
Proof.
  intros key data pos M.
  unfold store_heap at 1.
  Intros key_values.
  Intros data_values.
  Intros pos_values.
  match goal with
  | Hrep : heap_representation
      M key_values data_values pos_values 10 0 |- _ =>
      pose proof Hrep as Hrep_keep
  end.
  destruct Hrep_keep as (_ & _ & Hmap & _ & _).
  destruct Hmap as (Hkey_len & Hdata_len & _ & _ & Hpresent_index).
  assert (Hkey_nil : key_values = nil)
    by (apply Zlength_nil_inv; lia).
  assert (Hdata_nil : data_values = nil)
    by (apply Zlength_nil_inv; lia).
  assert (Hempty : partial_map_is_empty M).
  {
    unfold partial_map_is_empty.
    intros data_x key_x Hpresent.
    specialize (Hpresent_index data_x key_x Hpresent)
      as [index [Hidx _]].
    lia.
  }
  subst key_values data_values.
  split_pure_spatial.
  - rewrite IntArray.full_empty.
    rewrite IntArray.full_empty.
    eapply derivable1_trans with (y :=
      IntArray.undef_seg key 0 100000 **
      (IntArray.undef_seg data 0 100000 **
       IntArray.full pos 10 pos_values)).
    + entailer!.
    + apply derivable1_sepcon_mono.
      * apply dijkstra_dk_base_seg_to_undef_full.
      * apply derivable1_sepcon_mono.
        -- apply dijkstra_dk_base_seg_to_undef_full.
        -- apply (IntArray.full_to_undef_full pos 10 pos_values).
  - dump_pre_spatial; exact Hempty.
Qed.

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

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_1 : dijkstra_linked_forward_star_decrease_key_entail_wit_1.
Proof.
  right.
  intros.
  split_pure_spatial.
  - replace ((( &( "queue_key" ) ) + (0 * sizeof(INT)))) with ( &( "queue_key" ) ) by lia.
    replace ((( &( "queue_data" ) ) + (0 * sizeof(INT)))) with ( &( "queue_data" ) ) by lia.
    eapply derivable1_trans with (y :=
      (IntArray.undef_seg ( &( "queue_data" ) ) 0 100000) **
      (IntArray.undef_seg ( &( "queue_key" ) ) 0 100000)).
    + apply derivable1_sepcon_mono;
        apply IntArray.undef_full_to_undef_seg.
    + apply derivable1_sepcon_comm.
  - unfold repeat_Z.
    simpl.
    try reflexivity.
    entailer!.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_2 : dijkstra_linked_forward_star_decrease_key_entail_wit_2.
Proof.
  right.
  intros.
  split_pure_spatial.
  - entailer!.
  - entailer!.
    symmetry.
    apply repeat_Z_tail.
    lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_3 : dijkstra_linked_forward_star_decrease_key_entail_wit_3.
Proof.
  right.
  intros.
  replace i with 10 by lia.
  apply derivable1_refl.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_4 : dijkstra_linked_forward_star_decrease_key_entail_wit_4.
Proof.
  right.
  LLM_pre_process ltac:(int_auto).
  Exists (partial_map_add partial_map_empty source_pre 0)
    (fun _ : Z => False).
  split_pure_spatial.
  - replace (( &( "queue_pos" ) ) + 0 * sizeof(INT))
      with ( &( "queue_pos" ) ) by lia.
    unfold store_heap.
    Exists (@nil Z) (@nil Z) (repeat_Z (-1) 10).
    rewrite !IntArray.full_empty.
    split_pure_spatial.
    + cancel (IntArray.undef_seg (( &( "queue_key" ) ) + 0 * sizeof(INT)) 0 100000).
      cancel (IntArray.undef_seg (( &( "queue_data" ) ) + 0 * sizeof(INT)) 0 100000).
      cancel (IntArray.full ( &( "queue_pos" ) ) 10 (repeat_Z (-1) 10)).
    + split_pures; dump_pre_spatial; auto.
      exact dijkstra_dk_heap_representation_empty.
  - split_pures; dump_pre_spatial; auto; try lia.
    + unfold visited_set_empty; tauto.
    + apply partial_map_empty_absent.
    + unfold dk_map_queue_push_result; reflexivity.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_5 : dijkstra_linked_forward_star_decrease_key_entail_wit_5.
Proof.
  right.
  LLM_pre_process ltac:(int_auto).
  Exists visited_init.
  split_pure_spatial.
  - entailer!.
  - subst queue_size queue_map_empty.
    split_pures; dump_pre_spatial; auto; try lia.
    + eapply dijkstra_dk_initial_loop_state; eauto.
    + eapply dijkstra_dk_lfs_initial_to_loop_refines; eauto.
      unfold dk_map_queue_push_result; reflexivity.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_6 : dijkstra_linked_forward_star_decrease_key_entail_wit_6.
Proof.
  right.
  LLM_pre_process ltac:(int_auto).
  Exists visited_cur_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_7 : dijkstra_linked_forward_star_decrease_key_entail_wit_7.
Proof.
  right.
  LLM_pre_process ltac:(int_auto).
  destruct popped as [pop_key pop_data].
  simpl in PreH1, PreH2, PreH3.
  subst key_out_callee_v data_out_callee_v.
  assert (Hpop :
    dk_map_queue_pop_result queue_map_2
      (partial_map_remove queue_map_2 pop_data) pop_data pop_key).
  {
    unfold dk_map_queue_pop_result, heap_item.
    split; [exact PreH3 | reflexivity].
  }
  pose proof
    (dijkstra_dk_map_pop_result_bounds
      g_low_level_spec vertex_count_pre source_pre visited_cur_2
      dist_cur_2 queue_map_2
      (partial_map_remove queue_map_2 pop_data) pop_data pop_key
      PreH8 PreH11 Hpop)
    as (Hpop_storage & Hpop_vertex_bounds & Hpop_distance_bounds).
  pose proof
    (dijkstra_dk_map_loop_refines_pop
      g_low_level_spec source_pre head_values_low_level_spec
      to_values_low_level_spec weight_values_low_level_spec
      next_values_low_level_spec visited_cur_2 dist_cur_2
      queue_map_2 (partial_map_remove queue_map_2 pop_data)
      pop_data pop_key X_low_level_spec
      Hpop PreH11 PreH12)
    as Hafter_pop.
  Exists visited_cur_2 queue_map_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; auto; try lia.
    + unfold item_data; simpl; lia.
    + unfold item_data; simpl; lia.
    + unfold item_data, storage_index, DijkstraGraph.max_vertices in *;
        simpl in *; lia.
    + unfold item_key; simpl; lia.
    + unfold item_key, DijkstraGraph.infinity in *; simpl in *; lia.
Qed. 

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_8 : dijkstra_linked_forward_star_decrease_key_entail_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (forward_star_model_head_case_0
      g_low_level_spec vertex_count_pre edge_count_pre
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      cur_vertex PreH5 PreH17 ltac:(lia)) as Hhead.
  assert (Hcur_valid : vertex_valid g_low_level_spec cur_vertex)
    by (unfold vertex_valid, DijkstraGraph.vertex_valid;
        unfold graph_has_size in PreH5; lia).
  pose (visited_edge_cur := fun v : Z => visited_cur_2 v \/ v = cur_vertex).
  assert (Hvisit_add : visited_set_add visited_cur_2 cur_vertex visited_edge_cur)
    by (unfold visited_set_add, visited_edge_cur; tauto).
  pose proof
    (dijkstra_dk_map_after_pop_edge_loop_state
      g_low_level_spec edge_count_pre source_pre
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_cur_2 visited_edge_cur dist_cur queue_map_2
      cur_vertex cur_distance X_low_level_spec
      PreH17 Hcur_valid Hvisit_add PreH16)
    as Hedge_state.
  pose proof
    (dijkstra_dk_map_after_pop_refines_to_edge_loop
      g_low_level_spec edge_count_pre source_pre
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_cur_2 visited_edge_cur dist_cur queue_map_2
      cur_vertex cur_distance X_low_level_spec
      PreH17 Hcur_valid Hvisit_add PreH16)
    as Hedge_refines.
  destruct Hhead as [Hhead_nil | Hhead_edge].
  - Left.
    Exists dist_cur queue_map_2 visited_cur_2 visited_edge_cur.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (IntArray.full dist_pre 10 dist_cur).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT)))
        10 100000 queue_map_2 queue_size).
    + split_pures; dump_pre_spatial; auto; try lia.
  - Right.
    Exists dist_cur queue_map_2 visited_cur_2 visited_edge_cur.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (IntArray.full dist_pre 10 dist_cur).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT)))
        10 100000 queue_map_2 queue_size).
    + split_pures; dump_pre_spatial; auto; try lia.
      * unfold edge_index in Hhead_edge; lia.
      * unfold edge_index in Hhead_edge; lia.
Qed. 

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_9 : dijkstra_linked_forward_star_decrease_key_entail_wit_9.
Proof.
  right.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (forward_star_model_edge_bounds
      g_low_level_spec edge_count_pre
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      edge PreH18 ltac:(unfold edge_index; lia))
    as (Hto_graph & Hto_storage & Hweight_bounds & _).
  assert (Hto_vertex_count :
    0 <= Znth edge to_values_low_level_spec 0 < vertex_count_pre)
    by (unfold graph_has_size in PreH6; lia).
  Exists visited_cur_2 visited_edge_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; auto; try reflexivity; try lia;
    try (unfold storage_index, DijkstraGraph.max_vertices in Hto_storage; lia);
    try (unfold DijkstraGraph.infinity in Hweight_bounds; lia).
Qed. 

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_10 : dijkstra_linked_forward_star_decrease_key_entail_wit_10.
Proof.
  left.
  LLM_pre_process ltac:(int_auto).
  sep_apply (dk_store_heap_size_data_bound
    (( &( "queue_key" ) ) + (0 * sizeof(INT)))
    (( &( "queue_data" ) ) + (0 * sizeof(INT)))
    (( &( "queue_pos" ) ) + (0 * sizeof(INT)))
    10 100000 queue_map queue_size).
  Intros_p Hqueue_size_bounds.
  destruct Hqueue_size_bounds as
    (Hqueue_size_nonneg & Hqueue_size_data & Hqueue_size_capacity).
  assert (Hneighbor_valid : vertex_valid g_low_level_spec neighbor).
  {
    unfold vertex_valid, DijkstraGraph.vertex_valid.
    unfold graph_has_size in PreH8; lia.
  }
  assert (Hneighbor_storage : storage_index neighbor)
    by (unfold storage_index, DijkstraGraph.max_vertices; lia).
  assert (Hdist_cell_neighbor :
    dist_cell dist_edge neighbor = Znth neighbor dist_edge 0).
  {
    apply dist_cell_Znth_0.
    - unfold dijkstra_dk_map_edge_loop_state in PreH25.
      destruct PreH25 as [Hloop _].
      unfold dijkstra_dk_map_loop_state in Hloop.
      tauto.
    - exact Hneighbor_storage.
  }
  assert (Hdist_neighbor_safe :
    0 <= dist_cell dist_edge neighbor <= DijkstraGraph.infinity).
  {
    unfold dijkstra_dk_map_edge_loop_state in PreH25.
    destruct PreH25 as [Hloop _].
    unfold dijkstra_dk_map_loop_state in Hloop.
    destruct Hloop as (_ & _ & _ & _ & Hsafe & _).
    apply Hsafe.
    exact Hneighbor_storage.
  }
  assert (Hrelax_cell :
    cur_distance + edge_weight0 < dist_cell dist_edge neighbor)
    by (rewrite Hdist_cell_neighbor; exact PreH1).
  assert (Hcandidate_bounds :
    0 <= cur_distance + edge_weight0 < DijkstraGraph.infinity)
    by (unfold DijkstraGraph.infinity in *; lia).
  assert (Hedge_state_after :
    dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge_2
      cur_vertex cur_distance edge
      (replace_Znth neighbor (cur_distance + edge_weight0) dist_edge)
      queue_map).
  {
    eapply (dijkstra_dk_map_edge_loop_state_relax_update
      g_low_level_spec vertex_count_pre source_pre visited_edge_2
      cur_vertex cur_distance edge neighbor edge_weight0
      (cur_distance + edge_weight0) dist_edge queue_map).
    - exact PreH8.
    - exact Hneighbor_valid.
    - exact Hneighbor_storage.
    - exact Hcandidate_bounds.
    - lia.
    - reflexivity.
    - exact Hrelax_cell.
    - exact PreH25.
  }
  assert (Hupdate_pre :
    partial_map_update_or_add_pre queue_map neighbor
      (cur_distance + edge_weight0)).
  {
    pose proof PreH26 as Hrefines_parts.
    unfold dijkstra_dk_map_edge_loop_refines in Hrefines_parts.
    destruct Hrefines_parts as (_ & Hexact & _).
    destruct Hexact as (Hitem & _Hcover).
    destruct (classic (partial_map_absent queue_map neighbor))
      as [Habs | Hnot_abs].
    - left; exact Habs.
    - right.
      unfold partial_map_decrease_key_pre, decrease_key_pre.
      unfold partial_map_absent, partial_map_get in Hnot_abs.
      destruct (queue_map neighbor) as [old_key |] eqn:Hget.
      + exists old_key.
        split; [exact Hget |].
        specialize (Hitem neighbor old_key Hget)
          as (_ & _ & Hold_eq & _).
        lia.
      + contradiction Hnot_abs; reflexivity.
  }
  assert (Hafter_relax :
    dijkstra_dk_map_after_relax_refines g_low_level_spec source_pre
      cur_vertex cur_distance edge neighbor (cur_distance + edge_weight0)
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_edge_2
      (replace_Znth neighbor (cur_distance + edge_weight0) dist_edge)
      queue_map X_low_level_spec).
  {
    eapply dijkstra_dk_map_edge_loop_refines_relax_to_after_relax.
    - exact PreH8.
    - exact PreH27.
    - unfold edge_index; lia.
    - exact PreH25.
    - lia.
    - exact PreH17.
    - exact PreH18.
    - reflexivity.
    - exact Hneighbor_valid.
    - exact Hneighbor_storage.
    - exact Hcandidate_bounds.
    - lia.
    - unfold DijkstraGraph.infinity; lia.
    - exact Hrelax_cell.
    - exact PreH26.
  }
  pose proof Hupdate_pre as Hupdate_pre_keep.
  set (queue_map_after :=
    partial_map_update_or_add queue_map neighbor
      (cur_distance + edge_weight0)).
  destruct Hupdate_pre as [Habsent | Hdecrease].
  - assert (Hupdate_result :
      dk_map_queue_update_or_push_result queue_map queue_map_after
        queue_size (queue_size + 1) neighbor (cur_distance + edge_weight0)).
    {
      unfold dk_map_queue_update_or_push_result,
        partial_map_update_or_add_size, queue_map_after.
      split; [left; split; [exact Habsent | reflexivity] | reflexivity].
    }
    Exists queue_map_after (queue_size + 1)
      (replace_Znth neighbor (cur_distance + edge_weight0) dist_edge)
      queue_map visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full dist_pre 10
        (replace_Znth neighbor (cur_distance + edge_weight0) dist_edge)).
      cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT)))
        10 100000 queue_map queue_size).
    + split_pures; dump_pre_spatial; auto; try lia;
        try exact PreH24; try exact Hedge_state_after;
        try exact Hafter_relax; try exact Hupdate_pre_keep;
        try exact Hupdate_result; try exact PreH27.
  - assert (Hupdate_result :
      dk_map_queue_update_or_push_result queue_map queue_map_after
        queue_size queue_size neighbor (cur_distance + edge_weight0)).
    {
      unfold dk_map_queue_update_or_push_result,
        partial_map_update_or_add_size, queue_map_after.
      split; [right; split; [exact Hdecrease | reflexivity] | reflexivity].
    }
    Exists queue_map_after queue_size
      (replace_Znth neighbor (cur_distance + edge_weight0) dist_edge)
      queue_map visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full dist_pre 10
        (replace_Znth neighbor (cur_distance + edge_weight0) dist_edge)).
      cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT)))
        10 100000 queue_map queue_size).
    + split_pures; dump_pre_spatial; auto; try lia;
        try exact PreH24; try exact Hedge_state_after;
        try exact Hafter_relax; try exact Hupdate_pre_keep;
        try exact Hupdate_result; try exact PreH27.
Qed. 

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_11_1 : dijkstra_linked_forward_star_decrease_key_entail_wit_11_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (forward_star_model_next_case_0
      g_low_level_spec edge_count_pre head_values_low_level_spec
      to_values_low_level_spec weight_values_low_level_spec
      next_values_low_level_spec edge PreH31
      ltac:(unfold edge_index; lia)) as Hnext.
  assert (Hnext_nonneg : -1 <= Znth edge next_values_low_level_spec 0)
    by (destruct Hnext as [Hnext_nil | Hnext_edge];
        [rewrite Hnext_nil | unfold edge_index in Hnext_edge]; lia).
  assert (Hn_after_bounds : 0 <= n_after /\ n_after <= 100000).
  {
    pose proof PreH1 as Hresult_size.
    destruct Hresult_size as [(_ & Hn_after) | (_ & Hn_after)];
      subst n_after; lia.
  }
  assert (Hcur_valid : vertex_valid g_low_level_spec cur_vertex).
  {
    unfold vertex_valid, DijkstraGraph.vertex_valid.
    unfold graph_has_size in PreH7; lia.
  }
  assert (Hupdate_result_actual :
    dk_map_queue_update_or_push_result queue_map_before
      (partial_map_update_or_add queue_map_before neighbor candidate)
      queue_size n_after neighbor candidate).
  {
    unfold dk_map_queue_update_or_push_result.
    split; [exact PreH1 | reflexivity].
  }
  assert (Hrefines_next :
    dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex
      cur_distance (Znth edge next_values_low_level_spec 0)
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_edge_2 dist_after
      (partial_map_update_or_add queue_map_before neighbor candidate)
      X_low_level_spec).
  {
    eapply dijkstra_dk_map_after_relax_refines_update_to_edge_loop.
    - exact PreH31.
    - exact Hcur_valid.
    - unfold edge_index; lia.
    - exact PreH16.
    - exact Hupdate_result_actual.
    - exact PreH28.
  }
  assert (Hedge_next :
    dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge_2
      cur_vertex cur_distance (Znth edge next_values_low_level_spec 0)
      dist_after
      (partial_map_update_or_add queue_map_before neighbor candidate)).
  {
    eapply dijkstra_dk_map_after_relax_update_edge_loop_state.
    - exact PreH31.
    - unfold edge_index; lia.
    - exact PreH27.
    - exact Hupdate_result_actual.
    - exact PreH28.
  }
  destruct Hnext as [Hnext_nil | Hnext_edge].
  - Left.
    Exists dist_after
      (partial_map_update_or_add queue_map_before neighbor candidate)
      visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (IntArray.full dist_pre 10 dist_after).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT)))
        10 100000
        (partial_map_update_or_add queue_map_before neighbor candidate)
        n_after).
    + destruct Hn_after_bounds as (Hn_lower & Hn_upper).
      split_pures; dump_pre_spatial; auto; try lia;
        try exact PreH26; try exact Hedge_next;
        try exact Hrefines_next; try exact Hnext_nil.
  - Right.
    Exists dist_after
      (partial_map_update_or_add queue_map_before neighbor candidate)
      visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (IntArray.full dist_pre 10 dist_after).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT)))
        10 100000
        (partial_map_update_or_add queue_map_before neighbor candidate)
        n_after).
    + destruct Hn_after_bounds as (Hn_lower & Hn_upper).
      split_pures; dump_pre_spatial; auto; try lia;
        try exact PreH26; try exact Hedge_next;
        try exact Hrefines_next.
      * unfold edge_index in Hnext_edge; lia.
      * unfold edge_index in Hnext_edge; lia.
Qed. 

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_11_2 : dijkstra_linked_forward_star_decrease_key_entail_wit_11_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (forward_star_model_next_case_0
      g_low_level_spec edge_count_pre head_values_low_level_spec
      to_values_low_level_spec weight_values_low_level_spec
      next_values_low_level_spec edge PreH27
      ltac:(unfold edge_index; lia)) as Hnext.
  assert (Hnext_nonneg : -1 <= Znth edge next_values_low_level_spec 0)
    by (destruct Hnext as [Hnext_nil | Hnext_edge];
        [rewrite Hnext_nil | unfold edge_index in Hnext_edge]; lia).
  assert (Hedge_next :
    dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge_2
      cur_vertex cur_distance (Znth edge next_values_low_level_spec 0)
      dist_edge_2 queue_map_2).
  {
    eapply dijkstra_dk_map_edge_loop_next_state; eauto.
  }
  assert (Hneighbor_valid : vertex_valid g_low_level_spec neighbor).
  {
    unfold vertex_valid, DijkstraGraph.vertex_valid.
    unfold graph_has_size in PreH8; lia.
  }
  assert (Hdist_cell_neighbor :
    dist_cell dist_edge_2 neighbor = Znth neighbor dist_edge_2 0).
  {
    apply (dist_cell_Znth_0 dist_edge_2 neighbor).
    - unfold dijkstra_dk_map_edge_loop_state in PreH25.
      destruct PreH25 as [Hloop _].
      unfold dijkstra_dk_map_loop_state in Hloop.
      tauto.
    - unfold storage_index, DijkstraGraph.max_vertices; lia.
  }
  assert (Hrefines_next :
    dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex
      cur_distance (Znth edge next_values_low_level_spec 0)
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_edge_2 dist_edge_2 queue_map_2 X_low_level_spec).
  {
    eapply dijkstra_dk_map_edge_loop_refines_no_relax_to_next.
    - exact PreH27.
    - unfold edge_index; lia.
    - exact PreH25.
    - lia.
    - exact PreH17.
    - exact PreH18.
    - exact Hneighbor_valid.
    - right; right.
      rewrite Hdist_cell_neighbor.
      exact PreH1.
    - exact PreH26.
  }
  destruct Hnext as [Hnext_nil | Hnext_edge].
  - Left.
    Exists dist_edge_2 queue_map_2 visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (IntArray.full dist_pre 10 dist_edge_2).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT)))
        10 100000 queue_map_2 queue_size).
    + split_pures; dump_pre_spatial; auto; try lia;
        try exact Hedge_next; try exact Hrefines_next; try exact Hnext_nil.
  - Right.
    Exists dist_edge_2 queue_map_2 visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (IntArray.full dist_pre 10 dist_edge_2).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT)))
        10 100000 queue_map_2 queue_size).
    + split_pures; dump_pre_spatial; auto; try lia;
        try exact Hedge_next; try exact Hrefines_next.
      * unfold edge_index in Hnext_edge; lia.
      * unfold edge_index in Hnext_edge; lia.
Qed. 

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_11_3 : dijkstra_linked_forward_star_decrease_key_entail_wit_11_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (forward_star_model_next_case_0
      g_low_level_spec edge_count_pre head_values_low_level_spec
      to_values_low_level_spec weight_values_low_level_spec
      next_values_low_level_spec edge PreH26
      ltac:(unfold edge_index; lia)) as Hnext.
  assert (Hnext_nonneg : -1 <= Znth edge next_values_low_level_spec 0)
    by (destruct Hnext as [Hnext_nil | Hnext_edge];
        [rewrite Hnext_nil | unfold edge_index in Hnext_edge]; lia).
  assert (Hedge_next :
    dijkstra_dk_map_edge_loop_state g_low_level_spec source_pre visited_edge_2
      cur_vertex cur_distance (Znth edge next_values_low_level_spec 0)
      dist_edge_2 queue_map_2).
  {
    eapply dijkstra_dk_map_edge_loop_next_state; eauto.
  }
  assert (Hneighbor_valid : vertex_valid g_low_level_spec neighbor).
  {
    unfold vertex_valid, DijkstraGraph.vertex_valid.
    unfold graph_has_size in PreH7; lia.
  }
  assert (Hrefines_next :
    dijkstra_dk_map_edge_loop_refines g_low_level_spec source_pre cur_vertex
      cur_distance (Znth edge next_values_low_level_spec 0)
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_edge_2 dist_edge_2 queue_map_2 X_low_level_spec).
  {
    eapply dijkstra_dk_map_edge_loop_refines_no_relax_to_next.
    - exact PreH26.
    - unfold edge_index; lia.
    - exact PreH24.
    - lia.
    - exact PreH16.
    - exact PreH17.
    - exact Hneighbor_valid.
    - right; left; exact PreH1.
    - exact PreH25.
  }
  destruct Hnext as [Hnext_nil | Hnext_edge].
  - Left.
    Exists dist_edge_2 queue_map_2 visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (IntArray.full dist_pre 10 dist_edge_2).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT)))
        10 100000 queue_map_2 queue_size).
    + split_pures; dump_pre_spatial; auto; try lia.
  - Right.
    Exists dist_edge_2 queue_map_2 visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (IntArray.full dist_pre 10 dist_edge_2).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT)))
        10 100000 queue_map_2 queue_size).
    + split_pures; dump_pre_spatial; auto; try lia.
      * unfold edge_index in Hnext_edge; lia.
      * unfold edge_index in Hnext_edge; lia.
Qed. 

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_12 : dijkstra_linked_forward_star_decrease_key_entail_wit_12.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hloop_state :
    dijkstra_dk_map_loop_state g_low_level_spec source_pre
      visited_edge dist_edge queue_map_2).
  {
    eapply dijkstra_dk_map_edge_loop_to_loop_state; eauto.
  }
  assert (Hrefines_loop :
    dijkstra_dk_map_loop_refines g_low_level_spec source_pre
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_edge dist_edge queue_map_2 X_low_level_spec).
  {
    eapply dijkstra_dk_map_edge_loop_refines_break_to_loop; eauto.
  }
  Exists visited_edge dist_edge queue_map_2.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
    cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
    cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
    cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
    cancel (IntArray.full dist_pre 10 dist_edge).
    cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) (( &( "queue_pos" ) ) + (0 * sizeof(INT)))
      10 100000 queue_map_2 queue_size).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed. 

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_entail_wit_13 : dijkstra_linked_forward_star_decrease_key_entail_wit_13.
Proof.
  right.
  LLM_pre_process ltac:(int_auto).
  subst queue_size.
  eapply derivable1_trans with (y :=
    “ partial_map_is_empty queue_map ” &&
    IntArray.undef_full ( &( "queue_key" ) ) 100000 **
    IntArray.undef_full ( &( "queue_data" ) ) 100000 **
    IntArray.undef_full ( &( "queue_pos" ) ) 10).
  - replace ((( &( "queue_key" ) ) + 0 * sizeof(INT))) with
      ( &( "queue_key" ) ) by lia.
    replace ((( &( "queue_data" ) ) + 0 * sizeof(INT))) with
      ( &( "queue_data" ) ) by lia.
    replace ((( &( "queue_pos" ) ) + 0 * sizeof(INT))) with
      ( &( "queue_pos" ) ) by lia.
    apply dijkstra_dk_store_heap_zero_to_undef_fulls.
  - 
  Intros_p Hempty.
  assert (Hreturn :
    safeExec (graph_state_model g_low_level_spec visited_cur dist_cur)
      (return tt) X_low_level_spec).
  {
    eapply dijkstra_dk_map_loop_refines_empty_to_return; eauto.
  }
  Exists visited_cur queue_map.
  split_pure_spatial.
  + cancel (IntArray.undef_full ( &( "queue_key" ) ) 100000).
    cancel (IntArray.undef_full ( &( "queue_data" ) ) 100000).
    cancel.
  + split_pures; dump_pre_spatial; auto.
Qed. 

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure_split_goal_1 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (graph_has_size_vertex_valid_bounds
      g_low_level_spec vertex_count_pre source_pre PreH7 PreH8)
    as ((Hvertex_count_pos & _) & _).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure_split_goal_2 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (graph_has_size_bounds g_low_level_spec vertex_count_pre PreH7)
    as Hvertex_count_bounds.
  dump_pre_spatial.
  unfold DijkstraGraph.max_vertices in *; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure_split_goal_3 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (graph_has_size_vertex_valid_bounds
      g_low_level_spec vertex_count_pre source_pre PreH7 PreH8)
    as (_ & Hsource_bounds).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure_split_goal_4 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (graph_has_size_vertex_valid_bounds
      g_low_level_spec vertex_count_pre source_pre PreH7 PreH8)
    as (_ & Hsource_bounds).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_1_pure.
Proof.
  right.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (graph_has_size_vertex_valid_bounds
      g_low_level_spec vertex_count_pre source_pre PreH7 PreH8)
    as (Hvertex_count_bounds & Hsource_bounds).
  destruct Hvertex_count_bounds as (Hvertex_count_pos & Hvertex_count_upper).
  split_pures; dump_pre_spatial.
  all: unfold DijkstraGraph.max_vertices in *; lia.
Qed.

Lemma dijkstra_dk_queue_pos_init_partial_solve_wit_2 : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (graph_has_size_vertex_valid_bounds
      g_low_level_spec vertex_count_pre source_pre PreH4 PreH5)
    as (Hvertex_count_bounds & Hsource_bounds).
  destruct Hvertex_count_bounds as (_ & Hvertex_count_upper).
  rewrite (IntArray.undef_seg_unfold ( &( "queue_pos" ) ) i 10) by lia.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec);
    cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec);
    cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec);
    cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec);
    cancel (IntArray.full dist_pre 10 dist_init);
    cancel (IntArray.undef_seg (( &( "queue_key" ) ) + (0 * sizeof(INT))) 0 100000);
    cancel (IntArray.undef_seg (( &( "queue_data" ) ) + (0 * sizeof(INT))) 0 100000);
    cancel (IntArray.full ( &( "queue_pos" ) ) i (repeat_Z (-1) i));
    cancel.
  - split_pures; dump_pre_spatial; auto.
    all: unfold DijkstraGraph.max_vertices in *; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_partial_solve_wit_3_pure : dijkstra_linked_forward_star_decrease_key_partial_solve_wit_3_pure.
Proof.
  right.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (graph_has_size_vertex_valid_bounds
      g_low_level_spec vertex_count_pre source_pre PreH10 PreH11)
    as (Hvertex_count_bounds & Hsource_bounds).
  destruct Hvertex_count_bounds as (_ & Hvertex_count_upper).
  split_pures; dump_pre_spatial.
  all: unfold DijkstraGraph.max_vertices in *; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_decrease_key_derive_high_level_spec_by_low_level_spec : dijkstra_linked_forward_star_decrease_key_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  rename H into Hsize_high_level_spec.
  rename H0 into Hsource_valid_high_level_spec.
  rename H1 into Hnonnegative_high_level_spec.
  rename H2 into Hno_overflow_high_level_spec.
  rename H3 into Hheap_capacity_pos_high_level_spec.
  rename H4 into Hheap_capacity_max_high_level_spec.
  rename H5 into Hedge_capacity_high_level_spec.
  rename H6 into Hedge_count_nonnegative_high_level_spec.
  rename H7 into Hedge_count_bound_high_level_spec.
  rename H8 into Hdist_shape_high_level_spec.
  sep_apply (@GraphForwardStar.store_graph_elim_with_size
    g_high_level_spec vertex_count_pre edge_count_pre
    head_pre to_pre weight_pre next_pre Hsize_high_level_spec).
  Intros head_values_high_level_spec to_values_high_level_spec
    weight_values_high_level_spec next_values_high_level_spec.
  match goal with
  | H : forward_star_model g_high_level_spec edge_count_pre
          head_values_high_level_spec to_values_high_level_spec
          weight_values_high_level_spec next_values_high_level_spec |- _ =>
      rename H into Hforward_star_high_level_spec
  end.
  set (X_low_level_spec :=
    result_state (eq (initial_state source_pre))
      (dijkstra_dk_lfs_program source_pre
        head_values_high_level_spec to_values_high_level_spec
        weight_values_high_level_spec next_values_high_level_spec)).
  assert (Hsafe_first :
    safeExec (eq (initial_state source_pre))
      (dijkstra_dk_lfs_program source_pre
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
    dijkstra_dk_lfs_initial_refines g_high_level_spec source_pre
      head_values_high_level_spec to_values_high_level_spec
      weight_values_high_level_spec next_values_high_level_spec
      X_low_level_spec).
  {
    unfold dijkstra_dk_lfs_initial_refines.
    split; [exact Hsafe_first | exact Hno_overflow_high_level_spec].
  }
  Exists g_high_level_spec head_values_high_level_spec
    to_values_high_level_spec weight_values_high_level_spec
    next_values_high_level_spec dist0_high_level_spec
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
    cancel (IntArray.full dist_pre 10 dist0_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros visited_out dist_out_2.
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
      eapply (dijkstra_dk_lfs_program_correct
        g_high_level_spec vertex_count_pre edge_count_pre source_pre
        head_values_high_level_spec to_values_high_level_spec
        weight_values_high_level_spec next_values_high_level_spec); eauto.
    }
    Exists dist_out_2.
    split_pure_spatial.
    + sep_apply (@GraphForwardStar.store_graph_intro_with_size
        g_high_level_spec vertex_count_pre edge_count_pre
        head_pre to_pre weight_pre next_pre
        head_values_high_level_spec to_values_high_level_spec
        weight_values_high_level_spec next_values_high_level_spec
        Hsize_high_level_spec
        Hforward_star_high_level_spec);
      cancel (GraphForwardStar.store_graph
        g_high_level_spec edge_count_pre head_pre to_pre weight_pre next_pre);
      cancel (IntArray.full dist_pre 10 dist_out_2).
    + split_pures; dump_pre_spatial; auto.
  - split_pures; dump_pre_spatial; auto.
Qed.
