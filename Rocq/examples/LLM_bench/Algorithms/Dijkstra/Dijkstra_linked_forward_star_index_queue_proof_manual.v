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
From SimpleC.EE.LLM_bench.Algorithms.Dijkstra Require Import Dijkstra_linked_forward_star_index_queue_goal.
From SimpleC.EE.LLM_bench.Algorithms.Dijkstra Require Import Dijkstra_linked_forward_star_index_queue_proof_auto.
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
Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.
Require Import Algorithms.Dijkstra.Dijkstra.
From GraphLib Require Import Zweight.
Require Import SimpleC.EE.LLM_bench.Algorithms.Dijkstra.Dijkstra_linked_forward_star_index_queue_lib.
Import DijkstraGraph.
Import DijkstraLinkedForwardStar.
Import DijkstraIndexQueue.
Local Open Scope sac.

Lemma dijkstra_index_queue_sepcon_assoc2 :
  forall P Q R : Assertion,
    (P ** Q) ** R |-- P ** (Q ** R).
Proof.
  intros.
  rewrite derivable1_sepcon_comm.
  rewrite derivable1_sepcon_assoc1.
  rewrite <- (derivable1_sepcon_comm (Q ** R) P).
  rewrite <- (derivable1_sepcon_assoc1 Q R P).
  rewrite <- (derivable1_sepcon_comm (R ** P) Q).
  apply derivable1_refl.
Qed.

Lemma dijkstra_index_queue_undef_pair_merge :
  forall key data lo mid hi,
    lo <= mid <= hi ->
    IntArray.undef_seg key lo mid **
    IntArray.undef_seg data lo mid **
    IntArray.undef_seg key mid hi **
    IntArray.undef_seg data mid hi |--
    IntArray.undef_seg key lo hi **
    IntArray.undef_seg data lo hi.
Proof.
  intros key data lo mid hi Hrange.
  eapply derivable1_trans with (y :=
    (IntArray.undef_seg key lo mid **
     IntArray.undef_seg key mid hi) **
    (IntArray.undef_seg data lo mid **
     IntArray.undef_seg data mid hi)).
  - entailer!.
  - apply derivable1_sepcon_mono;
      apply IntArray.undef_seg_merge_to_undef_seg; lia.
Qed.

Lemma dijkstra_index_queue_local_undef_full_to_zero_seg :
  forall p n,
    IntArray.undef_full p n |--
    IntArray.undef_seg (p + 0 * sizeof(INT)) 0 n.
Proof.
  intros p n.
  replace (p + 0 * sizeof(INT)) with p by lia.
  apply IntArray.undef_full_to_undef_seg.
Qed.

Lemma dijkstra_index_queue_heap_tail_zero_to_undef_pair :
  forall key data,
    heap_tail key 0 ** heap_tail data 0 |--
    IntArray.undef_seg key 0 heap_capacity **
    IntArray.undef_seg data 0 heap_capacity.
Proof.
  intros key data.
  unfold heap_tail.
  destruct (Z_lt_dec 0 heap_capacity) as [_ | Hnot].
  2:{ unfold heap_capacity in Hnot; lia. }
  unfold heap_spare.
  replace (0 + 1) with 1 by lia.
  apply derivable1_sepcon_mono;
    apply IntArray.undef_seg_merge_to_undef_seg;
    unfold heap_capacity; lia.
Qed.

Lemma dijkstra_index_queue_undef_pair_to_heap_tail_zero :
  forall key data,
    IntArray.undef_seg key 0 heap_capacity **
    IntArray.undef_seg data 0 heap_capacity |--
    heap_tail key 0 ** heap_tail data 0.
Proof.
  intros key data.
  apply derivable1_sepcon_mono;
    apply undef_seg_to_heap_tail;
    unfold heap_capacity; lia.
Qed.

Lemma dijkstra_index_queue_store_heap_zero_to_emp :
  forall key data queue_set,
    store_heap key data queue_set 0 |--
    “ mlist queue_set = nil ” &&
    IntArray.undef_seg key 0 heap_capacity **
    IntArray.undef_seg data 0 heap_capacity.
Proof.
  intros key data queue_set.
  unfold store_heap.
  Intros key_values.
  Intros data_values.
  match goal with
  | Hrep : heap_representation queue_set key_values data_values 0 |- _ =>
      destruct Hrep as (_ & _ & Hsize & Hkey_len & Hdata_len & _ & _);
      assert (Hempty : mlist queue_set = nil) by
        (unfold multiset_size in Hsize; apply Zlength_nil_inv; lia);
      assert (Hkey_nil : key_values = nil) by
        (apply Zlength_nil_inv; lia);
      assert (Hdata_nil : data_values = nil) by
        (apply Zlength_nil_inv; lia)
  end.
  subst key_values data_values.
  split_pure_spatial.
  - rewrite IntArray.full_empty.
    rewrite IntArray.full_empty.
    Intros.
    Intros.
    repeat rewrite sepcon_emp_equiv.
    repeat rewrite sepcon_emp_logic_equiv'.
    apply dijkstra_index_queue_heap_tail_zero_to_undef_pair.
  - dump_pre_spatial; exact Hempty.
Qed.

Lemma dijkstra_index_queue_zero_seg_to_undef_full :
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

Lemma dijkstra_index_queue_zero_segs_to_undef_full_pair :
  forall key data n,
    IntArray.undef_seg (key + 0 * sizeof(INT)) 0 n **
    IntArray.undef_seg (data + 0 * sizeof(INT)) 0 n |--
    IntArray.undef_full key n **
    IntArray.undef_full data n.
Proof.
  intros key data n.
  apply derivable1_sepcon_mono;
    apply dijkstra_index_queue_zero_seg_to_undef_full.
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

Lemma proof_of_dijkstra_linked_forward_star_index_queue_entail_wit_1 : dijkstra_linked_forward_star_index_queue_entail_wit_1.
Proof.
  right.
  intros.
  replace ((( &( "queue_key" ) ) + (0 * sizeof(INT)))) with ( &( "queue_key" ) ) by lia.
  replace ((( &( "queue_data" ) ) + (0 * sizeof(INT)))) with ( &( "queue_data" ) ) by lia.
  eapply derivable1_trans with (y :=
    (IntArray.undef_seg ( &( "queue_data" ) ) 0 100000) **
    (IntArray.undef_seg ( &( "queue_key" ) ) 0 100000)).
  - apply derivable1_sepcon_mono;
      apply IntArray.undef_full_to_undef_seg.
  - apply derivable1_sepcon_comm.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_index_queue_entail_wit_2 : dijkstra_linked_forward_star_index_queue_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (multiset_insert (list_to_multiset (@nil (Z * Z)))
            (heap_item 0 source_pre))
    (list_to_multiset (@nil (Z * Z)))
    (fun _ : Z => False) dist_init_2.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
    cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
    cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
    cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
    cancel (IntArray.full dist_pre 10 dist_init_2).
    unfold store_heap.
    Exists (@nil Z) (@nil Z).
    rewrite !IntArray.full_empty.
    split_pure_spatial.
    + repeat rewrite sepcon_emp_equiv.
      repeat rewrite sepcon_emp_logic_equiv'.
      change 100000 with heap_capacity.
      apply dijkstra_index_queue_undef_pair_to_heap_tail_zero.
    + split_pures; dump_pre_spatial.
      unfold heap_representation, heap_relation, heap_ordered,
        multiset_size, list_to_multiset, pair_list.
      simpl; repeat split; try lia; try constructor.
      try (intros child Hchild; lia).
      all: lia.
  - split_pures; dump_pre_spatial; auto; try lia.
    + unfold visited_set_empty; tauto.
    + unfold index_queue_push_result; reflexivity.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_index_queue_entail_wit_3 : dijkstra_linked_forward_star_index_queue_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst queue_size.
  replace (0 + 1) with 1 in * by lia.
  pose proof PreH8 as Hinit_dist.
  unfold index_queue_push_result in PreH12.
  subst queue_set_initial_after.
  Exists visited_init dist_init
    (multiset_insert (list_to_multiset (@nil (Z * Z)))
      (heap_item 0 source_pre)).
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
    cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
    cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
    cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
    cancel (IntArray.full dist_pre 10 dist_init).
    subst queue_set_empty.
    cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT)))
      (multiset_insert (list_to_multiset (@nil (Z * Z)))
        (heap_item 0 source_pre)) 1).
  - split_pures; dump_pre_spatial; auto; try lia.
    + unfold dijkstra_heap_loop_state.
      destruct PreH8 as (Hdist_shape & Hdist_safe & _).
      split; [eapply forward_star_model_graph_wf; eauto |].
      split; [exact PreH3 |].
      split; [exact PreH4 |].
      split; [exact Hdist_shape |].
      split; [exact Hdist_safe |].
      unfold heap_queue_items_valid, list_to_multiset, multiset_insert,
          heap_item, item_data, item_key.
      simpl.
      intros item [Hitem | []]; subst item; simpl.
      split; [exact PreH3 | unfold DijkstraGraph.infinity; lia].
    + eapply dijkstra_heap_lfs_initial_to_loop_refines.
      * exact PreH2.
      * exact PreH10.
      * exact Hinit_dist.
      * unfold index_queue_push_result; reflexivity.
      * exact PreH9.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_index_queue_entail_wit_4 : dijkstra_linked_forward_star_index_queue_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists visited_cur_2 dist_cur_2 queue_set_2.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
    cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
    cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
    cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
    cancel (IntArray.full dist_pre 10 dist_cur_2).
    cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) queue_set_2 queue_size).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_index_queue_entail_wit_5 : dijkstra_linked_forward_star_index_queue_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct popped as [pop_key pop_data].
  simpl in *.
  subst key_out_callee_v data_out_callee_v.
  assert (Hpop :
    index_queue_pop_result queue_set_2
      (multiset_remove queue_set_2 (pop_key, pop_data))
      pop_data pop_key).
  {
    unfold index_queue_pop_result.
    exists (pop_key, pop_data).
    split; [unfold heap_item; reflexivity |].
    split; [exact PreH3 | reflexivity].
  }
  pose proof
    (dijkstra_heap_pop_result_bounds
      g_low_level_spec vertex_count_pre source_pre visited_cur_2
      dist_cur_2 queue_set_2
      (multiset_remove queue_set_2 (pop_key, pop_data))
      pop_data pop_key PreH8 PreH11 Hpop)
    as (Hpop_storage & Hpop_vertex_bounds & Hpop_distance_bounds).
  pose proof
    (dijkstra_heap_loop_refines_pop
      g_low_level_spec source_pre
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_cur_2 dist_cur_2 queue_set_2
      (multiset_remove queue_set_2 (pop_key, pop_data))
      pop_data pop_key X_low_level_spec Hpop PreH11 PreH12)
    as Hafter_pop.
  Exists (multiset_remove queue_set_2 (pop_key, pop_data))
    visited_cur_2 dist_cur_2 queue_set_2.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
    cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
    cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
    cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
    cancel (IntArray.full dist_pre 10 dist_cur_2).
    cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT)))
      (multiset_remove queue_set_2 (pop_key, pop_data))
      (queue_size - 1)).
  - split_pures; dump_pre_spatial; auto; try lia.
    + unfold storage_index, DijkstraGraph.max_vertices in *; lia.
    + unfold DijkstraGraph.infinity in *; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_index_queue_entail_wit_6 : dijkstra_linked_forward_star_index_queue_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (forward_star_model_head_case_0
      g_low_level_spec vertex_count_pre edge_count_pre
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      cur_vertex PreH6 PreH18 ltac:(lia)) as Hhead.
  assert (Hcur_valid : vertex_valid g_low_level_spec cur_vertex)
    by (unfold vertex_valid, DijkstraGraph.vertex_valid;
        unfold graph_has_size in PreH6; lia).
  assert (Hdist : dist_cell dist_cur cur_vertex = cur_distance).
  {
    rewrite PreH1.
    apply dist_cell_Znth_0; [unfold dijkstra_heap_loop_state in PreH9; tauto |].
    exact PreH10.
  }
  assert (Hedge_nonneg : -1 <= Znth cur_vertex head_values_low_level_spec 0)
    by (destruct Hhead as [Hhead_nil | Hhead_edge];
        [rewrite Hhead_nil | unfold edge_index in Hhead_edge]; lia).
  pose (visited_edge_cur := fun v : Z => visited_cur_2 v \/ v = cur_vertex).
  assert (Hvisit_add : visited_set_add visited_cur_2 cur_vertex visited_edge_cur)
    by (unfold visited_set_add, visited_edge_cur; tauto).
  pose proof
    (dijkstra_heap_loop_state_pop
      g_low_level_spec source_pre visited_cur_2 dist_cur
      queue_set_before queue_set_2 cur_vertex cur_distance PreH9 PreH16)
    as Hloop_after_pop.
  assert (Hedge_state :
    dijkstra_heap_edge_loop_state g_low_level_spec source_pre
      visited_edge_cur cur_vertex cur_distance
      (Znth cur_vertex head_values_low_level_spec 0) dist_cur queue_set_2).
  {
    unfold dijkstra_heap_edge_loop_state.
    split; [exact Hloop_after_pop |].
    split; [exact Hcur_valid |].
    split; [exact Hdist | exact Hedge_nonneg].
  }
  assert (Hedge_refines :
    dijkstra_heap_edge_loop_refines g_low_level_spec source_pre cur_vertex
      cur_distance (Znth cur_vertex head_values_low_level_spec 0)
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_edge_cur dist_cur queue_set_2 X_low_level_spec).
  {
    eapply dijkstra_heap_after_pop_refines_equal_to_edge_loop; eauto.
    eapply forward_star_head_0_nil_or_chain; eauto.
  }
  destruct Hhead as [Hhead_nil | Hhead_edge].
  - Left.
    Exists dist_cur queue_set_2 visited_cur_2 visited_edge_cur.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (IntArray.full dist_pre 10 dist_cur).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) queue_set_2 queue_size).
    + split_pures; dump_pre_spatial; auto; try lia.
  - Right.
    Exists dist_cur queue_set_2 visited_cur_2 visited_edge_cur.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (IntArray.full dist_pre 10 dist_cur).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) queue_set_2 queue_size).
    + split_pures; dump_pre_spatial; auto; try lia.
      * unfold edge_index in Hhead_edge; lia.
      * unfold edge_index in Hhead_edge; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_index_queue_entail_wit_7 : dijkstra_linked_forward_star_index_queue_entail_wit_7.
Proof.
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
  Exists dist_edge_2 queue_set_2 visited_cur_2 visited_edge_2.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
    cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
    cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
    cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
    cancel (IntArray.full dist_pre 10 dist_edge_2).
    cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) queue_set_2 queue_size).
  - split_pures; dump_pre_spatial; auto; try reflexivity; try lia;
    try (unfold storage_index, DijkstraGraph.max_vertices in Hto_storage; lia);
    try (unfold DijkstraGraph.infinity in Hweight_bounds; lia).
Qed.

Lemma proof_of_dijkstra_linked_forward_star_index_queue_entail_wit_8 : dijkstra_linked_forward_star_index_queue_entail_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply (store_heap_size_eq (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT)))
    queue_set queue_size).
  Intros_p Hqueue_size_eq.
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
    - unfold dijkstra_heap_edge_loop_state in PreH25.
      destruct PreH25 as [Hloop _].
      unfold dijkstra_heap_loop_state in Hloop.
      tauto.
    - exact Hneighbor_storage.
  }
  assert (Hdist_neighbor_safe :
    0 <= dist_cell dist_edge neighbor <= DijkstraGraph.infinity).
  {
    unfold dijkstra_heap_edge_loop_state in PreH25.
    destruct PreH25 as [Hloop _].
    unfold dijkstra_heap_loop_state in Hloop.
    destruct Hloop as (_ & _ & _ & _ & Hsafe & _).
    apply Hsafe.
    exact Hneighbor_storage.
  }
  assert (Hcandidate_bounds :
    0 <= cur_distance + edge_weight0 < DijkstraGraph.infinity)
    by (rewrite <- Hdist_cell_neighbor in PreH1; lia).
  assert (Hrelax_cell :
    cur_distance + edge_weight0 < dist_cell dist_edge neighbor)
    by (rewrite Hdist_cell_neighbor; exact PreH1).
  assert (Hedge_state_after :
    dijkstra_heap_edge_loop_state g_low_level_spec source_pre visited_edge_2
      cur_vertex cur_distance edge
      (replace_Znth neighbor (cur_distance + edge_weight0) dist_edge)
      queue_set).
	  {
	    eapply (dijkstra_heap_edge_loop_state_relax_update
	      g_low_level_spec vertex_count_pre source_pre visited_edge_2
	      cur_vertex cur_distance edge neighbor edge_weight0
	      (cur_distance + edge_weight0) dist_edge queue_set).
	    - exact PreH8.
	    - exact Hneighbor_valid.
	    - exact Hneighbor_storage.
	    - exact Hcandidate_bounds.
	    - lia.
	    - reflexivity.
	    - exact Hrelax_cell.
	    - exact PreH25.
	  }
  assert (Hafter_relax :
    dijkstra_heap_after_relax_refines g_low_level_spec source_pre
      cur_vertex cur_distance edge neighbor (cur_distance + edge_weight0)
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_edge_2
      (replace_Znth neighbor (cur_distance + edge_weight0) dist_edge)
      queue_set X_low_level_spec).
  {
    eapply dijkstra_heap_edge_loop_refines_relax_to_after_relax.
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
  assert (Hpush :
    index_queue_push_result queue_set
      (multiset_insert queue_set
        (heap_item (cur_distance + edge_weight0) neighbor))
      neighbor (cur_distance + edge_weight0))
    by (unfold index_queue_push_result; reflexivity).
  assert (Hqueue_room : queue_size < 100000).
  {
    pose proof PreH26 as Hrefines_for_cap.
    unfold dijkstra_heap_edge_loop_refines in Hrefines_for_cap.
    destruct Hrefines_for_cap as (_ & Hcap & _).
    assert (Hwf : DijkstraGraph.graph_wf g_low_level_spec)
      by (unfold dijkstra_heap_edge_loop_state,
            dijkstra_heap_loop_state in PreH25; tauto).
    assert (Hcur_valid : vertex_valid g_low_level_spec cur_vertex)
      by (unfold dijkstra_heap_edge_loop_state in PreH25; tauto).
    pose proof
      (forward_star_model_edge_safe _ _ _ _ _ _ PreH27)
      as (_ & _ & Hnext_len & _).
    assert (Hedge_next_bound :
      0 <= edge < Zlength next_values_low_level_spec)
      by (rewrite Hnext_len; lia).
    pose proof
      (heap_queue_edge_capacity_state_has_push_room
        g_low_level_spec visited_edge_2 cur_vertex edge
        head_values_low_level_spec to_values_low_level_spec
        next_values_low_level_spec queue_set neighbor
        Hwf Hcur_valid Hneighbor_valid PreH17 Hedge_next_bound Hcap)
	      as Hroom.
    rewrite Hqueue_size_eq in Hroom.
    unfold DijkstraGraph.max_vertices in Hroom.
    lia.
  }
  Exists (multiset_insert queue_set
          (heap_item (cur_distance + edge_weight0) neighbor))
    (replace_Znth neighbor (cur_distance + edge_weight0) dist_edge)
    queue_set visited_cur_2 visited_edge_2.
  split_pure_spatial.
  - cancel (IntArray.full dist_pre 10
      (replace_Znth neighbor (cur_distance + edge_weight0) dist_edge)).
    cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
    cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
    cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
    cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
    cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) queue_set queue_size).
  - split_pures; dump_pre_spatial; auto; try lia;
      try exact PreH24; try exact Hedge_state_after;
      try exact Hafter_relax; try exact Hpush; try exact PreH27.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_index_queue_entail_wit_9_1 : dijkstra_linked_forward_star_index_queue_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold index_queue_push_result in PreH28.
  subst queue_set_after.
  assert (Hneighbor_valid : vertex_valid g_low_level_spec neighbor).
  {
    unfold vertex_valid, DijkstraGraph.vertex_valid.
    unfold graph_has_size in PreH6; lia.
  }
  pose proof
    (dijkstra_heap_edge_loop_to_loop_state
      g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge
      dist_after queue_set_before PreH26) as Hloop_before.
  assert (Hcandidate_bounds :
    0 <= candidate <= DijkstraGraph.infinity)
    by (unfold DijkstraGraph.infinity; lia).
  assert (Hloop_push :
    dijkstra_heap_loop_state g_low_level_spec source_pre
      visited_edge_2 dist_after
      (multiset_insert queue_set_before (heap_item candidate neighbor))).
  {
    eapply dijkstra_heap_loop_state_push; eauto.
    unfold index_queue_push_result; reflexivity.
  }
  unfold dijkstra_heap_edge_loop_state in PreH26.
  destruct PreH26 as (_ & Hcur_valid & Hdist & Hedge_nonneg_old).
  assert (Hedge_push :
    dijkstra_heap_edge_loop_state g_low_level_spec source_pre
      visited_edge_2 cur_vertex cur_distance edge dist_after
      (multiset_insert queue_set_before (heap_item candidate neighbor))).
  {
    unfold dijkstra_heap_edge_loop_state.
    split; [exact Hloop_push |].
    split; [exact Hcur_valid |].
    split; [exact Hdist | exact Hedge_nonneg_old].
  }
  pose proof
    (forward_star_model_next_case_0
      g_low_level_spec edge_count_pre head_values_low_level_spec
      to_values_low_level_spec weight_values_low_level_spec
      next_values_low_level_spec edge PreH29
      ltac:(unfold edge_index; lia)) as Hnext.
  assert (Hnext_nonneg : -1 <= Znth edge next_values_low_level_spec 0)
    by (destruct Hnext as [Hnext_nil | Hnext_edge];
        [rewrite Hnext_nil | unfold edge_index in Hnext_edge]; lia).
  assert (Hedge_next :
    dijkstra_heap_edge_loop_state g_low_level_spec source_pre
      visited_edge_2 cur_vertex cur_distance
      (Znth edge next_values_low_level_spec 0) dist_after
      (multiset_insert queue_set_before (heap_item candidate neighbor))).
  {
    apply (dijkstra_heap_edge_loop_next
      g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge);
      auto.
  }
  assert (Hrefines_next :
    dijkstra_heap_edge_loop_refines g_low_level_spec source_pre cur_vertex
      cur_distance (Znth edge next_values_low_level_spec 0)
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_edge_2 dist_after
      (multiset_insert queue_set_before (heap_item candidate neighbor))
      X_low_level_spec).
  {
    eapply dijkstra_heap_after_relax_refines_push_to_edge_loop.
    - exact PreH29.
    - exact Hcur_valid.
    - unfold edge_index; lia.
    - exact PreH15.
    - unfold index_queue_push_result; reflexivity.
    - exact PreH27.
  }
  destruct Hnext as [Hnext_nil | Hnext_edge].
  - Left.
    Exists dist_after
      (multiset_insert queue_set_before (heap_item candidate neighbor))
      visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (IntArray.full dist_pre 10 dist_after).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT)))
        (multiset_insert queue_set_before (heap_item candidate neighbor))
        (queue_size + 1)).
    + split_pures; dump_pre_spatial; auto; try lia;
        try (unfold heap_capacity; lia);
        try exact Hedge_next; try exact Hrefines_next; try exact Hnext_nil.
  - Right.
    Exists dist_after
      (multiset_insert queue_set_before (heap_item candidate neighbor))
      visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (IntArray.full dist_pre 10 dist_after).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT)))
        (multiset_insert queue_set_before (heap_item candidate neighbor))
        (queue_size + 1)).
    + split_pures; dump_pre_spatial; auto; try lia;
        try (unfold heap_capacity; lia);
        try exact Hedge_next; try exact Hrefines_next.
      * unfold edge_index in Hnext_edge; lia.
      * unfold edge_index in Hnext_edge; lia.
Qed. 

Lemma proof_of_dijkstra_linked_forward_star_index_queue_entail_wit_9_2 : dijkstra_linked_forward_star_index_queue_entail_wit_9_2.
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
    dijkstra_heap_edge_loop_state g_low_level_spec source_pre visited_edge_2
      cur_vertex cur_distance (Znth edge next_values_low_level_spec 0)
      dist_edge_2 queue_set_2).
  {
    apply (dijkstra_heap_edge_loop_next
      g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge);
      auto.
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
    - unfold dijkstra_heap_edge_loop_state in PreH25.
      destruct PreH25 as [Hloop _].
      unfold dijkstra_heap_loop_state in Hloop.
      tauto.
    - unfold storage_index, DijkstraGraph.max_vertices; lia.
  }
  assert (Hrefines_next :
    dijkstra_heap_edge_loop_refines g_low_level_spec source_pre cur_vertex
      cur_distance (Znth edge next_values_low_level_spec 0)
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_edge_2 dist_edge_2 queue_set_2 X_low_level_spec).
  {
	    eapply dijkstra_heap_edge_loop_refines_no_relax_to_next.
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
    Exists dist_edge_2 queue_set_2 visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (IntArray.full dist_pre 10 dist_edge_2).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) queue_set_2 queue_size).
    + split_pures; dump_pre_spatial; auto; try lia;
        try exact Hedge_next; try exact Hrefines_next; try exact Hnext_nil.
  - Right.
    Exists dist_edge_2 queue_set_2 visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (IntArray.full dist_pre 10 dist_edge_2).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) queue_set_2 queue_size).
    + split_pures; dump_pre_spatial; auto; try lia;
        try exact Hedge_next; try exact Hrefines_next.
      * unfold edge_index in Hnext_edge; lia.
      * unfold edge_index in Hnext_edge; lia.
Qed. 

Lemma proof_of_dijkstra_linked_forward_star_index_queue_entail_wit_9_3 : dijkstra_linked_forward_star_index_queue_entail_wit_9_3.
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
    dijkstra_heap_edge_loop_state g_low_level_spec source_pre visited_edge_2
      cur_vertex cur_distance (Znth edge next_values_low_level_spec 0)
      dist_edge_2 queue_set_2).
  {
    apply (dijkstra_heap_edge_loop_next
      g_low_level_spec source_pre visited_edge_2 cur_vertex cur_distance edge);
      auto.
  }
  assert (Hneighbor_valid : vertex_valid g_low_level_spec neighbor).
  {
    unfold vertex_valid, DijkstraGraph.vertex_valid.
    unfold graph_has_size in PreH7; lia.
  }
  assert (Hrefines_next :
    dijkstra_heap_edge_loop_refines g_low_level_spec source_pre cur_vertex
      cur_distance (Znth edge next_values_low_level_spec 0)
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_edge_2 dist_edge_2 queue_set_2 X_low_level_spec).
  {
	    eapply dijkstra_heap_edge_loop_refines_no_relax_to_next.
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
    Exists dist_edge_2 queue_set_2 visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (IntArray.full dist_pre 10 dist_edge_2).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) queue_set_2 queue_size).
    + split_pures; dump_pre_spatial; auto; try lia.
  - Right.
    Exists dist_edge_2 queue_set_2 visited_cur_2 visited_edge_2.
    split_pure_spatial.
    + cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
      cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
      cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
      cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
      cancel (IntArray.full dist_pre 10 dist_edge_2).
      cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) queue_set_2 queue_size).
    + split_pures; dump_pre_spatial; auto; try lia.
      * unfold edge_index in Hnext_edge; lia.
      * unfold edge_index in Hnext_edge; lia.
Qed. 

Lemma proof_of_dijkstra_linked_forward_star_index_queue_entail_wit_10_1 : dijkstra_linked_forward_star_index_queue_entail_wit_10_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hloop_state :
    dijkstra_heap_loop_state g_low_level_spec source_pre
      visited_edge dist_edge queue_set_2).
  {
    apply (dijkstra_heap_edge_loop_to_loop_state
      g_low_level_spec source_pre visited_edge cur_vertex cur_distance edge);
      auto.
  }
  assert (Hrefines_loop :
    dijkstra_heap_loop_refines g_low_level_spec source_pre
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_edge dist_edge queue_set_2 X_low_level_spec).
  {
    eapply dijkstra_heap_edge_loop_refines_break_to_loop; eauto.
  }
  Exists visited_edge dist_edge queue_set_2.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
    cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
    cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
    cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
    cancel (IntArray.full dist_pre 10 dist_edge).
    cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) queue_set_2 queue_size).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed. 

Lemma proof_of_dijkstra_linked_forward_star_index_queue_entail_wit_10_2 : dijkstra_linked_forward_star_index_queue_entail_wit_10_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hcur_valid : vertex_valid g_low_level_spec cur_vertex).
  {
    unfold vertex_valid, DijkstraGraph.vertex_valid.
    unfold graph_has_size in PreH6; lia.
  }
  assert (Hdist_cell_cur :
    dist_cell dist_cur_2 cur_vertex = Znth cur_vertex dist_cur_2 0).
  {
    apply (dist_cell_Znth_0 dist_cur_2 cur_vertex).
    - unfold dijkstra_heap_loop_state in PreH9.
      tauto.
    - exact PreH10.
  }
  assert (Hdist_neq :
    cur_distance <> dist_cell dist_cur_2 cur_vertex).
  {
    rewrite Hdist_cell_cur.
    exact PreH1.
  }
  pose proof
    (dijkstra_heap_loop_state_pop
      g_low_level_spec source_pre visited_cur_2 dist_cur_2
      queue_set_before queue_set_2 cur_vertex cur_distance PreH9 PreH16)
    as Hloop_after_pop.
  assert (Hrefines_loop :
    dijkstra_heap_loop_refines g_low_level_spec source_pre
      head_values_low_level_spec to_values_low_level_spec
      weight_values_low_level_spec next_values_low_level_spec
      visited_cur_2 dist_cur_2 queue_set_2 X_low_level_spec).
  {
    eapply dijkstra_heap_after_pop_refines_not_equal_to_loop; eauto.
  }
  Exists visited_cur_2 dist_cur_2 queue_set_2.
  split_pure_spatial.
  - cancel (IntArray.full head_pre vertex_count_pre head_values_low_level_spec).
    cancel (IntArray.full to_pre edge_count_pre to_values_low_level_spec).
    cancel (IntArray.full weight_pre edge_count_pre weight_values_low_level_spec).
    cancel (IntArray.full next_pre edge_count_pre next_values_low_level_spec).
    cancel (IntArray.full dist_pre 10 dist_cur_2).
    cancel (store_heap (( &( "queue_key" ) ) + (0 * sizeof(INT))) (( &( "queue_data" ) ) + (0 * sizeof(INT))) queue_set_2 queue_size).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed. 

Lemma proof_of_dijkstra_linked_forward_star_index_queue_entail_wit_11 : dijkstra_linked_forward_star_index_queue_entail_wit_11.
Proof.
  right.
  LLM_pre_process ltac:(int_auto).
  subst queue_size.
  sep_apply_l_atomic (dijkstra_index_queue_store_heap_zero_to_emp
    (( &( "queue_key" ) ) + (0 * sizeof(INT)))
    (( &( "queue_data" ) ) + (0 * sizeof(INT)))
    queue_set).
  Intros.
  assert (Hsafe_return :
    safeExec (graph_state_model g_low_level_spec visited_cur dist_cur)
      (return tt) X_low_level_spec).
  {
    eapply dijkstra_heap_loop_refines_empty_to_return; eauto.
  }
  Exists visited_cur queue_set.
  split_pure_spatial.
  - repeat rewrite sepcon_emp_equiv.
    repeat rewrite sepcon_emp_logic_equiv'.
    apply (dijkstra_index_queue_zero_segs_to_undef_full_pair
      ( &( "queue_key" ) ) ( &( "queue_data" ) ) 100000).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_index_queue_partial_solve_wit_1_pure_split_goal_1 : dijkstra_linked_forward_star_index_queue_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (graph_has_size_vertex_valid_bounds
      g_low_level_spec vertex_count_pre source_pre PreH7 PreH8)
    as ((Hvertex_count_pos & _) & _).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_index_queue_partial_solve_wit_1_pure_split_goal_2 : dijkstra_linked_forward_star_index_queue_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (graph_has_size_bounds g_low_level_spec vertex_count_pre PreH7)
    as Hvertex_count_bounds.
  dump_pre_spatial.
  unfold DijkstraGraph.max_vertices in *; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_index_queue_partial_solve_wit_1_pure_split_goal_3 : dijkstra_linked_forward_star_index_queue_partial_solve_wit_1_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (graph_has_size_vertex_valid_bounds
      g_low_level_spec vertex_count_pre source_pre PreH7 PreH8)
    as (_ & Hsource_bounds).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_index_queue_partial_solve_wit_1_pure_split_goal_4 : dijkstra_linked_forward_star_index_queue_partial_solve_wit_1_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (graph_has_size_vertex_valid_bounds
      g_low_level_spec vertex_count_pre source_pre PreH7 PreH8)
    as (_ & Hsource_bounds).
  dump_pre_spatial; lia.
Qed.

Lemma proof_of_dijkstra_linked_forward_star_index_queue_partial_solve_wit_1_pure : dijkstra_linked_forward_star_index_queue_partial_solve_wit_1_pure.
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

Lemma proof_of_dijkstra_linked_forward_star_index_queue_derive_high_level_spec_by_low_level_spec : dijkstra_linked_forward_star_index_queue_derive_high_level_spec_by_low_level_spec.
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
      (dijkstra_heap_lfs_program source_pre
        head_values_high_level_spec to_values_high_level_spec
        weight_values_high_level_spec next_values_high_level_spec)).
  assert (Hsafe_first :
    safeExec (eq (initial_state source_pre))
      (dijkstra_heap_lfs_program source_pre
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
    dijkstra_heap_lfs_initial_refines g_high_level_spec source_pre
      head_values_high_level_spec to_values_high_level_spec
      weight_values_high_level_spec next_values_high_level_spec
      X_low_level_spec).
	  {
	    unfold dijkstra_heap_lfs_initial_refines.
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
      eapply (dijkstra_heap_lfs_program_correct
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
