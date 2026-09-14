Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Logic.ClassicalDescription.
From ListLib.Base Require Import Positional.
Require Import ListLib.General.Length.
From SimpleC.SL Require Import IntLib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import SetsClass.SetsClass.
From AUXLib Require Import ListLib.
From SumLib Require Import ZRange.
From MaxMinLib Require Import MaxMin Interface.
Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.Zweight.
Require Import GraphLib.subgraph.subgraph.
From GraphLib.undirected Require Import tree.
From GraphLib.examples Require Import prim.
From MonadLib.StateRelMonad Require Import StateRelHoare.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelMonad.
Require Algorithms.Prim.Prim.
From SimpleC.EE.LLM_bench.Algorithms.Prim Require Export prim_forward_star_lib.
Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_lib.

Import ListNotations.
Import MonadNotation.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Definition selected_edges_range_state := parent_edges_range_state.
Definition selected_edges_exact_state := parent_edges_exact_state.
Definition selected_edges_match_state := parent_edges_match_state.
Definition return_is_mst (g rg : G) : Prop := is_mst g rg.

(** * Priority-queue decrease-key interface for Prim

    The C implementation now uses the shared decrease-key heap.  At the
    algorithm layer the heap is represented by a partial map from vertex
    ([data]) to current priority ([key]).
 *)

Definition partial_map_empty : partial_map := fun _ => None.

Lemma partial_map_empty_absent :
  forall data_x,
    partial_map_absent partial_map_empty data_x.
Proof.
  intros data_x.
  unfold partial_map_absent, partial_map_get, partial_map_empty.
  reflexivity.
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

Lemma partial_map_update_or_add_present_other_rewrite :
  forall M data_x key_x query old_key new_key,
    query <> data_x ->
    partial_map_present M query old_key ->
    new_key = old_key ->
    partial_map_present
      (partial_map_update_or_add M data_x key_x) query new_key.
Proof.
  intros M data_x key_x query old_key new_key Hneq Hpresent Hkey.
  subst new_key.
  apply partial_map_update_or_add_present_other; assumption.
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

Lemma Zlength_repeat_Z_nonneg :
  forall A (x : A) n,
    0 <= n ->
    Zlength (repeat_Z x n) = n.
Proof.
  intros A x n Hn.
  unfold repeat_Z.
  rewrite Zlength_correct, repeat_length.
  lia.
Qed.

Lemma heap_pos_consistent_empty :
  forall data_bound,
    0 <= data_bound ->
    heap_pos_consistent [] (repeat_Z absent data_bound) data_bound 0.
Proof.
  intros data_bound Hbound.
  unfold heap_pos_consistent.
  split; [assumption |].
  split.
  - apply Zlength_repeat_Z_nonneg; assumption.
  - split.
    + unfold heap_data_valid. intros index Hindex. lia.
    + split.
      * unfold heap_pos_backlinks. intros index Hindex. lia.
      * unfold heap_pos_forward_links.
        intros data_x Hdata_x.
        left.
        unfold repeat_Z.
        rewrite Znth_repeat_lt by
          (rewrite Z2Nat.id by lia; lia).
        reflexivity.
Qed.

Lemma heap_representation_empty :
  forall data_bound,
    0 <= data_bound ->
    heap_representation
      partial_map_empty [] [] (repeat_Z absent data_bound) data_bound 0.
Proof.
  intros data_bound Hbound.
  unfold heap_representation.
  split; [lia |].
  split; [unfold heap_capacity; lia |].
  split.
  - unfold heap_map_relation.
    split; [reflexivity |].
    split; [reflexivity |].
    split.
    + unfold heap_data_unique.
      intros i j Hi _ _.
      destruct Hi as [Hlo Hi].
      exfalso; lia.
    + split.
      * intros index Hindex. lia.
      * intros data_x key_x Hpresent.
        unfold partial_map_present, partial_map_get, partial_map_empty in Hpresent.
        discriminate.
  - split.
    + unfold heap_ordered. intros child Hchild. lia.
    + apply heap_pos_consistent_empty; assumption.
Qed.

Lemma store_heap_empty_from_undef :
  forall key data pos data_bound capacity,
    0 <= data_bound ->
    0 <= capacity ->
    IntArray.undef_seg key 0 capacity **
    IntArray.undef_seg data 0 capacity **
    IntArray.full pos data_bound (repeat_Z absent data_bound)
    |-- store_heap key data pos data_bound capacity partial_map_empty 0.
Proof.
  intros key data pos data_bound capacity Hbound Hcapacity.
  unfold store_heap.
  Exists (@nil Z) (@nil Z) (repeat_Z absent data_bound).
  split_pure_spatial.
  - rewrite (IntArray.full_empty key 0).
    rewrite (IntArray.full_empty data 0).
    entailer!.
  - apply derivable1s_coq_prop_r.
    apply heap_representation_empty; assumption.
Qed.

Definition prim_queue_map_initial
    (before after : partial_map) (vertex key : Z) : Prop :=
  before = partial_map_empty /\
  after = partial_map_add before vertex key.

Definition prim_queue_map_pop
    (before after : partial_map) (vertex key : Z) : Prop :=
  partial_map_minimum before (heap_item key vertex) /\
  after = partial_map_remove before vertex.

Definition prim_queue_map_update_or_push
    (before after : partial_map)
    (size_before size_after vertex key : Z) : Prop :=
  partial_map_update_or_add_size before size_before size_after vertex key /\
  after = partial_map_update_or_add before vertex key.

Definition prim_heap_map_matches_state
    (g : G) (s : St)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (M : partial_map) : Prop :=
  (forall vertex key,
      partial_map_present M vertex key ->
      candidate_vertex g s lowcost edge_parent inf vertex /\
      key = Znth vertex lowcost 0) /\
  (forall vertex,
      candidate_vertex g s lowcost edge_parent inf vertex ->
      partial_map_present M vertex (Znth vertex lowcost 0)).

Definition candidate_vertex_by
    (g : G) (s : St)
    (edge_for_vertex : V -> E -> Prop)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (v : V) : Prop :=
  In v (graph_vertices g) /\
  ~ vvalid s.(Prim.graph_in_state) v /\
  Znth v edge_parent 0 <> -1 /\
  0 <= Znth v edge_parent 0 < 2 * graph_edge_count g /\
  Znth v lowcost 0 < inf /\
  min_object_of_subset Z_op_le
    (edge_for_vertex v) (weight g) (Znth v edge_parent 0 / 2) /\
  weight g (Znth v edge_parent 0 / 2) = Some (Znth v lowcost 0).

Definition prim_heap_map_matches_state_by
    (g : G) (s : St) (edge_for_vertex : V -> E -> Prop)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (M : partial_map) : Prop :=
  (forall vertex key,
      partial_map_present M vertex key ->
      candidate_vertex_by g s edge_for_vertex lowcost edge_parent inf vertex /\
      key = Znth vertex lowcost 0) /\
  (forall vertex,
      candidate_vertex_by g s edge_for_vertex lowcost edge_parent inf vertex ->
      partial_map_present M vertex (Znth vertex lowcost 0)).

Definition prim_heap_map_pop_selects_min_vertex
    (g : G) (s : St) (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (M : partial_map) (key vertex : Z) : Prop :=
  partial_map_minimum M (heap_item key vertex) /\
  prim_heap_map_matches_state g s lowcost edge_parent inf M /\
  key = Znth vertex lowcost 0 /\
  min_vertex_in_range g s (Zlength lowcost) inf vertex lowcost edge_parent.

Definition partial_map_update_one_directed_edge
    (g : G) (s_next : St)
    (to_new : list DE) (wt_new : list Z)
    (lowcost_in : list Z) (de : DE)
    (M_in M_out : partial_map) : Prop :=
  let v := Znth de to_new 0 in
  let w := Znth de wt_new 0 in
  (is_cut_edge_to_vertex g s_next v (de / 2) /\
   w < Znth v lowcost_in 0 /\
   M_out = partial_map_update_or_add M_in v w) \/
  ((~ is_cut_edge_to_vertex g s_next v (de / 2) \/
    Znth v lowcost_in 0 <= w) /\
   M_out = M_in).

Inductive scan_directed_edges_partial_map_update
    (g : G) (s_next : St)
    (to_new : list DE) (wt_new : list Z) :
    list DE ->
    list Z -> list DE -> partial_map ->
    list Z -> list DE -> partial_map -> Prop :=
| scan_directed_edges_partial_map_update_nil :
    forall lowcost edge_parent M,
      scan_directed_edges_partial_map_update
        g s_next to_new wt_new nil
        lowcost edge_parent M
        lowcost edge_parent M
| scan_directed_edges_partial_map_update_cons :
    forall de rest
           lowcost0 edge_parent0 M0
           lowcost1 edge_parent1 M1
           lowcost2 edge_parent2 M2,
      scan_one_directed_edge_update
        g s_next to_new wt_new
        lowcost0 edge_parent0 de
        lowcost1 edge_parent1 ->
      partial_map_update_one_directed_edge
        g s_next to_new wt_new lowcost0 de M0 M1 ->
      scan_directed_edges_partial_map_update
        g s_next to_new wt_new rest
        lowcost1 edge_parent1 M1
        lowcost2 edge_parent2 M2 ->
      scan_directed_edges_partial_map_update
        g s_next to_new wt_new (de :: rest)
        lowcost0 edge_parent0 M0
        lowcost2 edge_parent2 M2.

Definition scan_minIndex_adjacency_map_prefix_update
    (g : G) (s_next : St)
    (from_new first link to_new : list DE) (wt_new : list Z)
    (minIndex : V) (current_e : DE)
    (lowcost_before : list Z) (edge_parent_before : list DE)
    (M_before : partial_map)
    (lowcost_current : list Z) (edge_parent_current : list DE)
    (M_current : partial_map) : Prop :=
  exists edge_for_base scanned_edges remaining_edges,
    is_first_link_chain link first minIndex (scanned_edges ++ remaining_edges) /\
    is_link_chain link current_e remaining_edges /\
    Permutation (scanned_edges ++ remaining_edges)
      (vertex_directed_edges g from_new minIndex) /\
    scan_directed_edges_partial_map_update
      g s_next to_new wt_new scanned_edges
      lowcost_before edge_parent_before M_before
      lowcost_current edge_parent_current M_current /\
    lowcost_parent_match_by
      g (fun v => ~ vvalid s_next.(Prim.graph_in_state) v)
      (add_scanned_edges_for_vertex g s_next to_new edge_for_base scanned_edges)
      lowcost_current edge_parent_current 1000000000 /\
    prim_heap_map_matches_state_by
      g s_next
      (add_scanned_edges_for_vertex g s_next to_new edge_for_base scanned_edges)
      lowcost_current edge_parent_current 1000000000 M_current /\
    (forall v e,
      ~ vvalid s_next.(Prim.graph_in_state) v ->
      add_vertex_directed_edges_for_vertex
        g s_next from_new to_new minIndex edge_for_base v e <->
      is_cut_edge_to_vertex g s_next v e).

Definition scan_minIndex_adjacency_map_update
    (g : G) (s_next : St)
    (from_new first link to_new : list DE) (wt_new : list Z)
    (minIndex : V)
    (lowcost_before : list Z) (edge_parent_before : list DE)
    (M_before : partial_map)
    (lowcost_after : list Z) (edge_parent_after : list DE)
    (M_after : partial_map) : Prop :=
  scan_minIndex_adjacency_update
    g s_next from_new first link to_new wt_new minIndex
    lowcost_before edge_parent_before lowcost_after edge_parent_after /\
  prim_heap_map_matches_state
    g s_next lowcost_after edge_parent_after 1000000000 M_after.

Definition prim_heap_loop_state
    (g : G) (src : V) (chosen : Z) (s : St)
    (lowcost visited edge_parent : list Z) (M : partial_map)
    (X : unit -> St -> Prop) : Prop :=
  (chosen = 0 /\
   s = initSt g src /\
   lowcost =
     replace_Znth src 0
       (repeat 1000000000 (Z.to_nat (Zlength lowcost))) /\
   visited = repeat 0 (Z.to_nat (Zlength visited)) /\
   edge_parent = repeat (-1) (Z.to_nat (Zlength edge_parent)) /\
   M = partial_map_add partial_map_empty src 0 /\
   safeExec (initStPred g src) (Prim2 g) X) \/
  (1 <= chosen /\
   growing_subgraph_state g s /\
   visited_matches_state g s visited /\
   state_vertex_count s = chosen /\
   selected_edges_match_state g src s edge_parent /\
   lowcost_parent_match g s lowcost edge_parent 1000000000 /\
   prim_heap_map_matches_state g s lowcost edge_parent 1000000000 M /\
   safeExec (prim_state_is s) (Prim2_loop g (chosen - 1)) X).

Definition prim_heap_after_pop_state
    (g : G) (src : V) (chosen : Z) (s : St)
    (lowcost visited edge_parent : list Z)
    (M_before M_after : partial_map) (minIndex minCost : Z)
    (X : unit -> St -> Prop) : Prop :=
  prim_heap_loop_state g src chosen s lowcost visited edge_parent M_before X /\
  prim_queue_map_pop M_before M_after minIndex minCost /\
  ((chosen = 0 /\ minIndex = src /\ minCost = 0 /\ s = initSt g src) \/
   (1 <= chosen /\
    prim_heap_map_pop_selects_min_vertex
      g s lowcost edge_parent 1000000000 M_before minCost minIndex)).

Definition prim_heap_scan_state
    (g : G) (src : V) (chosen : Z) (s_before s_after : St)
    (from_new first link to_new weight_new : list Z)
    (lowcost_before visited_after edge_parent_before : list Z)
    (lowcost_current edge_parent_current : list Z)
    (current_e minIndex minCost : Z)
    (M_before : partial_map)
    (lowcost_out edge_parent_out : list Z) (M_current : partial_map)
    (X : unit -> St -> Prop) : Prop :=
  1 <= chosen /\
  growing_subgraph_state g s_after /\
  visited_matches_state g s_after visited_after /\
  state_vertex_count s_after = chosen /\
  selected_edges_match_state g src s_after edge_parent_before /\
  scan_minIndex_adjacency_map_prefix_update
    g s_after from_new first link to_new weight_new minIndex current_e
    lowcost_before edge_parent_before M_before
    lowcost_current edge_parent_current M_current /\
  lowcost_out = lowcost_current /\
  edge_parent_out = edge_parent_current /\
  safeExec (prim_state_is s_after) (Prim2_loop g (chosen - 1)) X.

Definition prim_heap_done_state
    (g : G) (src : V) (s : St)
    (lowcost visited edge_parent : list Z) (M : partial_map)
    (X : unit -> St -> Prop) : Prop :=
  growing_subgraph_state g s /\
  visited_matches_state g s visited /\
  state_vertex_count s = Zlength lowcost /\
  selected_edges_match_state g src s edge_parent /\
  lowcost_parent_match g s lowcost edge_parent 1000000000 /\
  prim_heap_map_matches_state g s lowcost edge_parent 1000000000 M /\
  safeExec (prim_state_is s) (return tt) X.

Lemma add_edge_graph_gvalid_any :
  forall g u v e,
    gvalid g ->
    vvalid g u ->
    vvalid g v ->
    ~ evalid g e ->
    gvalid (add_edge_graph g u v e).
Proof.
  intros g u v e Hg Hu Hv Hne.
  unfold gvalid, gvalid_instance, graph_wf in *.
  intros a Ha.
  rewrite add_edge_graph_evalid in Ha by auto.
  destruct Ha as [Ha | ->].
  - destruct (Hg a Ha) as [x [y Hstep]].
    exists x, y.
    rewrite add_edge_graph_step by auto.
    left; exact Hstep.
  - exists u, v.
    rewrite add_edge_graph_step by auto.
    right; split; [reflexivity|auto].
Qed.

Lemma remove_edge_graph_gvalid :
  forall g u v e,
    gvalid g ->
    step_aux g e u v ->
    gvalid (remove_edge_graph g e).
Proof.
  intros g u v e Hg Hstep.
  unfold gvalid, gvalid_instance, graph_wf in *.
  intros a Ha.
  unfold remove_edge_graph in Ha; simpl in Ha.
  apply filter_In in Ha as [Ha Hkeep].
  destruct (Z.eq_dec a e) as [Ha_eq | Ha_neq]; [discriminate|].
  destruct (Hg a Ha) as [x [y Hstep_a]].
  destruct (proj1 (remove_edge_graph_step g u v e x y a Hg Hstep) Hstep_a)
    as [Hremove | [Ha_eq Hnew]].
  - exists x, y; exact Hremove.
  - contradiction.
Qed.

#[export] Instance addEdgeInSubgraph_instance :
  addEdgeInSubgraph G V E.
Proof.
  constructor.
  - intros g s u v e Hg Hs Hsub Hstep Hu Hv Hne.
    exists (add_edge_graph s u v e).
    split.
    + apply add_edge_graph_gvalid_any; auto.
    + split.
      * apply add_edge_graph_addEdge_any; auto.
      * constructor.
        -- intros z Hz.
           rewrite add_edge_graph_vvalid in Hz.
           destruct Hz as [Hz | [-> | ->]].
           ++ apply Hsub; exact Hz.
           ++ apply Hsub; exact Hu.
           ++ apply Hsub; exact Hv.
        -- intros x y a Ha.
           rewrite add_edge_graph_step_any in Ha by auto.
           destruct Ha as [Ha_old | [Ha_new Hxy]].
           ++ apply Hsub; exact Ha_old.
           ++ subst a.
              destruct Hxy as [[-> ->] | [-> ->]]; [exact Hstep|].
              apply step_sym; exact Hstep.
  - intros g s u v e Hg Hs Hsub Hstep Hu Hvout Hne.
    exists (add_edge_graph s u v e).
    split.
    + apply add_edge_graph_gvalid_new_vertex; auto.
    + split.
      * apply add_edge_graph_addEdge_any; auto.
      * constructor.
        -- intros z Hz.
           rewrite add_edge_graph_vvalid in Hz.
           destruct Hz as [Hz | [-> | ->]].
           ++ apply Hsub; exact Hz.
           ++ apply Hsub; exact Hu.
           ++ eapply step_vvalid2; eauto.
        -- intros x y a Ha.
           rewrite add_edge_graph_step_any in Ha by auto.
           destruct Ha as [Ha_old | [Ha_new Hxy]].
           ++ apply Hsub; exact Ha_old.
           ++ subst a.
              destruct Hxy as [[-> ->] | [-> ->]]; [exact Hstep|].
              apply step_sym; exact Hstep.
  - intros g h u v e Hg Hh Hsub Hu Hv He Hstep.
    exists (remove_edge_graph h e).
    split.
    + eapply remove_edge_graph_gvalid; eauto.
    + split.
      * constructor.
        -- intros z.
           rewrite remove_edge_graph_vvalid.
           split.
           ++ intros Hz; left; exact Hz.
           ++ intros [Hz | [-> | ->]]; auto.
        -- intros a.
           rewrite remove_edge_graph_evalid.
           split.
           ++ intros Ha.
              destruct (Z.eq_dec a e) as [-> | Hneq]; auto.
           ++ intros [[Ha _] | ->]; auto.
        -- intros x y a.
           apply remove_edge_graph_step; auto.
      * split.
        -- constructor.
           ++ intros z Hz.
              rewrite remove_edge_graph_vvalid in Hz.
              apply Hsub; exact Hz.
           ++ intros x y a Ha.
              apply Hsub.
              apply (proj2 (remove_edge_graph_step h u v e x y a Hh Hstep)).
              left; exact Ha.
        -- repeat split.
           ++ rewrite remove_edge_graph_vvalid; exact Hu.
           ++ rewrite remove_edge_graph_vvalid; exact Hv.
           ++ rewrite remove_edge_graph_evalid.
              intros [_ Hneq]; auto.
Qed.

Lemma Prim2_correct_concrete :
  forall g src,
    PrimEnv g src ->
    Hoare (initStPred g src) (Prim2 g)
      (fun _ s => return_is_mst g s.(Prim.graph_in_state)).
Proof.
  intros g src Henv.
  destruct Henv as [Hg Hsrc Hconn].
  unfold initStPred, Prim2, initSt, return_is_mst.
  eapply (@Prim.Prim2_correct
    G V E graph_instance gvalid_instance
    stepvalid_instance noempty_instance undirected_instance stepunique_instance
    finite_instance elist_bijective_instance
    g
    P path_instance emptypath_instance singlepath_instance concatpath_instance
    destruct1npath_instance tree_instance
    edge_weight_instance
    Hconn
    src Hsrc Hg
    addEdgeInSubgraph_instance addEdgeGValid_instance
    (emptyGraph_instance g src)).
Qed.

Record multiset (A : Type) : Type := {
  mlist : list A
}.

Arguments mlist {A} _.

Definition list_to_multiset {A} (l : list A) : multiset A :=
  {| mlist := l |}.

Definition multiset_empty {A} : multiset A :=
  list_to_multiset [].

Definition multiset_size {A} (S : multiset A) : Z :=
  Zlength (mlist S).

Definition multiset_insert {A}
    (S : multiset A) (x : A) : multiset A :=
  list_to_multiset (x :: mlist S).

Definition multiset_remove {A}
    (S : multiset A) (x : A) : multiset A :=
  let fix remove_one (l : list A) : list A :=
    match l with
    | [] => []
    | y :: ys =>
        if excluded_middle_informative (x = y)
        then ys
        else y :: remove_one ys
    end
  in list_to_multiset (remove_one (mlist S)).

Lemma mlist_list_to_multiset :
  forall A (l : list A),
    mlist (list_to_multiset l) = l.
Proof.
  reflexivity.
Qed.

Lemma multiset_insert_mlist :
  forall A (S : multiset A) x,
    mlist (multiset_insert S x) =
    x :: mlist S.
Proof.
  reflexivity.
Qed.

Lemma multiset_insert_size :
  forall A (S : multiset A) x,
    multiset_size (multiset_insert S x) =
    multiset_size S + 1.
Proof.
  intros.
  unfold multiset_size, multiset_insert, list_to_multiset.
  simpl.
  rewrite Zlength_cons.
  lia.
Qed.

(** * 双数组最小堆模型

    这部分仿照 [LLM_bench/Data_structures/priority_queue]，但 Prim 需要
    存二元信息：cost 是当前候选代价，vertex 是候选点编号。因此 C 中使用
    两个数组 [heap_cost] 和 [heap_vertex]，逻辑层用 [(cost, vertex)] 列表描述。

    本区命名尽量和 [priority_queue_lib.v] 对齐，并统一加 [Pair] 后缀表示
    “双数组一起移动”的版本。 *)

Definition HeapEntry : Type := (Z * V)%type.

(** [IntArray.full] 存储的每个元素都是合法 int。 *)
Lemma IntArray_full_int_range :
  forall p n l idx,
    0 <= idx < Zlength l ->
    IntArray.full p n l |-- “ INT_MIN <= Znth idx l 0 <= INT_MAX ”.
Proof.
  intros p n l.
  revert p n.
  induction l as [| a l IH]; intros p n idx Hr.
  - simpl in Hr. rewrite Zlength_nil in Hr. lia.
  - rewrite IntArray.full_unfold.
    destruct (Z.eq_dec idx 0) as [Heq | Hneq].
    + subst idx. simpl.
      sep_apply (store_int_range (p + 0 * sizeof(INT)) a).
      LLM_pre_process ltac:(lia).
    + sep_apply (IntArray.seg_to_full p 1 n l).
      assert (Hrange : 0 <= idx - 1 < Zlength l).
      { rewrite Zlength_cons in Hr.
        assert (Hidx_ge1 : 1 <= idx) by lia.
        lia. }
      sep_apply (IH (p + 1 * sizeof(INT)) (n - 1) (idx - 1) Hrange).
      LLM_pre_process ltac:(lia).
      { destruct H as [Hlo Hhi].
        replace (Znth idx (a :: l) 0) with (Znth (idx - 1) l 0).
        { LLM_pre_process ltac:(lia). }
        { unfold Znth.
          assert (Hz : Z.to_nat idx = S (Z.to_nat (idx - 1))).
          { rewrite <- (Z2Nat.inj_succ (idx - 1)) by lia.
            f_equal. lia. }
          rewrite Hz.
          simpl. reflexivity. } }
Qed.

(** [IntArray.full] 存储的每个元素都是合法 int（全局版）。 *)
Lemma IntArray_full_int_range_all :
  forall p n l,
    IntArray.full p n l |--
      “ forall idx, 0 <= idx < Zlength l ->
         INT_MIN <= Znth idx l 0 <= INT_MAX ”.
Proof.
  intros p n l m HA idx Hr.
  exact (IntArray_full_int_range p n l idx Hr m HA).
Qed.

Definition HeapParent (child : Z) : Z :=
  Z.quot (child - 1) 2.

Lemma heap_pair_Zlength_replace_Znth :
  forall {A : Type} (l : list A) i (v : A),
    Zlength (replace_Znth i v l) = Zlength l.
Proof.
  intros.
  apply Zlength_replace_Znth.
Qed.

Lemma heap_pair_Znth_replace_Znth_same :
  forall {A : Type} (l : list A) i (v d : A),
    0 <= i < Zlength l ->
    Znth i (replace_Znth i v l) d = v.
Proof.
  intros A l i v d Hi.
  unfold Znth.
  apply Znth_replace_Znth_Same.
  exact Hi.
Qed.

Lemma heap_pair_Znth_replace_Znth_diff :
  forall {A : Type} (l : list A) i j (v d : A),
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    i <> j ->
    Znth j (replace_Znth i v l) d = Znth j l d.
Proof.
  intros A l i j v d Hi Hj Hneq.
  unfold Znth.
  apply Znth_replace_Znth_Diff; auto.
Qed.

Lemma heap_pair_sublist_replace_last :
  forall {A : Type} (l : list A) n (v : A),
    0 < n ->
    Zlength l = n ->
    sublist 0 (n - 1) (replace_Znth (n - 1) v l) =
    sublist 0 (n - 1) l.
Proof.
  intros A l n v Hn Hlen.
  apply (proj2 (list_eq_ext _ _ (Znth 0 l v))).
  split.
  - repeat rewrite Zlength_sublist by (rewrite ?Zlength_replace_Znth; lia).
    lia.
  - intros i Hi.
    rewrite Zlength_sublist in Hi by (rewrite ?Zlength_replace_Znth; lia).
    repeat rewrite Znth_sublist by (rewrite ?Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
    reflexivity.
Qed.

Lemma heap_pair_Z_list_init_last_by_sublist :
  forall (l : list Z) n,
    0 < n ->
    Zlength l = n ->
    l = sublist 0 (n - 1) l ++ Znth (n - 1) l 0 :: nil.
Proof.
  intros l n Hn Hlen.
  rewrite <- (sublist_self l n) at 1 by lia.
  rewrite (sublist_split 0 n (n - 1) l) by lia.
  replace (sublist (n - 1) n l) with (Znth (n - 1) l 0 :: nil).
  2:{
    symmetry.
    change (Znth (n - 1) l 0 :: nil) with ([Znth (n - 1) l 0]).
    rewrite <- (@sublist_single Z 0 (n - 1) l) by lia.
    replace (n - 1 + 1) with n by lia.
    reflexivity.
  }
  reflexivity.
Qed.

Lemma int_array_full_drop_last_to_prefix_undef :
  forall p n (l : list Z),
    0 < n ->
    Zlength l = n ->
    IntArray.full p n l |--
      IntArray.full p (n - 1) (sublist 0 (n - 1) l) **
      IntArray.undef_seg p (n - 1) n.
Proof.
  intros p n l Hn Hlen.
  sep_apply_l_atomic (IntArray.full_split_to_seg p (n - 1) n l).
  - LLM_pre_process ltac:(lia); lia.
  - sep_apply_l_atomic
      (IntArray.seg_to_full p 0 (n - 1) (sublist 0 (n - 1) l)).
    replace (n - 1 - 0) with (n - 1) by lia.
    sep_apply_l_atomic
      (IntArray.seg_to_undef_seg p (n - 1) n (sublist (n - 1) n l)).
    replace (p + 0 * sizeof (INT)) with p by lia.
    LLM_pre_process ltac:(lia).
Qed.

Lemma two_int_array_full_drop_last_to_prefix_undef :
  forall vertex_p cost_p n vertex_l cost_l,
    0 < n ->
    Zlength vertex_l = n ->
    Zlength cost_l = n ->
    IntArray.full vertex_p n vertex_l **
    IntArray.full cost_p n cost_l |--
      IntArray.full cost_p (n - 1) (sublist 0 (n - 1) cost_l) **
      IntArray.full vertex_p (n - 1) (sublist 0 (n - 1) vertex_l) **
      IntArray.undef_seg cost_p (n - 1) n **
      IntArray.undef_seg vertex_p (n - 1) n.
Proof.
  intros vertex_p cost_p n vertex_l cost_l Hn Hvertex_len Hcost_len.
  sep_apply_l_atomic
    (int_array_full_drop_last_to_prefix_undef vertex_p n vertex_l Hn Hvertex_len).
  sep_apply_l_atomic
    (int_array_full_drop_last_to_prefix_undef cost_p n cost_l Hn Hcost_len).
  cancel.
Qed.

Lemma heap_pair_list_head_tail_by_sublist :
  forall {A : Type} (l : list A) n d,
    0 < n ->
    Zlength l = n ->
    l = Znth 0 l d :: sublist 1 n l.
Proof.
  intros A l n d Hn Hlen.
  rewrite <- (sublist_self l n) at 1 by lia.
  rewrite (sublist_split 0 n 1 l) by lia.
  replace (sublist 0 1 l) with (Znth 0 l d :: nil).
  2:{
    replace 1 with (0 + 1) by lia.
    symmetry.
    apply sublist_single.
    lia.
  }
  simpl.
  reflexivity.
Qed.

Lemma heap_pair_Zlength_replace_Znth2 :
  forall {A : Type} (l : list A) i j (vi vj : A),
    Zlength (replace_Znth i vi (replace_Znth j vj l)) = Zlength l.
Proof.
  intros.
  repeat rewrite heap_pair_Zlength_replace_Znth.
  reflexivity.
Qed.

Lemma heap_pair_Zlength_replace_Znth2_le :
  forall {A : Type} (l : list A) i j (vi vj : A) n,
    n <= Zlength l ->
    n <= Zlength (replace_Znth i vi (replace_Znth j vj l)).
Proof.
  intros.
  rewrite heap_pair_Zlength_replace_Znth2.
  exact H.
Qed.

Lemma heap_pair_int_range_swap_replace :
  forall (l : list Z) n i j,
    Zlength l = n + 1 ->
    0 <= i < n + 1 ->
    0 <= j < n + 1 ->
    (forall idx,
      0 <= idx < n + 1 ->
      INT_MIN <= Znth idx l 0 <= INT_MAX) ->
    forall idx,
      0 <= idx < n + 1 ->
      INT_MIN <=
        Znth idx
          (replace_Znth i (Znth j l 0)
            (replace_Znth j (Znth i l 0) l)) 0 <=
      INT_MAX.
Proof.
  intros l n i j Hlen Hi Hj Hrange idx Hidx.
  destruct (Z.eq_dec idx i) as [Heqi | Hnei].
  - subst idx.
    rewrite Znth_replace_Znth_same_local by
      (rewrite Zlength_replace_Znth_local; lia).
    apply Hrange; lia.
  - rewrite (Znth_replace_Znth_diff_local
        (replace_Znth j (Znth i l 0) l)
        i idx (Znth j l 0)) by
      (try rewrite Zlength_replace_Znth_local; lia).
    destruct (Z.eq_dec idx j) as [Heqj | Hnej].
    + subst idx.
      rewrite Znth_replace_Znth_same_local by lia.
      apply Hrange; lia.
    + rewrite (Znth_replace_Znth_diff_local
          l j idx (Znth i l 0)) by lia.
      apply Hrange; lia.
Qed.

Definition HeapEntriesPair
    (heap_cost heap_vertex : list Z) (n : Z) : list HeapEntry :=
  map
    (fun idx => (Znth idx heap_cost 0, Znth idx heap_vertex 0))
    (Zrange 0 n).

Definition MinHeapPrefixPair
    (heap_cost heap_vertex : list Z) (n : Z) : Prop :=
  0 <= n /\
  n <= Zlength heap_cost /\
  n <= Zlength heap_vertex /\
  forall child,
    0 < child /\ child < n ->
    Znth (HeapParent child) heap_cost 0 <= Znth child heap_cost 0.

Definition PrefixMinValuePair
    (entries : list HeapEntry) (cost : Z) (vertex : V) : Prop :=
  min_object_of_subset Z_op_le
    (fun entry => In entry entries)
    (fun entry => Some (fst entry))
    (cost, vertex).

Definition PriorityQueuePrefixPair
    (heap_cost heap_vertex : list Z) (n : Z) (entries : list HeapEntry) : Prop :=
  entries = HeapEntriesPair heap_cost heap_vertex n /\
  MinHeapPrefixPair heap_cost heap_vertex n /\
  (0 < n ->
   PrefixMinValuePair entries
     (Znth 0 heap_cost 0)
     (Znth 0 heap_vertex 0)).

(** 堆中保存的 vertex 都是 C 程序可访问的点编号。 *)
Definition HeapEntriesVertexRangePair (bound : Z) (entries : list HeapEntry) : Prop :=
  forall cost vertex,
    In (cost, vertex) entries ->
    0 <= vertex < bound.

(** 新版 priority_queue 风格的 pair 堆抽象。

    [multiset] 只描述堆里“有哪些 entry”，不描述数组顺序；
    [heap_representation_pair] 才把这个 multiset 和两条 C 数组前缀联系起来，
    并要求前缀满足最小堆序。这样 push/pop 的规格就不用偷看调用前
    [heap_size] 位置的数组值。 *)
Definition HeapEntrySet : Type := multiset HeapEntry.

Definition empty_heap_entry_set : HeapEntrySet := multiset_empty.

Lemma empty_heap_entry_set_mlist :
  mlist empty_heap_entry_set = nil.
Proof.
  unfold empty_heap_entry_set, multiset_empty.
  reflexivity.
Qed.

Definition heap_entry_set_insert
    (S : HeapEntrySet) (cost vertex : Z) : HeapEntrySet :=
  multiset_insert S (cost, vertex).

Definition heap_entry_eq_dec (x y : HeapEntry) : {x = y} + {x <> y}.
Proof.
  decide equality; apply Z.eq_dec.
Defined.

Definition heap_entry_set_remove
    (S : HeapEntrySet) (cost vertex : Z) : HeapEntrySet :=
  let fix remove_one (l : list HeapEntry) : list HeapEntry :=
    match l with
    | [] => []
    | (entry_cost, entry_vertex) :: rest =>
        if Z.eq_dec cost entry_cost
        then if Z.eq_dec vertex entry_vertex
             then rest
             else (entry_cost, entry_vertex) :: remove_one rest
        else (entry_cost, entry_vertex) :: remove_one rest
    end
  in list_to_multiset (remove_one (mlist S)).

Definition heap_entry_set_minimum
    (S : HeapEntrySet) (cost vertex : Z) : Prop :=
  In (cost, vertex) (mlist S) /\
  forall cost' vertex',
    In (cost', vertex') (mlist S) ->
    cost <= cost'.

Definition heap_entries_to_set (entries : list HeapEntry) : HeapEntrySet :=
  list_to_multiset entries.

Lemma PrefixMinValuePair_heap_entry_set_minimum :
  forall entries cost vertex,
    PrefixMinValuePair entries cost vertex ->
    heap_entry_set_minimum (heap_entries_to_set entries) cost vertex.
Proof.
  intros entries cost vertex Hmin.
  unfold PrefixMinValuePair, min_object_of_subset in Hmin.
  unfold heap_entry_set_minimum, heap_entries_to_set, list_to_multiset.
  cbn.
  destruct Hmin as [Hin Hle].
  split.
  - exact Hin.
  - intros cost' vertex' Hin'.
    specialize (Hle (cost', vertex') Hin').
    simpl in Hle.
    exact Hle.
Qed.

Definition heap_relation_pair
    (S : HeapEntrySet) (heap_cost heap_vertex : list Z) (size : Z) : Prop :=
  Permutation (mlist S) (HeapEntriesPair heap_cost heap_vertex size).

Definition heap_representation_pair
    (S : HeapEntrySet) (heap_cost heap_vertex : list Z) (size : Z) : Prop :=
  0 <= size /\
  Zlength heap_cost = size /\
  Zlength heap_vertex = size /\
  multiset_size S = size /\
  heap_relation_pair S heap_cost heap_vertex size /\
  MinHeapPrefixPair heap_cost heap_vertex size.

Definition store_heap_pair
    (heap_cost_ptr heap_vertex_ptr : Z) (S : HeapEntrySet) (size : Z)
    : Assertion :=
  EX heap_cost : list Z, EX heap_vertex : list Z,
    “ heap_representation_pair S heap_cost heap_vertex size ” &&
    IntArray.full heap_cost_ptr size heap_cost **
    IntArray.full heap_vertex_ptr size heap_vertex.

Lemma Zlength_zero_nil :
  forall {A : Type} (l : list A),
    Zlength l = 0 -> l = nil.
Proof.
  intros A l Hlen.
  destruct l as [| x xs]; [reflexivity|].
  rewrite Zlength_cons in Hlen.
  pose proof (Zlength_nonneg xs).
  lia.
Qed.

Lemma store_heap_pair_zero_to_empty_full :
  forall heap_cost_ptr heap_vertex_ptr S,
    store_heap_pair heap_cost_ptr heap_vertex_ptr S 0 |--
      IntArray.full heap_cost_ptr 0 nil **
      IntArray.full heap_vertex_ptr 0 nil.
Proof.
  intros heap_cost_ptr heap_vertex_ptr S.
  unfold store_heap_pair.
  Intros heap_cost heap_vertex.
  unfold heap_representation_pair in H.
  destruct H as [_ [Hcost_len [Hvertex_len _]]].
  apply Zlength_zero_nil in Hcost_len.
  apply Zlength_zero_nil in Hvertex_len.
  subst.
  cancel.
Qed.

Lemma IntArray_missing_i_replace_same_rec :
  forall p i lo hi (l : list Z) v,
    lo <= i < hi ->
    Zlength l = hi - lo ->
    store_array_missing_i_rec
      (fun (x : addr) (lo a : Z) => (x + lo * sizeof(INT)) # Int |-> a)
      p i lo hi l |--
    store_array_missing_i_rec
      (fun (x : addr) (lo a : Z) => (x + lo * sizeof(INT)) # Int |-> a)
      p i lo hi (replace_Znth (i - lo) v l).
Proof.
  intros p i lo hi l v Hi Hlen.
  revert p i lo hi v Hi Hlen.
  induction l as [| a l IH]; intros p i lo hi v Hi Hlen; simpl in *.
  - rewrite Zlength_nil in Hlen; lia.
  - destruct (Z.eq_dec i lo) as [Hi0 | Hi0].
    + subst i.
      replace (lo - lo) with 0 by lia.
      replace (replace_Znth 0 v (a :: l)) with (v :: l).
      2:{
        unfold replace_Znth.
        simpl.
        reflexivity.
      }
      simpl.
      Split.
      * Left; cancel.
      * Intros_p Hfalse.
        lia.
    + replace (replace_Znth (i - lo) v (a :: l))
        with (a :: replace_Znth (i - (lo + 1)) v l).
      2:{
        rewrite replace_Znth_cons by lia.
        replace (i - lo - 1) with (i - (lo + 1)) by lia.
        reflexivity.
      }
      simpl.
      assert (lo + 1 <= i < hi) by lia.
      assert (Zlength l = hi - (lo + 1)) by (rewrite Zlength_cons in Hlen; lia).
      Split.
      * Intros_p Heq.
        lia.
      * Intros_p Hgt.
        Right.
        sep_apply (IH p i (lo + 1) hi v H H0).
        andp_cancel.
Qed.

Lemma IntArray_missing_i_replace_same :
  forall p i n (l : list Z) v,
    0 <= i < n ->
    Zlength l = n ->
    IntArray.missing_i p i 0 n l |--
      IntArray.missing_i p i 0 n (replace_Znth i v l).
Proof.
  intros p i n l v Hi Hlen.
  unfold IntArray.missing_i.
  replace (replace_Znth i v l) with (replace_Znth (i - 0) v l) by (f_equal; lia).
  apply IntArray_missing_i_replace_same_rec; lia.
Qed.

Lemma store_heap_pair_from_full_prefix :
  forall heap_cost_ptr heap_vertex_ptr heap_cost heap_vertex size entries,
    PriorityQueuePrefixPair heap_cost heap_vertex size entries ->
    Zlength heap_cost = size ->
    Zlength heap_vertex = size ->
    IntArray.full heap_cost_ptr size heap_cost **
    IntArray.full heap_vertex_ptr size heap_vertex |--
      store_heap_pair heap_cost_ptr heap_vertex_ptr
        (heap_entries_to_set entries) size.
Proof.
  intros heap_cost_ptr heap_vertex_ptr heap_cost heap_vertex size entries
         Hpq Hcost_len Hvertex_len.
  unfold store_heap_pair.
  Exists heap_cost.
  Exists heap_vertex.
  unfold heap_representation_pair, heap_relation_pair, heap_entries_to_set,
    list_to_multiset.
  destruct Hpq as [Hentries [Hheap _]].
  andp_cancel.
  split.
  - rewrite <- Hcost_len.
    apply Zlength_nonneg.
  - split.
    + exact Hcost_len.
    + split.
      * exact Hvertex_len.
      * split.
        -- simpl.
           rewrite Hentries.
           unfold HeapEntriesPair.
           unfold multiset_size.
           rewrite !Zlength_correct.
           simpl.
           rewrite length_map.
           assert (0 <= size) by (rewrite <- Hcost_len; apply Zlength_nonneg).
           rewrite <- Zlength_correct.
           rewrite Zlength_Zrange by lia.
           lia.
        -- split.
          ++ simpl.
             rewrite Hentries.
             reflexivity.
          ++ exact Hheap.
Qed.

Definition heap_spare_pair
    (heap_cost_ptr heap_vertex_ptr size : Z) : Assertion :=
  IntArray.undef_seg heap_cost_ptr size (size + 1) **
  IntArray.undef_seg heap_vertex_ptr size (size + 1).

Definition PushSourcePair
    (written_cost written_vertex : list Z)
    (before : HeapEntrySet) (size cost vertex : Z) : Prop :=
  Zlength written_cost = size + 1 /\
  Zlength written_vertex = size + 1 /\
  Permutation
    (HeapEntriesPair written_cost written_vertex (size + 1))
    ((cost, vertex) :: mlist before) /\
  MinHeapPrefixPair written_cost written_vertex size.

Definition PushResultPair
    (before : HeapEntrySet) (result_cost result_vertex : list Z)
    (size cost vertex : Z) : Prop :=
  0 <= size /\
  Zlength result_cost = size + 1 /\
  Zlength result_vertex = size + 1 /\
  Permutation
    (HeapEntriesPair result_cost result_vertex (size + 1))
    ((cost, vertex) :: mlist before) /\
  MinHeapPrefixPair result_cost result_vertex (size + 1).

Definition HeapOrderExceptUpPair
    (heap_cost : list Z) (size child : Z) : Prop :=
  0 <= child /\
  child < size /\
  forall node,
    0 < node /\ node < size /\ node <> child ->
    Znth (HeapParent node) heap_cost 0 <= Znth node heap_cost 0.

Definition PushHoleChildrenPreservedPair
    (heap_cost : list Z) (size child : Z) : Prop :=
  forall node,
    0 < node /\ node < size /\ HeapParent node = child ->
    Znth (HeapParent child) heap_cost 0 <= Znth node heap_cost 0.

Definition PushLoopStatePair
    (written_cost written_vertex cost_cur vertex_cur : list Z)
    (size child cost vertex : Z) : Prop :=
  0 <= size /\
  Zlength written_cost = size + 1 /\
  Zlength written_vertex = size + 1 /\
  Zlength cost_cur = size + 1 /\
  Zlength vertex_cur = size + 1 /\
  0 <= child /\
  child <= size /\
  Znth child cost_cur 0 = cost /\
  Znth child vertex_cur 0 = vertex /\
  Permutation
    (HeapEntriesPair written_cost written_vertex (size + 1))
    (HeapEntriesPair cost_cur vertex_cur (size + 1)) /\
  HeapOrderExceptUpPair cost_cur (size + 1) child /\
  PushHoleChildrenPreservedPair cost_cur (size + 1) child.

Lemma heap_parent_bounds_pos_pair : forall child,
  0 < child ->
  0 <= HeapParent child /\ HeapParent child < child.
Proof.
  intros child Hchild.
  unfold HeapParent.
  split.
  - apply Z.quot_pos; lia.
  - apply Z.quot_lt_upper_bound; lia.
Qed.

Lemma Znth_map_local :
  forall {A B} (f : A -> B) (l : list A) (i : Z) (da : A) (db : B),
    0 <= i < Zlength l ->
    Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l i da db Hrange.
  unfold Znth.
  rewrite nth_indep with (d' := f da).
  - rewrite map_nth.
    reflexivity.
  - rewrite length_map.
    rewrite Zlength_correct in Hrange.
    lia.
Qed.

Lemma Znth_Zrange_aux :
  forall len low i d,
    0 <= i < Z.of_nat len ->
    Znth i (Zrange_aux low len) d = low + i.
Proof.
  induction len as [| len IH]; intros low i d Hrange; simpl in *.
  - lia.
  - destruct (Z.eq_dec i 0) as [-> | Hi0].
    + unfold Znth. simpl. lia.
    + rewrite Znth_cons by lia.
      rewrite IH by lia.
      lia.
Qed.

Lemma Znth_Zrange_0 :
  forall n i d,
    0 <= i < n ->
    Znth i (Zrange 0 n) d = i.
Proof.
  intros n i d Hrange.
  unfold Zrange.
  rewrite Znth_Zrange_aux by lia.
  lia.
Qed.

Lemma Znth_HeapEntriesPair :
  forall cost vertex n i d,
    0 <= i < n ->
    n <= Zlength cost ->
    n <= Zlength vertex ->
    Znth i (HeapEntriesPair cost vertex n) d =
      (Znth i cost 0, Znth i vertex 0).
Proof.
  intros cost vertex n i d Hi Hcost Hvertex.
  unfold HeapEntriesPair.
  rewrite Znth_map_local with (da := 0).
  - rewrite Znth_Zrange_0 by lia.
    reflexivity.
  - rewrite Zlength_Zrange by lia.
    lia.
Qed.

Lemma Zlength_HeapEntriesPair :
  forall cost vertex n,
    0 <= n ->
    Zlength (HeapEntriesPair cost vertex n) = n.
Proof.
  intros cost vertex n Hn.
  unfold HeapEntriesPair.
  rewrite !Zlength_correct.
  rewrite length_map.
  rewrite <- Zlength_correct.
  rewrite Zlength_Zrange by lia.
  lia.
Qed.

Lemma HeapEntriesVertexRangePair_root :
  forall bound cost vertex n,
    0 < n ->
    n <= Zlength cost ->
    n <= Zlength vertex ->
    HeapEntriesVertexRangePair bound (HeapEntriesPair cost vertex n) ->
    0 <= Znth 0 vertex 0 < bound.
Proof.
  intros bound cost vertex n Hn Hcost Hvertex Hrange.
  specialize (Hrange (Znth 0 cost 0) (Znth 0 vertex 0)).
  apply Hrange.
  assert (Hin0 :
    In (Znth 0 (HeapEntriesPair cost vertex n) (0, 0))
      (HeapEntriesPair cost vertex n)).
  {
    apply (Znth_In_Zlength (HeapEntriesPair cost vertex n) (0, 0) 0).
    rewrite Zlength_HeapEntriesPair by lia.
    lia.
  }
  rewrite Znth_HeapEntriesPair in Hin0 by lia.
  exact Hin0.
Qed.

Lemma HeapEntriesPair_sublist_prefix :
  forall cost vertex n,
    0 <= n ->
    HeapEntriesPair (sublist 0 n cost) (sublist 0 n vertex) n =
    HeapEntriesPair cost vertex n.
Proof.
  intros cost vertex n Hn.
  unfold HeapEntriesPair.
  apply map_ext_in.
  intros i Hi.
  rewrite <- In_Zrange in Hi.
  repeat rewrite Znth_sublist by lia.
  replace (i + 0) with i by lia.
  reflexivity.
Qed.

Lemma PriorityQueuePrefixPair_sublist_prefix :
  forall cost vertex n,
    0 <= n ->
    n <= Zlength cost ->
    n <= Zlength vertex ->
    PriorityQueuePrefixPair cost vertex n (HeapEntriesPair cost vertex n) ->
    PriorityQueuePrefixPair
      (sublist 0 n cost) (sublist 0 n vertex) n
      (HeapEntriesPair (sublist 0 n cost) (sublist 0 n vertex) n).
Proof.
  intros cost vertex n Hn Hcost Hvertex HPQ.
  unfold PriorityQueuePrefixPair in *.
  destruct HPQ as [Hentries [Hheap Hmin]].
  split.
  - reflexivity.
  - split.
    +
      unfold MinHeapPrefixPair in *.
      destruct Hheap as [Hn0 [Hcost0 [Hvertex0 Horder]]].
      repeat split.
      * lia.
      * rewrite Zlength_sublist by lia; lia.
      * rewrite Zlength_sublist by lia; lia.
      * intros child Hchild.
        assert (Hparent : 0 <= HeapParent child < n).
        {
          destruct Hchild as [Hchild0 Hchildn].
          pose proof (heap_parent_bounds_pos_pair child Hchild0) as [Hp0 Hplt].
          lia.
        }
        repeat rewrite Znth_sublist by lia.
        replace (HeapParent child + 0) with (HeapParent child) by lia.
        replace (child + 0) with child by lia.
        apply Horder.
        split; [lia|].
        destruct Hchild as [Hchild0 Hchildn].
        exact Hchildn.
    + intros Hpos.
      rewrite HeapEntriesPair_sublist_prefix by lia.
      specialize (Hmin Hpos).
      unfold PrefixMinValuePair in *.
      unfold min_object_of_subset in *.
      destruct Hmin as [Hin Hle].
      split.
      * repeat rewrite Znth_sublist by lia.
        replace (0 + 0) with 0 by lia.
        exact Hin.
      * intros y Hy.
        specialize (Hle y Hy).
        repeat rewrite Znth_sublist by lia.
        replace (0 + 0) with 0 by lia.
        exact Hle.
Qed.

Lemma replace_Znth_swap_form_any :
  forall {A : Type} (l1 l2 l3 : list A) (xi xj : A),
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros A l1 l2 l3 xi xj.
  assert (Hlen2 : 0 <= Zlength l2) by (rewrite Zlength_correct; lia).
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with (l1 := l1) (l2 := xi :: l2 ++ xj :: l3)
    by (subst n1; lia).
  rewrite (replace_Znth_nothing (A := A) n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  simpl.
  rewrite replace_Znth_app_r with (l1 := l1) (l2 := xj :: l2 ++ xj :: l3)
    by (subst n2; lia).
  rewrite (replace_Znth_nothing (A := A) (n1 + 1 + Zlength l2) l1 xi)
    by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1) with (1 + Zlength l2)
    by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with (l1 := l2) (l2 := xj :: l3) by lia.
  rewrite (replace_Znth_nothing (A := A) (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  simpl.
  reflexivity.
Qed.

Lemma permutation_swap_Znth_lt_any :
  forall {A : Type} (l : list A) i j (d : A),
    0 <= i /\ i < j /\ j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d Hrange.
  destruct Hrange as [Hi [Hij Hj]].
  remember (Znth i l d) as xi0.
  remember (Znth j l d) as xj0.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni l).
  set (lr := skipn (S ni) l).
  set (l2 := firstn nj lr).
  set (l3 := skipn (S nj) lr).
  assert (Hsplit_i : l = l1 ++ xi0 :: lr).
  {
    subst l1 lr ni.
    rewrite (list_split_nth _ (Z.to_nat i) l d) at 1.
    2:{ rewrite Zlength_correct in Hj. lia. }
    rewrite Heqxi0.
    reflexivity.
  }
  assert (Hj_lr : (nj < List.length lr)%nat).
  {
    subst nj lr ni.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  assert (Hsplit_j : lr = l2 ++ xj0 :: l3).
  {
    subst l2 l3.
    rewrite (list_split_nth _ nj lr d) at 1 by exact Hj_lr.
    replace xj0 with (nth nj lr d).
    2:{
      subst nj lr ni.
      rewrite Heqxj0.
      unfold Znth.
      rewrite nth_skipn.
      assert (Hnat : (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat = Z.to_nat j).
      {
        apply Nat2Z.inj.
        rewrite Nat2Z.inj_add.
        rewrite Nat2Z.inj_succ.
        repeat rewrite Z2Nat.id by lia.
        lia.
      }
      rewrite Nat.add_comm.
      rewrite Hnat.
      reflexivity.
    }
    reflexivity.
  }
  assert (Hl : l = l1 ++ xi0 :: l2 ++ xj0 :: l3).
  {
    rewrite Hsplit_j in Hsplit_i.
    exact Hsplit_i.
  }
  replace l with (l1 ++ xi0 :: l2 ++ xj0 :: l3) by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2:{
    subst l1 ni.
    rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj.
    rewrite Nat.min_l by lia.
    lia.
  }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2:{
    subst l1 l2 lr ni nj.
    rewrite !Zlength_correct.
    rewrite !length_firstn.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  rewrite replace_Znth_swap_form_any.
  eapply Permutation_trans.
  2:{ reflexivity. }
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head.
      apply perm_swap.
    + apply Permutation_sym.
      apply Permutation_middle.
Qed.

Lemma replace_nth_comm_any :
  forall {A : Type} ni nj (l : list A) (a b : A),
    ni <> nj ->
    replace_nth nj (replace_nth ni l a) b =
    replace_nth ni (replace_nth nj l b) a.
Proof.
  intros A ni nj l a b Hneq.
  revert nj l Hneq.
  induction ni as [|ni IH]; intros nj l Hneq; destruct l as [|x xs]; simpl.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + contradiction Hneq; reflexivity.
    + reflexivity.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + reflexivity.
    + f_equal.
      apply IH.
      intros Heq.
      apply Hneq.
      now f_equal.
Qed.

Lemma replace_Znth_comm_any :
  forall {A : Type} (l : list A) i j (a b : A),
    0 <= i ->
    0 <= j ->
    i <> j ->
    replace_Znth j b (replace_Znth i a l) =
    replace_Znth i a (replace_Znth j b l).
Proof.
  intros A l i j a b Hi Hj Hneq.
  unfold replace_Znth.
  apply replace_nth_comm_any.
  intro Heq.
  apply Hneq.
  apply Z2Nat.inj in Heq; lia.
Qed.

Lemma permutation_swap_Znth_any :
  forall {A : Type} (l : list A) i j (d : A),
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d Hi Hj.
  destruct (Z_lt_ge_dec i j) as [Hij | Hge].
  - apply permutation_swap_Znth_lt_any.
    lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Heq].
    + rewrite replace_Znth_comm_any by lia.
      apply permutation_swap_Znth_lt_any.
      lia.
    + assert (i = j) by lia.
      subst j.
      rewrite replace_Znth_Znth by lia.
      rewrite replace_Znth_Znth by lia.
      apply Permutation_refl.
Qed.

Lemma HeapEntriesPair_swap_lt :
  forall cost vertex size i j,
    0 <= i < j ->
    j < size ->
    size <= Zlength cost ->
    size <= Zlength vertex ->
    Permutation
      (HeapEntriesPair
        (replace_Znth j (Znth i cost 0) (replace_Znth i (Znth j cost 0) cost))
        (replace_Znth j (Znth i vertex 0) (replace_Znth i (Znth j vertex 0) vertex))
        size)
      (HeapEntriesPair cost vertex size).
Proof.
  intros cost vertex size i j Hij Hj Hcost Hvertex.
  assert (Hsize_nonneg : 0 <= size) by lia.
  set (entries := HeapEntriesPair cost vertex size).
  set (cost_swapped :=
    replace_Znth j (Znth i cost 0) (replace_Znth i (Znth j cost 0) cost)).
  set (vertex_swapped :=
    replace_Znth j (Znth i vertex 0) (replace_Znth i (Znth j vertex 0) vertex)).
  assert (Hentries_len : Zlength entries = size).
  { subst entries. apply Zlength_HeapEntriesPair. lia. }
  assert (Hswap_eq :
    HeapEntriesPair cost_swapped vertex_swapped size =
    replace_Znth j (Znth i entries (0, 0))
      (replace_Znth i (Znth j entries (0, 0)) entries)).
  {
    apply list_eq_ext with (d := (0, 0)).
    split.
    - rewrite Zlength_HeapEntriesPair by lia.
      rewrite !Zlength_replace_Znth.
      symmetry. exact Hentries_len.
    - intros k Hk.
      rewrite Zlength_HeapEntriesPair in Hk by lia.
      destruct (Z.eq_dec k j) as [-> | Hkj].
      + subst entries cost_swapped vertex_swapped.
        rewrite Znth_HeapEntriesPair by (rewrite ?Zlength_replace_Znth; lia).
        rewrite !Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
        rewrite Znth_HeapEntriesPair by lia.
        rewrite Znth_replace_Znth_Same by
          (rewrite ?Zlength_replace_Znth, ?Zlength_HeapEntriesPair; lia).
        reflexivity.
      + destruct (Z.eq_dec k i) as [-> | Hki].
        * subst entries cost_swapped vertex_swapped.
          rewrite Znth_HeapEntriesPair by (rewrite ?Zlength_replace_Znth; lia).
          rewrite Znth_replace_Znth_Diff with (i := j) (j := i)
            by (rewrite ?Zlength_replace_Znth; lia).
          rewrite Znth_replace_Znth_Same by lia.
          rewrite Znth_replace_Znth_Diff with (i := j) (j := i)
            by (rewrite ?Zlength_replace_Znth; lia).
          rewrite Znth_replace_Znth_Same by lia.
          rewrite Znth_HeapEntriesPair by lia.
          rewrite Znth_replace_Znth_Diff with (i := j) (j := i)
            by (rewrite ?Zlength_replace_Znth, ?Zlength_HeapEntriesPair; lia).
          rewrite Znth_replace_Znth_Same by
            (rewrite ?Zlength_HeapEntriesPair; lia).
          rewrite Znth_HeapEntriesPair by lia.
          reflexivity.
        * subst entries cost_swapped vertex_swapped.
          rewrite Znth_HeapEntriesPair by (rewrite ?Zlength_replace_Znth; lia).
          repeat rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
          rewrite Znth_HeapEntriesPair by lia.
          rewrite Znth_replace_Znth_Diff with (i := j) (j := k)
            by (rewrite ?Zlength_replace_Znth, ?Zlength_HeapEntriesPair; lia).
          rewrite Znth_replace_Znth_Diff with (i := i) (j := k)
            by (rewrite ?Zlength_HeapEntriesPair; lia).
          rewrite Znth_HeapEntriesPair by lia.
          reflexivity.
  }
  rewrite Hswap_eq.
  apply Permutation_sym.
  subst entries.
  apply permutation_swap_Znth_any;
    rewrite Zlength_HeapEntriesPair by lia; lia.
Qed.

Lemma push_loop_pair_swap :
  forall cost_before vertex_before cost_cur vertex_cur n child parent cost vertex,
    PushLoopStatePair
      cost_before vertex_before cost_cur vertex_cur n child cost vertex ->
    0 < child ->
    parent = HeapParent child ->
    parent < child ->
    Znth parent cost_cur 0 > Znth child cost_cur 0 ->
    PushLoopStatePair
      cost_before vertex_before
      (replace_Znth child (Znth parent cost_cur 0)
         (replace_Znth parent (Znth child cost_cur 0) cost_cur))
      (replace_Znth child (Znth parent vertex_cur 0)
         (replace_Znth parent (Znth child vertex_cur 0) vertex_cur))
      n parent cost vertex.
Proof.
  intros cost_before vertex_before cost_cur vertex_cur n child parent cost vertex
         Hstate Hchild_pos Hparent_eq Hparent_child Hswap_cond.
  unfold PushLoopStatePair in Hstate.
  destruct Hstate as [Hn0 Hstate].
  destruct Hstate as [Hwritten_cost_len Hstate].
  destruct Hstate as [Hwritten_vertex_len Hstate].
  destruct Hstate as [Hcost_cur_len Hstate].
  destruct Hstate as [Hvertex_cur_len Hstate].
  destruct Hstate as [Hchild0 Hstate].
  destruct Hstate as [Hchildn Hstate].
  destruct Hstate as [Hcost_child Hstate].
  destruct Hstate as [Hvertex_child Hstate].
  destruct Hstate as [Hperm [Hexcept Hchildren]].
  unfold HeapOrderExceptUpPair in Hexcept.
  destruct Hexcept as [_ [_ Hexcept_ord]].
  unfold PushHoleChildrenPreservedPair in Hchildren.
  set (cost_swapped :=
    replace_Znth child (Znth parent cost_cur 0)
      (replace_Znth parent (Znth child cost_cur 0) cost_cur)).
  set (vertex_swapped :=
    replace_Znth child (Znth parent vertex_cur 0)
      (replace_Znth parent (Znth child vertex_cur 0) vertex_cur)).
  destruct (heap_parent_bounds_pos_pair child Hchild_pos)
    as [Hheap_parent0 Hheap_parentlt].
  assert (Hparent0 : 0 <= parent) by lia.
  assert (Hparentn : parent <= n) by lia.
  assert (Hparent_len_cost : parent < Zlength cost_cur) by lia.
  assert (Hchild_len_cost : child < Zlength cost_cur) by lia.
  assert (Hparent_len_vertex : parent < Zlength vertex_cur) by lia.
  assert (Hchild_len_vertex : child < Zlength vertex_cur) by lia.
  assert (Hswap_parent_cost :
    Znth parent cost_swapped 0 = Znth child cost_cur 0).
  {
    subst cost_swapped.
    rewrite Znth_replace_Znth_Diff with (i := child) (j := parent)
      by (rewrite ?Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  }
  assert (Hswap_child_cost :
    Znth child cost_swapped 0 = Znth parent cost_cur 0).
  {
    subst cost_swapped.
    rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
    reflexivity.
  }
  assert (Hswap_other_cost :
    forall k,
      0 <= k < Zlength cost_cur ->
      k <> parent ->
      k <> child ->
      Znth k cost_swapped 0 = Znth k cost_cur 0).
  {
    intros k Hk Hk_parent Hk_child.
    subst cost_swapped.
    rewrite Znth_replace_Znth_Diff with (i := child) (j := k)
      by (rewrite ?Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff with (i := parent) (j := k) by lia.
    reflexivity.
  }
  assert (Hswap_parent_vertex :
    Znth parent vertex_swapped 0 = Znth child vertex_cur 0).
  {
    subst vertex_swapped.
    rewrite Znth_replace_Znth_Diff with (i := child) (j := parent)
      by (rewrite ?Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  }
  unfold PushLoopStatePair.
  split; [lia|].
  split; [exact Hwritten_cost_len|].
  split; [exact Hwritten_vertex_len|].
  split; [subst cost_swapped; rewrite !Zlength_replace_Znth; lia|].
  split; [subst vertex_swapped; rewrite !Zlength_replace_Znth; lia|].
		  split; [lia|].
	  split; [lia|].
		  split.
		  - subst cost_swapped.
		    rewrite Znth_replace_Znth_Diff with (i := child) (j := parent)
		      by (rewrite ?Zlength_replace_Znth; lia).
	    rewrite Znth_replace_Znth_Same by lia.
	    exact Hcost_child.
		  - split.
		    + rewrite Hswap_parent_vertex.
		      exact Hvertex_child.
			    + split.
			      * eapply Permutation_trans.
			        -- exact Hperm.
			        -- apply Permutation_sym.
			           subst cost_swapped vertex_swapped.
			           apply HeapEntriesPair_swap_lt; lia.
			      * split.
              { unfold HeapOrderExceptUpPair.
           split; [lia|].
           split; [lia|].
           intros node [Hnode_pos [Hnode_bound Hnode_neq_parent]].
           destruct (Z.eq_dec node child) as [Hnode_child | Hnode_not_child].
           ++ subst node.
              rewrite <- Hparent_eq.
              rewrite Hswap_parent_cost, Hswap_child_cost.
              lia.
           ++ destruct (Z.eq_dec (HeapParent node) child)
                as [Hnode_parent_child | Hnode_parent_not_child].
              ** rewrite Hnode_parent_child.
                 rewrite Hswap_child_cost.
                 rewrite Hswap_other_cost.
                 2:{ lia. }
                 2:{ exact Hnode_neq_parent. }
                 2:{ exact Hnode_not_child. }
                 rewrite Hparent_eq.
                 apply Hchildren.
                 lia.
              ** destruct (Z.eq_dec (HeapParent node) parent)
                   as [Hnode_parent_parent | Hnode_parent_other].
                 --- rewrite Hnode_parent_parent.
                     rewrite Hswap_parent_cost.
                     rewrite Hswap_other_cost.
                     2:{ lia. }
                     2:{ exact Hnode_neq_parent. }
                     2:{ exact Hnode_not_child. }
                     assert (Hparent_node : Znth parent cost_cur 0 <= Znth node cost_cur 0).
                     { rewrite <- Hnode_parent_parent.
	                   apply Hexcept_ord.
	                   lia. }
		                 lia.
                 --- destruct (heap_parent_bounds_pos_pair node Hnode_pos)
                       as [Hnode_parent0 Hnode_parentlt].
                     rewrite Hswap_other_cost.
                     2:{ lia. }
                     2:{ exact Hnode_parent_other. }
                     2:{ exact Hnode_parent_not_child. }
                     rewrite Hswap_other_cost.
                     2:{ lia. }
                     2:{ exact Hnode_neq_parent. }
                     2:{ exact Hnode_not_child. }
                     apply Hexcept_ord.
                     lia.
              }
              { unfold PushHoleChildrenPreservedPair.
           intros node [Hnode_pos [Hnode_bound Hnode_parent]].
	           destruct (Z.eq_dec parent 0) as [Hparent_zero | Hparent_nonzero].
	           ++ subst parent.
	              assert (Hhp0 : HeapParent 0 = 0) by (vm_compute; reflexivity).
	              replace (Znth (HeapParent (HeapParent child)) cost_swapped 0)
	                with (Znth 0 cost_swapped 0).
	              2:{ rewrite Hparent_zero, Hhp0. reflexivity. }
	              replace (Znth 0 cost_swapped 0) with (Znth child cost_cur 0).
	              2:{ symmetry.
	                  transitivity (Znth (HeapParent child) cost_swapped 0).
	                  - rewrite Hparent_zero. reflexivity.
	                  - exact Hswap_parent_cost. }
	              destruct (Z.eq_dec node child) as [Hnode_child | Hnode_not_child].
	              ** subst node.
	                 rewrite Hswap_child_cost.
	                 lia.
              ** rewrite (Hswap_other_cost node).
                 2:{ rewrite Hcost_cur_len; lia. }
                 2:{ lia. }
                 2:{ exact Hnode_not_child. }
	                 assert (Hroot_node : Znth 0 cost_cur 0 <= Znth node cost_cur 0).
	                 { replace (Znth 0 cost_cur 0)
	                     with (Znth (HeapParent node) cost_cur 0).
		                   2:{ rewrite Hnode_parent, Hparent_zero. reflexivity. }
		                   apply Hexcept_ord.
		                   lia. }
		                 assert (Hchild_root : Znth child cost_cur 0 <= Znth 0 cost_cur 0).
		                 { replace (Znth 0 cost_cur 0)
		                     with (Znth (HeapParent child) cost_cur 0).
		                   - lia.
		                   - rewrite Hparent_zero. reflexivity. }
		                 lia.
           ++ assert (Hgp_parent :
                 Znth (HeapParent parent) cost_cur 0 <= Znth parent cost_cur 0).
              { apply Hexcept_ord. lia. }
              destruct (heap_parent_bounds_pos_pair parent) as [Hgp0 Hgplt]; try lia.
	              rewrite Hswap_other_cost.
	              2:{ lia. }
	              2:{ intro Heq; lia. }
	              2:{ intro Heq; lia. }
              destruct (Z.eq_dec node child) as [Hnode_child | Hnode_not_child].
              ** subst node.
                 rewrite Hswap_child_cost.
                 exact Hgp_parent.
              ** assert (Hnode_not_parent : node <> parent).
                 { intro Heq.
                   subst node.
                   destruct (heap_parent_bounds_pos_pair parent) as [_ Hparent_lt]; try lia. }
                 rewrite Hswap_other_cost.
                 2:{ lia. }
                 2:{ exact Hnode_not_parent. }
                 2:{ exact Hnode_not_child. }
                 assert (Hparent_node : Znth parent cost_cur 0 <= Znth node cost_cur 0).
                 { rewrite <- Hnode_parent.
                   apply Hexcept_ord.
                   lia. }
                 lia. }
Qed.

Lemma HeapEntriesPair_replace_tail_snoc :
  forall cost_before vertex_before n cost vertex,
    0 <= n ->
    n < Zlength cost_before ->
    n < Zlength vertex_before ->
    HeapEntriesPair
      (replace_Znth n cost cost_before)
      (replace_Znth n vertex vertex_before)
      (n + 1) =
    HeapEntriesPair cost_before vertex_before n ++ [(cost, vertex)].
Proof.
  intros cost_before vertex_before n cost vertex Hn Hcost_len Hvertex_len.
  unfold HeapEntriesPair.
  rewrite Zrange_0_snoc by exact Hn.
  rewrite map_app.
  simpl.
  replace
    (map
       (fun idx : Z =>
          (Znth idx (replace_Znth n cost cost_before) 0,
           Znth idx (replace_Znth n vertex vertex_before) 0))
       (Zrange 0 n))
    with
    (map
       (fun idx : Z => (Znth idx cost_before 0, Znth idx vertex_before 0))
       (Zrange 0 n)).
  - replace
      (Znth n (replace_Znth n cost cost_before) 0,
       Znth n (replace_Znth n vertex vertex_before) 0)
      with (cost, vertex).
    + reflexivity.
    + rewrite Znth_replace_Znth_same_local by lia.
      rewrite Znth_replace_Znth_same_local by lia.
      reflexivity.
  - apply map_ext_in.
    intros idx Hidx.
      rewrite <- In_Zrange in Hidx.
    f_equal.
    + symmetry. apply Znth_replace_Znth_diff_local; lia.
    + symmetry. apply Znth_replace_Znth_diff_local; lia.
Qed.

Lemma HeapEntriesPair_snoc :
  forall cost_before vertex_before n cost vertex,
    0 <= n ->
    Zlength cost_before = n ->
    Zlength vertex_before = n ->
    HeapEntriesPair
      (cost_before ++ [cost])
      (vertex_before ++ [vertex])
      (n + 1) =
    HeapEntriesPair cost_before vertex_before n ++ [(cost, vertex)].
Proof.
  intros cost_before vertex_before n cost vertex Hn Hcost_len Hvertex_len.
  unfold HeapEntriesPair.
  rewrite Zrange_0_snoc by exact Hn.
  rewrite map_app.
  simpl.
  replace
    (map
       (fun idx : Z =>
          (Znth idx (cost_before ++ [cost]) 0,
           Znth idx (vertex_before ++ [vertex]) 0))
       (Zrange 0 n))
    with
    (map
       (fun idx : Z => (Znth idx cost_before 0, Znth idx vertex_before 0))
       (Zrange 0 n)).
  - replace
      (Znth n (cost_before ++ [cost]) 0,
       Znth n (vertex_before ++ [vertex]) 0)
      with (cost, vertex).
    + reflexivity.
    + rewrite app_Znth2 by lia.
      rewrite app_Znth2 by lia.
      replace (n - Zlength cost_before) with 0 by lia.
      replace (n - Zlength vertex_before) with 0 by lia.
      reflexivity.
  - apply map_ext_in.
    intros idx Hidx.
    rewrite <- In_Zrange in Hidx.
    f_equal.
    + rewrite app_Znth1 by lia. reflexivity.
    + rewrite app_Znth1 by lia. reflexivity.
Qed.

Lemma MinHeapPrefixPair_snoc :
  forall cost_before vertex_before n cost vertex,
    Zlength cost_before = n ->
    Zlength vertex_before = n ->
    MinHeapPrefixPair cost_before vertex_before n ->
    MinHeapPrefixPair
      (cost_before ++ [cost])
      (vertex_before ++ [vertex])
      n.
Proof.
  intros cost_before vertex_before n cost vertex Hcost_len Hvertex_len Hheap.
  unfold MinHeapPrefixPair in *.
  destruct Hheap as [Hn0 [Hcost_bound [Hvertex_bound Hord]]].
  split; [exact Hn0|].
  split; [rewrite Zlength_app_cons, Hcost_len; lia|].
  split; [rewrite Zlength_app_cons, Hvertex_len; lia|].
  intros child Hchild.
  destruct (heap_parent_bounds_pos_pair child) as [Hparent0 Hparentlt]; try lia.
  rewrite (app_Znth1 0 cost_before [cost] (HeapParent child)) by lia.
  rewrite (app_Znth1 0 cost_before [cost] child) by lia.
  apply Hord. exact Hchild.
Qed.

Lemma push_source_pair_init_at_tail :
  forall before base_cost base_vertex n cost vertex,
    heap_representation_pair before base_cost base_vertex n ->
    PushSourcePair
      (base_cost ++ [cost])
      (base_vertex ++ [vertex])
      before n cost vertex.
Proof.
  intros before base_cost base_vertex n cost vertex Hrep.
  unfold heap_representation_pair in Hrep.
  destruct Hrep as [Hn0 [Hcost_bound [Hvertex_bound [Hsize [Hrel Hheap]]]]].
  unfold PushSourcePair.
  split; [rewrite Zlength_app_cons, Hcost_bound; lia|].
  split; [rewrite Zlength_app_cons, Hvertex_bound; lia|].
  split.
  - rewrite HeapEntriesPair_snoc by lia.
    unfold heap_relation_pair in Hrel.
    rewrite Hrel.
    apply Permutation_sym.
    apply Permutation_cons_append.
  - apply MinHeapPrefixPair_snoc; auto.
Qed.

Lemma push_loop_pair_init_at_tail :
  forall written_cost written_vertex before n cost vertex,
    PushSourcePair written_cost written_vertex before n cost vertex ->
    Znth n written_cost 0 = cost ->
    Znth n written_vertex 0 = vertex ->
    PushLoopStatePair
      written_cost written_vertex
      written_cost written_vertex
      n n cost vertex.
Proof.
  intros written_cost written_vertex before n cost vertex
         Hsource Hcost_tail Hvertex_tail.
  unfold PushSourcePair in Hsource.
  destruct Hsource as [Hwritten_cost_len [Hwritten_vertex_len [Hperm Hheap]]].
  destruct Hheap as [Hn0 [Hcost_heap_len [Hvertex_heap_len Hord]]].
  unfold PushLoopStatePair.
  split; [lia|].
  split; [exact Hwritten_cost_len|].
  split; [exact Hwritten_vertex_len|].
  split; [exact Hwritten_cost_len|].
  split; [exact Hwritten_vertex_len|].
  split; [lia|].
  split; [lia|].
  split; [exact Hcost_tail|].
  split; [exact Hvertex_tail|].
  split; [apply Permutation_refl|].
  split.
  - unfold HeapOrderExceptUpPair.
    split; [lia|].
    split; [lia|].
    intros node [Hnode_pos [Hnode_bound Hnode_neq]].
    apply Hord.
    lia.
  - unfold PushHoleChildrenPreservedPair.
    intros node [Hnode_pos [Hnode_bound Hparent]].
    destruct (heap_parent_bounds_pos_pair node Hnode_pos) as [_ Hparent_lt].
    rewrite Hparent in Hparent_lt.
    lia.
Qed.

Lemma min_heap_prefix_pair_root_min_for_push : forall cost vertex n,
  0 < n ->
  MinHeapPrefixPair cost vertex n ->
  PrefixMinValuePair
    (HeapEntriesPair cost vertex n)
    (Znth 0 cost 0)
    (Znth 0 vertex 0).
Proof.
  intros cost vertex n Hn [Hn0 [Hcost_len [Hvertex_len Hord]]].
  unfold PrefixMinValuePair, min_object_of_subset.
  split.
  - unfold HeapEntriesPair.
    replace (Znth 0 cost 0, Znth 0 vertex 0) with
      ((fun idx : Z => (Znth idx cost 0, Znth idx vertex 0)) 0) by reflexivity.
    apply (in_map
      (fun idx : Z => (Znth idx cost 0, Znth idx vertex 0))
      (Zrange 0 n) 0).
    rewrite <- In_Zrange.
    lia.
  - intros [c v] Hin.
    change (In (c, v) (HeapEntriesPair cost vertex n)) in Hin.
    unfold HeapEntriesPair in Hin.
    rewrite in_map_iff in Hin.
    destruct Hin as [idx [Hentry Hidx_range]].
    rewrite <- In_Zrange in Hidx_range.
    inversion Hentry; subst c v; clear Hentry.
    simpl.
    enough (Znth 0 cost 0 <= Znth idx cost 0) by exact H.
    refine (well_founded_induction_type
      (A := Z) (R := fun x y => 0 <= x < y)
      (Z.lt_wf 0)
      (fun y => 0 <= y < n -> Znth 0 cost 0 <= Znth y cost 0)
      _ idx _).
    + intros y IH [Hy0 Hylt].
      destruct (Z.eq_dec y 0) as [-> | Hyneq].
      * lia.
      * assert (Hy_pos : 0 < y) by lia.
        destruct (heap_parent_bounds_pos_pair y Hy_pos) as [Hparent0 Hparentlt].
        assert (Hedge : Znth (HeapParent y) cost 0 <= Znth y cost 0).
        { apply Hord. lia. }
        assert (Hroot_parent : Znth 0 cost 0 <= Znth (HeapParent y) cost 0).
        { apply IH; lia. }
        lia.
    + lia.
Qed.

Lemma push_loop_pair_stop_to_result :
  forall before written_cost written_vertex cost_cur vertex_cur n child parent cost vertex,
    PushSourcePair written_cost written_vertex before n cost vertex ->
    PushLoopStatePair
      written_cost written_vertex cost_cur vertex_cur n child cost vertex ->
    0 < child ->
    parent = HeapParent child ->
    Znth parent cost_cur 0 <= Znth child cost_cur 0 ->
    PushResultPair before cost_cur vertex_cur n cost vertex.
Proof.
  intros before written_cost written_vertex cost_cur vertex_cur n child parent cost vertex
         Hsource Hstate Hchild_pos Hparent_eq Hle.
  subst parent.
  unfold PushSourcePair in Hsource.
  destruct Hsource as [Hwritten_cost_source [Hwritten_vertex_source [Hsource_perm _]]].
  unfold PushLoopStatePair in Hstate.
  destruct Hstate as [Hn0 Hstate].
  destruct Hstate as [Hwritten_cost_len Hstate].
  destruct Hstate as [Hwritten_vertex_len Hstate].
  destruct Hstate as [Hcost_cur_len Hstate].
  destruct Hstate as [Hvertex_cur_len Hstate].
  destruct Hstate as [Hchild0 Hstate].
  destruct Hstate as [Hchildn Hstate].
  destruct Hstate as [Hcost_child Hstate].
  destruct Hstate as [Hvertex_child Hstate].
  destruct Hstate as [Hperm [Hexcept _]].
  assert (Hheap_cur : MinHeapPrefixPair cost_cur vertex_cur (n + 1)).
  {
    unfold MinHeapPrefixPair.
    split; [lia|].
    split; [lia|].
    split; [lia|].
    intros node [Hnode_pos Hnode_bound].
    destruct (Z.eq_dec node child) as [-> | Hnode_neq].
    - exact Hle.
    - apply Hexcept.
      lia.
  }
  unfold PushResultPair.
  split; [lia|].
  split; [exact Hcost_cur_len|].
  split; [exact Hvertex_cur_len|].
  split.
  - eapply Permutation_trans.
    + apply Permutation_sym. exact Hperm.
    + exact Hsource_perm.
  - exact Hheap_cur.
Qed.

Lemma push_loop_pair_root_to_result :
  forall before written_cost written_vertex cost_cur vertex_cur n child cost vertex,
    PushSourcePair written_cost written_vertex before n cost vertex ->
    PushLoopStatePair
      written_cost written_vertex cost_cur vertex_cur n child cost vertex ->
    child = 0 ->
    PushResultPair before cost_cur vertex_cur n cost vertex.
Proof.
  intros before written_cost written_vertex cost_cur vertex_cur n child cost vertex
         Hsource Hstate Hchild_eq.
  subst child.
  unfold PushSourcePair in Hsource.
  destruct Hsource as [Hwritten_cost_source [Hwritten_vertex_source [Hsource_perm _]]].
  unfold PushLoopStatePair in Hstate.
  destruct Hstate as [Hn0 Hstate].
  destruct Hstate as [Hwritten_cost_len Hstate].
  destruct Hstate as [Hwritten_vertex_len Hstate].
  destruct Hstate as [Hcost_cur_len Hstate].
  destruct Hstate as [Hvertex_cur_len Hstate].
  destruct Hstate as [Hchild0 Hstate].
  destruct Hstate as [Hchildn Hstate].
  destruct Hstate as [Hcost_child Hstate].
  destruct Hstate as [Hvertex_child Hstate].
  destruct Hstate as [Hperm [Hexcept _]].
  unfold HeapOrderExceptUpPair in Hexcept.
  destruct Hexcept as [_ [_ Hexcept_ord]].
  assert (Hheap_cur : MinHeapPrefixPair cost_cur vertex_cur (n + 1)).
  {
    unfold MinHeapPrefixPair.
    split; [lia|].
    split; [lia|].
    split; [lia|].
    intros node [Hnode_pos Hnode_bound].
    apply Hexcept_ord.
    lia.
  }
  unfold PushResultPair.
  split; [lia|].
  split; [exact Hcost_cur_len|].
  split; [exact Hvertex_cur_len|].
  split.
  - eapply Permutation_trans.
    + apply Permutation_sym. exact Hperm.
    + exact Hsource_perm.
  - exact Hheap_cur.
Qed.

Lemma push_result_pair_representation :
  forall before result_cost result_vertex size cost vertex,
    PushResultPair before result_cost result_vertex size cost vertex ->
    heap_representation_pair
      (heap_entry_set_insert before cost vertex)
      result_cost result_vertex (size + 1).
Proof.
  intros before result_cost result_vertex size cost vertex Hresult.
  unfold PushResultPair in Hresult.
  destruct Hresult as [Hsize [Hcost_len [Hvertex_len [Hperm Hheap]]]].
  unfold heap_representation_pair.
  split; [lia|].
  split; [exact Hcost_len|].
  split; [exact Hvertex_len|].
  split.
  - unfold heap_entry_set_insert.
    rewrite multiset_insert_size.
    assert (Hbefore_size : multiset_size before = size).
    {
      pose proof (Permutation_length Hperm) as Hlen.
      assert (Hentries_len :
        Z.of_nat (length (HeapEntriesPair result_cost result_vertex (size + 1))) =
        size + 1).
      {
        rewrite <- Zlength_correct.
        rewrite Zlength_HeapEntriesPair by lia.
        reflexivity.
      }
      unfold multiset_size.
      rewrite Zlength_correct.
      pose proof (f_equal Z.of_nat Hlen) as HlenZ.
      simpl in HlenZ.
      lia.
    }
    rewrite Hbefore_size.
    lia.
  - split.
    + unfold heap_relation_pair, heap_entry_set_insert.
      rewrite multiset_insert_mlist.
      apply Permutation_sym.
      exact Hperm.
    + exact Hheap.
Qed.

Lemma heap_representation_pair_to_priority_queue_prefix_pair :
  forall S cost vertex size,
    heap_representation_pair S cost vertex size ->
    PriorityQueuePrefixPair cost vertex size
      (HeapEntriesPair cost vertex size).
Proof.
  intros S cost vertex size Hrep.
  unfold heap_representation_pair in Hrep.
  destruct Hrep as [Hsize [Hcost_len [Hvertex_len [_ [_ Hheap]]]]].
  unfold PriorityQueuePrefixPair.
  split; [reflexivity|].
  split; [exact Hheap|].
  intros Hpos.
  apply min_heap_prefix_pair_root_min_for_push; try lia; exact Hheap.
Qed.

Lemma heap_representation_pair_root_prefix_min :
  forall S cost vertex size,
    0 < size ->
    heap_representation_pair S cost vertex size ->
    PrefixMinValuePair
      (HeapEntriesPair cost vertex size)
      (Znth 0 cost 0)
      (Znth 0 vertex 0).
Proof.
  intros S cost vertex size Hsize Hrep.
  unfold heap_representation_pair in Hrep.
  destruct Hrep as [_ [_ [_ [_ [_ Hheap]]]]].
  apply min_heap_prefix_pair_root_min_for_push; try lia.
  exact Hheap.
Qed.

Lemma heap_representation_pair_root_entry_set_minimum :
  forall S cost vertex size,
    0 < size ->
    heap_representation_pair S cost vertex size ->
    heap_entry_set_minimum S (Znth 0 cost 0) (Znth 0 vertex 0).
Proof.
  intros S cost vertex size Hsize Hrep.
  pose proof (heap_representation_pair_root_prefix_min
    S cost vertex size Hsize Hrep) as Hmin.
  unfold heap_representation_pair in Hrep.
  destruct Hrep as [_ [_ [_ [_ [Hrel _]]]]].
  unfold heap_relation_pair in Hrel.
  unfold PrefixMinValuePair, min_object_of_subset in Hmin.
  destruct Hmin as [Hin Hle].
  unfold heap_entry_set_minimum.
  split.
  - eapply Permutation_in.
    + apply Permutation_sym. exact Hrel.
    + exact Hin.
  - intros cost' vertex' HinS.
    specialize (Hle (cost', vertex')).
    assert (HinEntries :
      In (cost', vertex') (HeapEntriesPair cost vertex size)).
    {
      eapply Permutation_in; [exact Hrel | exact HinS].
    }
    specialize (Hle HinEntries).
    simpl in Hle.
    exact Hle.
Qed.

Lemma heap_representation_pair_insert_to_push_result_pair :
  forall entries cost_before vertex_before result_cost result_vertex
         size cost vertex,
    PriorityQueuePrefixPair cost_before vertex_before size entries ->
    heap_representation_pair
      (heap_entry_set_insert (heap_entries_to_set entries) cost vertex)
      result_cost result_vertex (size + 1) ->
    PushResultPair
      (heap_entries_to_set entries) result_cost result_vertex size cost vertex.
Proof.
  intros entries cost_before vertex_before result_cost result_vertex
         size cost vertex Hpq Hrep.
  unfold PriorityQueuePrefixPair in Hpq.
  destruct Hpq as [_ [Hheap_before _]].
  unfold MinHeapPrefixPair in Hheap_before.
  destruct Hheap_before as [Hsize_nonneg _].
  unfold heap_representation_pair in Hrep.
  destruct Hrep as [_ [Hcost_len [Hvertex_len [_ [Hperm Hheap]]]]].
  unfold PushResultPair.
  split; [lia|].
  split; [exact Hcost_len|].
  split; [exact Hvertex_len|].
  split.
  - unfold heap_relation_pair, heap_entry_set_insert in Hperm.
    rewrite multiset_insert_mlist in Hperm.
    apply Permutation_sym.
    exact Hperm.
  - exact Hheap.
Qed.

Lemma heap_entries_vertex_range_pair_insert_representation :
  forall bound entries result_cost result_vertex size cost vertex,
    HeapEntriesVertexRangePair bound entries ->
    0 <= vertex < bound ->
    heap_representation_pair
      (heap_entry_set_insert (heap_entries_to_set entries) cost vertex)
      result_cost result_vertex size ->
    HeapEntriesVertexRangePair bound
      (HeapEntriesPair result_cost result_vertex size).
Proof.
  intros bound entries result_cost result_vertex size cost vertex
         Hrange Hvertex_range Hrep.
  unfold HeapEntriesVertexRangePair in *.
  intros c v Hin.
  unfold heap_representation_pair, heap_relation_pair in Hrep.
  destruct Hrep as [_ [_ [_ [_ [Hperm _]]]]].
  unfold heap_entry_set_insert in Hperm.
  rewrite multiset_insert_mlist in Hperm.
  pose proof (Permutation_in (c, v) (Permutation_sym Hperm) Hin) as Hin_insert.
  simpl in Hin_insert.
  destruct Hin_insert as [Heq | Hin_old].
  - inversion Heq; subst; lia.
  - change (In (c, v) entries) in Hin_old.
    eapply Hrange; eauto.
Qed.

Lemma heap_entries_vertex_range_pair_of_representation :
  forall bound entries cost vertex size,
    HeapEntriesVertexRangePair bound entries ->
    heap_representation_pair (heap_entries_to_set entries) cost vertex size ->
    HeapEntriesVertexRangePair bound (HeapEntriesPair cost vertex size).
Proof.
  intros bound entries cost vertex size Hrange Hrep.
  unfold HeapEntriesVertexRangePair in *.
  intros c v Hin.
  unfold heap_representation_pair, heap_relation_pair, heap_entries_to_set,
    list_to_multiset in Hrep.
  destruct Hrep as [_ [_ [_ [_ [Hperm _]]]]].
  pose proof (Permutation_in (c, v) (Permutation_sym Hperm) Hin) as Hin_entries.
  eapply Hrange; eauto.
Qed.

Lemma push_result_pair_empty_singleton_of_representation :
  forall S cost vertex,
    mlist S = ((0, 0) :: nil)%list ->
    heap_representation_pair S cost vertex 1 ->
    PushResultPair empty_heap_entry_set cost vertex 0 0 0.
Proof.
  intros S cost vertex HS Hrep.
  unfold heap_representation_pair in Hrep.
  destruct Hrep as [_ [Hcost_len [Hvertex_len [_ [Hrel Hheap]]]]].
  unfold PushResultPair.
  split; [lia|].
  split; [exact Hcost_len|].
  split; [exact Hvertex_len|].
  split.
  - unfold heap_relation_pair in Hrel.
    rewrite empty_heap_entry_set_mlist.
    replace (0 + 1) with 1 by lia.
    assert (Hrel' : Permutation ((0, 0) :: nil) (HeapEntriesPair cost vertex 1)).
    { rewrite <- HS. exact Hrel. }
    apply Permutation_sym.
    exact Hrel'.
  - exact Hheap.
Qed.

Lemma heap_entries_vertex_range_pair_mono :
  forall bound1 bound2 entries,
    bound1 <= bound2 ->
    HeapEntriesVertexRangePair bound1 entries ->
    HeapEntriesVertexRangePair bound2 entries.
Proof.
  intros bound1 bound2 entries Hbound Hrange.
  unfold HeapEntriesVertexRangePair in *.
  intros cost vertex Hin.
  specialize (Hrange cost vertex Hin).
  lia.
Qed.

Definition PopResultPairCore
    (cost_before vertex_before cost_after vertex_after : list Z)
    (n cost vertex : Z) : Prop :=
  1 <= n /\
  Zlength cost_before = n /\
  Zlength vertex_before = n /\
  Zlength cost_after = n /\
  Zlength vertex_after = n /\
  PriorityQueuePrefixPair
    cost_before vertex_before n
    (HeapEntriesPair cost_before vertex_before n) /\
  PrefixMinValuePair
    (HeapEntriesPair cost_before vertex_before n) cost vertex /\
  cost = Znth 0 cost_before 0 /\
  vertex = Znth 0 vertex_before 0 /\
  Znth (n - 1) cost_after 0 = cost /\
  Znth (n - 1) vertex_after 0 = vertex /\
  PriorityQueuePrefixPair
    cost_after vertex_after (n - 1)
    (HeapEntriesPair cost_after vertex_after (n - 1)) /\
  Permutation
    (HeapEntriesPair cost_before vertex_before n)
    ((cost, vertex) :: HeapEntriesPair cost_after vertex_after (n - 1)).

Definition PopResultPair
    (S_before : HeapEntrySet)
    (cost_before vertex_before cost_after vertex_after : list Z)
    (n cost vertex : Z) : Prop :=
  heap_representation_pair S_before cost_before vertex_before n /\
  heap_entry_set_minimum S_before cost vertex /\
  PopResultPairCore cost_before vertex_before cost_after vertex_after
    n cost vertex.

Lemma PopResultPair_rebase_to_entries :
  forall S_before cost_before vertex_before cost_after vertex_after n cost vertex,
    PopResultPair S_before
      cost_before vertex_before cost_after vertex_after n cost vertex ->
    PopResultPair
      (heap_entries_to_set (HeapEntriesPair cost_before vertex_before n))
      cost_before vertex_before cost_after vertex_after n cost vertex.
Proof.
  intros S_before cost_before vertex_before cost_after vertex_after n cost vertex Hpop.
  unfold PopResultPair in Hpop.
  destruct Hpop as [_ [_ Hcore]].
  pose proof Hcore as Hcore_full.
  unfold PopResultPairCore in Hcore.
  destruct Hcore as
    [Hn [Hcost_before_len [Hvertex_before_len
    [Hcost_after_len [Hvertex_after_len
    [Hpq [Hprefix_min Hrest]]]]]]].
  unfold PopResultPair.
  split.
  - unfold heap_representation_pair, heap_relation_pair,
      heap_entries_to_set, list_to_multiset.
    destruct Hpq as [Hentries [Hheap _]].
    split; [lia|].
    split; [exact Hcost_before_len|].
    split; [exact Hvertex_before_len|].
    split.
    + unfold multiset_size.
      simpl.
      rewrite Zlength_HeapEntriesPair by lia.
      reflexivity.
    + split.
      * simpl.
        reflexivity.
      * exact Hheap.
  - split.
    + apply PrefixMinValuePair_heap_entry_set_minimum.
      exact Hprefix_min.
    + exact Hcore_full.
Qed.

Lemma pop_after_singleton_push_pair :
  forall before cost_before vertex_before cost_after vertex_after
         cost vertex out_cost out_vertex,
    mlist before = nil ->
    PushResultPair before cost_before vertex_before 0 cost vertex ->
    PopResultPair before cost_before vertex_before cost_after vertex_after
      1 out_cost out_vertex ->
    out_cost = cost /\ out_vertex = vertex.
Proof.
  intros before cost_before vertex_before cost_after vertex_after
         cost vertex out_cost out_vertex Hempty Hpush Hpop.
  unfold PushResultPair in Hpush.
  destruct Hpush as [_ [Hcost_len [Hvertex_len [Hperm _]]]].
  rewrite Hempty in Hperm.
  simpl in Hperm.
  unfold PopResultPair in Hpop.
  destruct Hpop as [_ [_ Hpop]].
  unfold PopResultPairCore in Hpop.
  destruct Hpop as [_ [_ [_ [_ [_ [_ [_ [Hout_cost [Hout_vertex _]]]]]]]]].
  subst out_cost out_vertex.
  unfold HeapEntriesPair in Hperm.
  simpl in Hperm.
  assert (Hin :
    In (Znth 0 cost_before 0, Znth 0 vertex_before 0) [(cost, vertex)]).
  { eapply Permutation_in; [exact Hperm | left; reflexivity]. }
  simpl in Hin.
  destruct Hin as [Heq | []].
  inversion Heq; subst; auto.
Qed.

Lemma pop_after_singleton_push_pair_entries :
  forall cost_before vertex_before cost_after vertex_after out_cost out_vertex,
    PushResultPair empty_heap_entry_set cost_before vertex_before 0 0 0 ->
    PopResultPair
      (heap_entries_to_set (HeapEntriesPair cost_before vertex_before 1))
      cost_before vertex_before cost_after vertex_after 1 out_cost out_vertex ->
    out_cost = 0 /\ out_vertex = 0.
Proof.
  intros cost_before vertex_before cost_after vertex_after out_cost out_vertex
         Hpush Hpop.
  unfold PopResultPair in Hpop.
  destruct Hpop as [_ [_ Hcore]].
  unfold PopResultPairCore in Hcore.
  destruct Hcore as [_ [_ [_ [_ [_ [_ [_ [Hout_cost [Hout_vertex _]]]]]]]]].
  subst out_cost out_vertex.
  unfold PushResultPair in Hpush.
  destruct Hpush as [_ [_ [_ [Hperm _]]]].
  unfold empty_heap_entry_set, multiset_empty in Hperm.
  simpl in Hperm.
  assert (Hin :
    In (Znth 0 cost_before 0, Znth 0 vertex_before 0) ((0, 0) :: nil)%list).
  { eapply Permutation_in; [exact Hperm | left; reflexivity]. }
  simpl in Hin.
  destruct Hin as [Heq | []].
  inversion Heq; subst; auto.
Qed.

Lemma pop_after_singleton_push_pair_any_set :
  forall S cost_before vertex_before cost_after vertex_after out_cost out_vertex,
    PushResultPair empty_heap_entry_set cost_before vertex_before 0 0 0 ->
    PopResultPair S cost_before vertex_before cost_after vertex_after
      1 out_cost out_vertex ->
    out_cost = 0 /\ out_vertex = 0.
Proof.
  intros S cost_before vertex_before cost_after vertex_after out_cost out_vertex
         Hpush Hpop.
  unfold PopResultPair in Hpop.
  destruct Hpop as [_ [_ Hcore]].
  unfold PopResultPairCore in Hcore.
  destruct Hcore as [_ [_ [_ [_ [_ [_ [_ [Hout_cost [Hout_vertex _]]]]]]]]].
  subst out_cost out_vertex.
  unfold PushResultPair in Hpush.
  destruct Hpush as [_ [_ [_ [Hperm _]]]].
  rewrite empty_heap_entry_set_mlist in Hperm.
  assert (Hin :
    In (Znth 0 cost_before 0, Znth 0 vertex_before 0) ((0, 0) :: nil)%list).
  { eapply Permutation_in; [exact Hperm | left; reflexivity]. }
  simpl in Hin.
  destruct Hin as [Heq | []].
  inversion Heq; subst; auto.
Qed.

Lemma pop_result_pair_singleton :
  forall l_cost l_vertex heap_entries root_cost out_vertex,
    Zlength l_cost = 1 ->
    Zlength l_vertex = 1 ->
    root_cost = Znth 0 l_cost 0 ->
    out_vertex = Znth 0 l_vertex 0 ->
    PriorityQueuePrefixPair l_cost l_vertex 1 heap_entries ->
    PopResultPair (heap_entries_to_set heap_entries)
      l_cost l_vertex l_cost l_vertex 1 root_cost out_vertex.
Proof.
  intros l_cost l_vertex heap_entries root_cost out_vertex
         Hcost_len Hvertex_len Hroot Hvertex Hpq.
  subst root_cost out_vertex.
  destruct Hpq as [Hentries [Hheap Hmin]].
  unfold PopResultPair.
  split.
  { unfold heap_representation_pair, heap_relation_pair, heap_entries_to_set,
      list_to_multiset.
    split; [lia|].
    split; [exact Hcost_len|].
    split; [exact Hvertex_len|].
    split.
    { unfold multiset_size.
      cbn.
      rewrite Hentries.
      rewrite Zlength_HeapEntriesPair by lia.
      reflexivity. }
    split.
    { simpl. rewrite Hentries. reflexivity. }
    exact Hheap. }
  split.
  { unfold heap_entry_set_minimum, heap_entries_to_set, list_to_multiset.
    change (In (Znth 0 l_cost 0, Znth 0 l_vertex 0) heap_entries /\
      (forall cost' vertex',
        In (cost', vertex') heap_entries ->
        Znth 0 l_cost 0 <= cost')).
    specialize (Hmin ltac:(lia)).
    unfold PrefixMinValuePair, min_object_of_subset in Hmin.
    destruct Hmin as [Hin Hle].
    split; [exact Hin|].
    intros cost' vertex' Hin'.
    specialize (Hle (cost', vertex') Hin').
    simpl in Hle.
    exact Hle. }
  unfold PopResultPairCore.
  split; [lia|].
  split; [exact Hcost_len|].
  split; [exact Hvertex_len|].
  split; [exact Hcost_len|].
  split; [exact Hvertex_len|].
  split.
  { unfold PriorityQueuePrefixPair.
    split; [reflexivity|].
    split; [exact Hheap|].
    intros Hpos.
    rewrite <- Hentries.
    apply Hmin; exact Hpos. }
  split.
  { rewrite <- Hentries.
    apply Hmin; lia. }
  split; [reflexivity|].
  split; [reflexivity|].
  split; [replace (1 - 1) with 0 by lia; reflexivity|].
  split; [replace (1 - 1) with 0 by lia; reflexivity|].
  split.
  { replace (1 - 1) with 0 by lia.
    unfold PriorityQueuePrefixPair.
    split; [reflexivity|].
    split.
    - unfold MinHeapPrefixPair.
      repeat split; try lia.
    - intros Hcontra; lia. }
  unfold HeapEntriesPair.
  simpl.
  reflexivity.
Qed.

Lemma pop_result_pair_singleton_from_representation :
  forall S_before l_cost l_vertex root_cost out_vertex,
    Zlength l_cost = 1 ->
    Zlength l_vertex = 1 ->
    root_cost = Znth 0 l_cost 0 ->
    out_vertex = Znth 0 l_vertex 0 ->
    heap_representation_pair S_before l_cost l_vertex 1 ->
    PrefixMinValuePair (HeapEntriesPair l_cost l_vertex 1) root_cost out_vertex ->
    heap_entry_set_minimum S_before root_cost out_vertex ->
    PopResultPair S_before
      l_cost l_vertex l_cost l_vertex 1 root_cost out_vertex.
Proof.
  intros S_before l_cost l_vertex root_cost out_vertex
         Hcost_len Hvertex_len Hroot Hvertex Hrep Hmin Hset_min.
  unfold heap_representation_pair in Hrep.
  destruct Hrep as [Hsize [Hcost_len_rep [Hvertex_len_rep [Hmsize [Hrel Hheap]]]]].
  subst root_cost out_vertex.
  unfold PopResultPair.
  split.
  { unfold heap_representation_pair.
    split; [exact Hsize|].
    split; [exact Hcost_len_rep|].
    split; [exact Hvertex_len_rep|].
    split; [exact Hmsize|].
    split; [exact Hrel|].
    exact Hheap. }
  split.
  { exact Hset_min. }
  unfold PopResultPairCore.
  split; [lia|].
  split; [exact Hcost_len|].
  split; [exact Hvertex_len|].
  split; [exact Hcost_len|].
  split; [exact Hvertex_len|].
  split.
  { unfold PriorityQueuePrefixPair.
    split; [reflexivity|].
    split; [exact Hheap|].
    intros _.
    exact Hmin. }
  split; [exact Hmin|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [replace (1 - 1) with 0 by lia; reflexivity|].
  split; [replace (1 - 1) with 0 by lia; reflexivity|].
  split.
  { replace (1 - 1) with 0 by lia.
    unfold PriorityQueuePrefixPair.
    split; [reflexivity|].
    split.
    + unfold MinHeapPrefixPair.
      repeat split; try lia.
    + intros Hcontra; lia. }
  unfold HeapEntriesPair.
  simpl.
  reflexivity.
Qed.

Lemma heap_entry_set_remove_root_singleton_empty :
  forall S_before l_cost l_vertex root_cost out_vertex,
    Zlength l_cost = 1 ->
    Zlength l_vertex = 1 ->
    root_cost = Znth 0 l_cost 0 ->
    out_vertex = Znth 0 l_vertex 0 ->
    heap_representation_pair S_before l_cost l_vertex 1 ->
    mlist (heap_entry_set_remove S_before root_cost out_vertex) = nil.
Proof.
  intros S_before l_cost l_vertex root_cost out_vertex
         Hcost_len Hvertex_len Hroot Hvertex Hrep.
  subst root_cost out_vertex.
  unfold heap_representation_pair in Hrep.
  destruct Hrep as [_ [_ [_ [_ [Hrel _]]]]].
  unfold heap_relation_pair in Hrel.
  assert (Hpair : HeapEntriesPair l_cost l_vertex 1 =
      (Znth 0 l_cost 0, Znth 0 l_vertex 0) :: nil).
  { unfold HeapEntriesPair. simpl. reflexivity. }
  rewrite Hpair in Hrel.
  assert (Hlen : length (mlist S_before) = 1%nat).
  { rewrite (Permutation_length Hrel). reflexivity. }
  destruct (mlist S_before) as [| entry rest] eqn:Hml; simpl in Hlen;
    try discriminate.
  destruct rest as [| entry' rest']; simpl in Hlen; try discriminate.
  assert (Heq : entry = (Znth 0 l_cost 0, Znth 0 l_vertex 0)).
  { pose proof (Permutation_in entry Hrel (or_introl eq_refl)) as Hin.
    simpl in Hin.
    destruct Hin as [Hin | []].
    symmetry; exact Hin. }
  subst entry.
  unfold heap_entry_set_remove, list_to_multiset.
  rewrite Hml.
  simpl.
  destruct (Z.eq_dec (Znth 0 l_cost 0) (Znth 0 l_cost 0)) as [_ | Hneq].
  - destruct (Z.eq_dec (Znth 0 l_vertex 0) (Znth 0 l_vertex 0)) as [_ | Hneq].
    + reflexivity.
    + contradiction Hneq; reflexivity.
  - contradiction Hneq; reflexivity.
Qed.

Lemma heap_representation_pair_remove_root_singleton_empty :
  forall S_before l_cost l_vertex root_cost out_vertex,
    Zlength l_cost = 1 ->
    Zlength l_vertex = 1 ->
    root_cost = Znth 0 l_cost 0 ->
    out_vertex = Znth 0 l_vertex 0 ->
    heap_representation_pair S_before l_cost l_vertex 1 ->
    heap_representation_pair
      (heap_entry_set_remove S_before root_cost out_vertex) nil nil 0.
Proof.
  intros S_before l_cost l_vertex root_cost out_vertex
         Hcost_len Hvertex_len Hroot Hvertex Hrep.
  pose proof (heap_entry_set_remove_root_singleton_empty
    S_before l_cost l_vertex root_cost out_vertex
    Hcost_len Hvertex_len Hroot Hvertex Hrep) as Hempty.
  unfold heap_representation_pair.
  split; [lia|].
  split; [rewrite Zlength_nil; reflexivity|].
  split; [rewrite Zlength_nil; reflexivity|].
  split.
  { unfold multiset_size.
    rewrite Hempty.
    rewrite Zlength_nil.
    reflexivity. }
  split.
  { unfold heap_relation_pair, HeapEntriesPair.
    rewrite Hempty.
    simpl.
    constructor. }
  unfold MinHeapPrefixPair.
  split; [lia|].
  split; [rewrite Zlength_nil; lia|].
  split; [rewrite Zlength_nil; lia|].
  intros child [_ Hchild].
  unfold Znth.
  simpl.
  destruct (Z.to_nat (HeapParent child));
    destruct (Z.to_nat child);
    apply Z.le_refl.
Qed.

Lemma heap_root_vertex_range_singleton :
  forall bound l_cost l_vertex heap_entries root_cost out_vertex,
    root_cost = Znth 0 l_cost 0 ->
    out_vertex = Znth 0 l_vertex 0 ->
    PriorityQueuePrefixPair l_cost l_vertex 1 heap_entries ->
    HeapEntriesVertexRangePair bound heap_entries ->
    0 <= out_vertex < bound.
Proof.
  intros bound l_cost l_vertex heap_entries root_cost out_vertex
         Hroot Hvertex Hpq Hrange.
  subst root_cost out_vertex.
  unfold PriorityQueuePrefixPair in Hpq.
  destruct Hpq as [Hentries _].
  apply (Hrange (Znth 0 l_cost 0) (Znth 0 l_vertex 0)).
  rewrite Hentries.
  unfold HeapEntriesPair.
  simpl.
  left; reflexivity.
Qed.

Lemma heap_root_vertex_range_pair :
  forall bound n l_cost l_vertex heap_entries,
    0 < n ->
    PriorityQueuePrefixPair l_cost l_vertex n heap_entries ->
    HeapEntriesVertexRangePair bound heap_entries ->
    0 <= Znth 0 l_vertex 0 < bound.
Proof.
  intros bound n l_cost l_vertex heap_entries Hn Hpq Hrange.
  unfold PriorityQueuePrefixPair in Hpq.
  destruct Hpq as [Hentries _].
  apply (Hrange (Znth 0 l_cost 0) (Znth 0 l_vertex 0)).
  rewrite Hentries.
  unfold HeapEntriesPair.
  change (In ((fun idx => (Znth idx l_cost 0, Znth idx l_vertex 0)) 0)
    (map (fun idx => (Znth idx l_cost 0, Znth idx l_vertex 0)) (Zrange 0 n))).
  apply in_map.
  rewrite <- In_Zrange.
  lia.
Qed.

Lemma HeapEntriesPair_replace_root_prefix :
  forall cost vertex n,
    1 < n ->
    n <= Zlength cost ->
    n <= Zlength vertex ->
    HeapEntriesPair
      (replace_Znth 0 (Znth (n - 1) cost 0) cost)
      (replace_Znth 0 (Znth (n - 1) vertex 0) vertex)
      (n - 1) =
    (Znth (n - 1) cost 0, Znth (n - 1) vertex 0) ::
      sublist 1 (n - 1) (HeapEntriesPair cost vertex n).
Proof.
  intros cost vertex n Hn Hcost_len Hvertex_len.
  apply (proj2 (list_eq_ext _ _ (0, 0))).
  split.
  - rewrite Zlength_HeapEntriesPair by lia.
    rewrite Zlength_cons.
    rewrite Zlength_sublist by
      (rewrite Zlength_HeapEntriesPair by lia; lia).
    lia.
  - intros i Hi.
    rewrite Zlength_HeapEntriesPair in Hi by lia.
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + rewrite Znth_HeapEntriesPair by
        (rewrite ?Zlength_replace_Znth; lia).
      rewrite !Znth_replace_Znth_Same by lia.
      reflexivity.
    + rewrite Znth_HeapEntriesPair by
        (rewrite ?Zlength_replace_Znth; lia).
      rewrite !Znth_replace_Znth_Diff by lia.
      rewrite Znth_cons by lia.
      rewrite Znth_sublist by lia.
      rewrite Znth_HeapEntriesPair by lia.
      replace (i - 1 + 1) with i by lia.
      reflexivity.
Qed.

Lemma heap_entries_vertex_range_pair_replace_root_prefix :
  forall bound cost vertex n entries,
    1 < n ->
    Zlength cost = n ->
    Zlength vertex = n ->
    PriorityQueuePrefixPair cost vertex n entries ->
    HeapEntriesVertexRangePair bound entries ->
    HeapEntriesVertexRangePair bound
      (HeapEntriesPair
        (replace_Znth 0 (Znth (n - 1) cost 0) cost)
        (replace_Znth 0 (Znth (n - 1) vertex 0) vertex)
        (n - 1)).
Proof.
  intros bound cost vertex n entries Hn Hcost_len Hvertex_len Hpq Hrange.
  unfold PriorityQueuePrefixPair in Hpq.
  destruct Hpq as [Hentries _].
  unfold HeapEntriesVertexRangePair in *.
  intros c v Hin.
  unfold HeapEntriesPair in Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as [i [Heq Hi]].
  rewrite <- In_Zrange in Hi.
  destruct (Z.eq_dec i 0) as [-> | Hi0].
  - rewrite Znth_replace_Znth_same_local in Heq by lia.
    rewrite Znth_replace_Znth_same_local in Heq by lia.
    inversion Heq; subst c v; clear Heq.
    apply Hrange with (cost := Znth (n - 1) cost 0).
    rewrite Hentries.
    unfold HeapEntriesPair.
    rewrite in_map_iff.
    exists (n - 1).
    split; [reflexivity|].
    rewrite <- In_Zrange.
    lia.
  - rewrite Znth_replace_Znth_diff_local in Heq by lia.
    rewrite Znth_replace_Znth_diff_local in Heq by lia.
    inversion Heq; subst c v; clear Heq.
    apply Hrange with (cost := Znth i cost 0).
    rewrite Hentries.
    unfold HeapEntriesPair.
    rewrite in_map_iff.
    exists i.
    split; [reflexivity|].
    rewrite <- In_Zrange.
    lia.
Qed.

Lemma heap_entries_vertex_range_pair_swap :
  forall bound cost vertex n idx smallest,
    0 <= idx < n ->
    0 <= smallest < n ->
    n <= Zlength cost ->
    n <= Zlength vertex ->
    HeapEntriesVertexRangePair bound (HeapEntriesPair cost vertex n) ->
    HeapEntriesVertexRangePair bound
      (HeapEntriesPair
        (replace_Znth smallest (Znth idx cost 0)
          (replace_Znth idx (Znth smallest cost 0) cost))
        (replace_Znth smallest (Znth idx vertex 0)
          (replace_Znth idx (Znth smallest vertex 0) vertex))
        n).
Proof.
  intros bound cost vertex n idx smallest Hidx Hsmallest Hcost_len Hvertex_len Hrange.
  unfold HeapEntriesVertexRangePair in *.
  intros c v Hin.
  unfold HeapEntriesPair in Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as [i [Heq Hi]].
  rewrite <- In_Zrange in Hi.
  destruct (Z.eq_dec i smallest) as [His | Hnsmallest].
  - subst i.
    destruct (Z.eq_dec smallest idx) as [Hsame | Hdiff].
    + subst smallest.
      rewrite Znth_replace_Znth_same_local in Heq by
        (rewrite ?Zlength_replace_Znth_local; lia).
      rewrite Znth_replace_Znth_same_local in Heq by
        (rewrite ?Zlength_replace_Znth_local; lia).
      inversion Heq; subst c v; clear Heq.
      apply Hrange with (cost := Znth idx cost 0).
      unfold HeapEntriesPair.
      rewrite in_map_iff.
      exists idx.
      split; [reflexivity | rewrite <- In_Zrange; lia].
    + rewrite Znth_replace_Znth_same_local in Heq by
        (rewrite ?Zlength_replace_Znth_local; lia).
      rewrite Znth_replace_Znth_same_local in Heq by
        (rewrite ?Zlength_replace_Znth_local; lia).
      inversion Heq; subst c v; clear Heq.
      apply Hrange with (cost := Znth idx cost 0).
      unfold HeapEntriesPair.
      rewrite in_map_iff.
      exists idx.
      split; [reflexivity | rewrite <- In_Zrange; lia].
  - destruct (Z.eq_dec i idx) as [Hiidx | Hnidx].
    + subst i.
      rewrite Znth_replace_Znth_diff_local in Heq by
        (rewrite ?Zlength_replace_Znth_local; lia).
      rewrite Znth_replace_Znth_same_local in Heq by
        (rewrite ?Zlength_replace_Znth_local; lia).
      rewrite Znth_replace_Znth_diff_local in Heq by
        (rewrite ?Zlength_replace_Znth_local; lia).
      rewrite Znth_replace_Znth_same_local in Heq by
        (rewrite ?Zlength_replace_Znth_local; lia).
      inversion Heq; subst c v; clear Heq.
      apply Hrange with (cost := Znth smallest cost 0).
      unfold HeapEntriesPair.
      rewrite in_map_iff.
      exists smallest.
      split; [reflexivity | rewrite <- In_Zrange; lia].
    + rewrite Znth_replace_Znth_diff_local in Heq by
        (rewrite ?Zlength_replace_Znth_local; lia).
      rewrite Znth_replace_Znth_diff_local in Heq by
        (rewrite ?Zlength_replace_Znth_local; lia).
      rewrite Znth_replace_Znth_diff_local in Heq by
        (rewrite ?Zlength_replace_Znth_local; lia).
      rewrite Znth_replace_Znth_diff_local in Heq by
        (rewrite ?Zlength_replace_Znth_local; lia).
      inversion Heq; subst c v; clear Heq.
      apply Hrange with (cost := Znth i cost 0).
      unfold HeapEntriesPair.
      rewrite in_map_iff.
      exists i.
      split; [reflexivity | rewrite <- In_Zrange; lia].
Qed.

Definition HeapOrderExceptDownPair
    (heap_cost : list Z) (size idx : Z) : Prop :=
  0 <= idx /\
  idx < size /\
  forall child,
    0 < child /\ child < size /\ HeapParent child <> idx ->
    Znth (HeapParent child) heap_cost 0 <= Znth child heap_cost 0.

Definition PopHoleParentDominatesChildrenPair
    (heap_cost : list Z) (size idx : Z) : Prop :=
  idx = 0 \/
  forall child,
    0 < child /\ child < size /\ HeapParent child = idx ->
    Znth (HeapParent idx) heap_cost 0 <= Znth child heap_cost 0.

Definition PopSelectedChildPair
    (heap_cost : list Z) (size idx smallest : Z) : Prop :=
  0 <= idx /\
  idx < size /\
  idx < smallest /\
  0 <= smallest /\
  smallest < size /\
  HeapParent smallest = idx /\
  (forall child,
     0 < child /\ child < size /\ HeapParent child = idx ->
     Znth smallest heap_cost 0 <= Znth child heap_cost 0).

Lemma heap_parent_of_left_child_pair : forall idx,
  0 <= idx ->
  HeapParent (2 * idx + 1) = idx.
Proof.
  intros idx Hidx.
  unfold HeapParent.
  replace (2 * idx + 1 - 1) with (2 * idx) by lia.
  replace (2 * idx) with (idx * 2) by lia.
  rewrite Z.quot_mul by lia.
  lia.
Qed.

Lemma heap_parent_of_right_child_pair : forall idx,
  0 <= idx ->
  HeapParent (2 * idx + 2) = idx.
Proof.
  intros idx Hidx.
  unfold HeapParent.
  replace (2 * idx + 2 - 1) with (2 * idx + 1) by lia.
  symmetry.
  apply Z.quot_unique with (r := 1); lia.
Qed.

Lemma heap_parent_child_cases_pair : forall idx child,
  0 <= idx ->
  0 < child ->
  HeapParent child = idx ->
  child = 2 * idx + 1 \/ child = 2 * idx + 2.
Proof.
  intros idx child Hidx Hchild Hparent.
  unfold HeapParent in Hparent.
  assert (Hchild_nonneg : 0 <= child - 1) by lia.
  assert (Hlow : 2 * idx <= child - 1).
  {
    rewrite <- Hparent.
    pose proof (Z.mul_quot_le (child - 1) 2 Hchild_nonneg ltac:(lia))
      as [_ Hlow].
    exact Hlow.
  }
  assert (Hhigh : child - 1 < 2 * (idx + 1)).
  {
    rewrite <- Hparent.
    apply Z.mul_succ_quot_gt; lia.
  }
  lia.
Qed.

Lemma pop_selected_child_right_pair : forall cur size idx left right,
  0 <= idx ->
  left = 2 * idx + 1 ->
  right = left + 1 ->
  right < size ->
  Znth right cur 0 < Znth left cur 0 ->
  PopSelectedChildPair cur size idx right.
Proof.
  intros cur size idx left right Hidx Hleft Hright Hbound Hcmp.
  subst left right.
  unfold PopSelectedChildPair.
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split.
  - replace (2 * idx + 1 + 1) with (2 * idx + 2) by lia.
    apply heap_parent_of_right_child_pair; lia.
  - intros child [Hchild_pos [Hchild_lt Hparent]].
    destruct (heap_parent_child_cases_pair idx child Hidx Hchild_pos Hparent)
      as [Hcase | Hcase].
    + subst child.
      replace (2 * idx + 1 + 1) with (2 * idx + 2) in * by lia.
      lia.
    + subst child.
      replace (2 * idx + 1 + 1) with (2 * idx + 2) in * by lia.
      lia.
Qed.

Lemma pop_selected_child_left_no_right_pair : forall cur size idx left right,
  0 <= idx ->
  left = 2 * idx + 1 ->
  right = left + 1 ->
  left < size ->
  right >= size ->
  PopSelectedChildPair cur size idx left.
Proof.
  intros cur size idx left right Hidx Hleft Hright Hleft_bound Hright_out.
  subst left right.
  unfold PopSelectedChildPair.
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split.
  - apply heap_parent_of_left_child_pair; lia.
  - intros child [Hchild_pos [Hchild_lt Hparent]].
    destruct (heap_parent_child_cases_pair idx child Hidx Hchild_pos Hparent)
      as [Hcase | Hcase].
    + subst child.
      lia.
    + subst child.
      replace (2 * idx + 1 + 1) with (2 * idx + 2) in * by lia.
      lia.
Qed.

Lemma pop_selected_child_left_le_right_pair : forall cur size idx left right,
  0 <= idx ->
  left = 2 * idx + 1 ->
  right = left + 1 ->
  right < size ->
  Znth left cur 0 <= Znth right cur 0 ->
  PopSelectedChildPair cur size idx left.
Proof.
  intros cur size idx left right Hidx Hleft Hright Hbound Hcmp.
  subst left right.
  unfold PopSelectedChildPair.
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split.
  - apply heap_parent_of_left_child_pair; lia.
  - intros child [Hchild_pos [Hchild_lt Hparent]].
    destruct (heap_parent_child_cases_pair idx child Hidx Hchild_pos Hparent)
      as [Hcase | Hcase].
    + subst child.
      lia.
    + subst child.
      replace (2 * idx + 1 + 1) with (2 * idx + 2) in * by lia.
      lia.
Qed.

Lemma pop_selected_child_bounds_pair : forall cur size idx left right smallest,
  0 <= idx ->
  left = 2 * idx + 1 ->
  right = left + 1 ->
  PopSelectedChildPair cur size idx smallest ->
  0 <= left /\ left < size /\ 0 <= right /\ right <= size.
Proof.
  intros cur size idx left right smallest Hidx Hleft Hright Hsel.
  unfold PopSelectedChildPair in Hsel.
  destruct Hsel as
    [_ [_ [Hidx_smallest [_ [Hsmallest_size [Hparent _]]]]]].
  subst left right.
  split; [lia|].
  split.
  - destruct (heap_parent_child_cases_pair idx smallest Hidx ltac:(lia) Hparent)
      as [Hcase | Hcase]; subst smallest; lia.
  - split; [lia|].
    destruct (heap_parent_child_cases_pair idx smallest Hidx ltac:(lia) Hparent)
      as [Hcase | Hcase]; subst smallest; lia.
Qed.

Lemma min_heap_prefix_pair_root_min : forall cost vertex n,
  0 < n ->
  MinHeapPrefixPair cost vertex n ->
  PrefixMinValuePair
    (HeapEntriesPair cost vertex n)
    (Znth 0 cost 0)
    (Znth 0 vertex 0).
Proof.
  intros cost vertex n Hn [Hn0 [Hcost_len [Hvertex_len Hord]]].
  unfold PrefixMinValuePair, min_object_of_subset.
  split.
  - unfold HeapEntriesPair.
    replace (Znth 0 cost 0, Znth 0 vertex 0) with
      ((fun idx : Z => (Znth idx cost 0, Znth idx vertex 0)) 0) by reflexivity.
    apply (in_map
      (fun idx : Z => (Znth idx cost 0, Znth idx vertex 0))
      (Zrange 0 n) 0).
    rewrite <- In_Zrange.
    lia.
  - intros [c v] Hin.
    change (In (c, v) (HeapEntriesPair cost vertex n)) in Hin.
    unfold HeapEntriesPair in Hin.
    rewrite in_map_iff in Hin.
    destruct Hin as [idx [Hentry Hidx_range]].
    rewrite <- In_Zrange in Hidx_range.
    inversion Hentry; subst c v; clear Hentry.
    simpl.
    enough (Znth 0 cost 0 <= Znth idx cost 0) by exact H.
    refine (well_founded_induction_type
      (A := Z) (R := fun x y => 0 <= x < y)
      (Z.lt_wf 0)
      (fun y => 0 <= y < n -> Znth 0 cost 0 <= Znth y cost 0)
      _ idx _).
    + intros y IH [Hy0 Hylt].
      destruct (Z.eq_dec y 0) as [-> | Hyneq].
      * lia.
      * assert (Hy_pos : 0 < y) by lia.
        destruct (heap_parent_bounds_pos_pair y Hy_pos) as [Hparent0 Hparentlt].
        assert (Hedge : Znth (HeapParent y) cost 0 <= Znth y cost 0).
        { apply Hord. lia. }
        assert (Hroot_parent : Znth 0 cost 0 <= Znth (HeapParent y) cost 0).
        { apply IH; lia. }
        lia.
    + lia.
Qed.

Definition PopLoopStatePair
    (cost_before vertex_before cost_cur vertex_cur : list Z)
  (n idx : Z) : Prop :=
  1 < n /\
  Zlength cost_before = n /\
  Zlength vertex_before = n /\
  Zlength cost_cur = n /\
  Zlength vertex_cur = n /\
  0 <= idx /\
  idx < n - 1 /\
  PriorityQueuePrefixPair
    cost_before vertex_before n
    (HeapEntriesPair cost_before vertex_before n) /\
  Znth idx cost_cur 0 = Znth (n - 1) cost_before 0 /\
  Znth idx vertex_cur 0 = Znth (n - 1) vertex_before 0 /\
  Znth (n - 1) cost_cur 0 = Znth (n - 1) cost_before 0 /\
  Znth (n - 1) vertex_cur 0 = Znth (n - 1) vertex_before 0 /\
  1 <= n /\
  n <= Zlength cost_before /\
  n <= Zlength vertex_before /\
  n <= Zlength cost_cur /\
  n <= Zlength vertex_cur /\
  Permutation
    (HeapEntriesPair cost_cur vertex_cur (n - 1))
    (sublist 1 n (HeapEntriesPair cost_before vertex_before n)) /\
  HeapOrderExceptDownPair cost_cur (n - 1) idx /\
  PopHoleParentDominatesChildrenPair cost_cur (n - 1) idx.

Lemma pop_loop_pair_init_replace_root :
  forall cost vertex heap_entries n,
    1 < n ->
    Zlength cost = n ->
    Zlength vertex = n ->
    PriorityQueuePrefixPair cost vertex n heap_entries ->
    PopLoopStatePair
      cost vertex
      (replace_Znth 0 (Znth (n - 1) cost 0) cost)
      (replace_Znth 0 (Znth (n - 1) vertex 0) vertex)
      n 0.
Proof.
  intros cost vertex heap_entries n Hn Hcost_len Hvertex_len Hpq.
  destruct Hpq as [Hentries [Hheap Hmin]].
  destruct Hheap as [Hn0 [Hcost_heap_len [Hvertex_heap_len Hord]]].
  assert (Hremaining :
    Permutation
      (HeapEntriesPair
        (replace_Znth 0 (Znth (n - 1) cost 0) cost)
        (replace_Znth 0 (Znth (n - 1) vertex 0) vertex)
        (n - 1))
      (sublist 1 n (HeapEntriesPair cost vertex n))).
  {
    set (entries := HeapEntriesPair cost vertex n).
    assert (Hentries_len : Zlength entries = n).
    { subst entries. rewrite Zlength_HeapEntriesPair by lia. reflexivity. }
    assert (Htail :
      sublist (n - 1) n entries =
      [(Znth (n - 1) cost 0, Znth (n - 1) vertex 0)]).
    {
      subst entries.
      replace (sublist (n - 1) n (HeapEntriesPair cost vertex n))
        with [Znth (n - 1) (HeapEntriesPair cost vertex n) (0, 0)].
      2:{
        replace (sublist (n - 1) n (HeapEntriesPair cost vertex n))
          with (sublist (n - 1) ((n - 1) + 1) (HeapEntriesPair cost vertex n))
          by (f_equal; lia).
        symmetry.
        apply sublist_single.
        rewrite Zlength_HeapEntriesPair by lia; lia.
      }
      rewrite !Znth_HeapEntriesPair by lia.
      simpl.
      reflexivity.
    }
    assert (Hsub_decomp :
      sublist 1 n entries =
      sublist 1 (n - 1) entries ++
      [(Znth (n - 1) cost 0, Znth (n - 1) vertex 0)]).
    {
      rewrite (sublist_split 1 n (n - 1) entries) by lia.
      rewrite Htail.
      reflexivity.
    }
    subst entries.
    rewrite HeapEntriesPair_replace_root_prefix by lia.
    rewrite Hsub_decomp.
    apply Permutation_cons_append.
  }
  unfold PopLoopStatePair.
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [rewrite Zlength_replace_Znth; lia|].
  split; [rewrite Zlength_replace_Znth; lia|].
  split; [lia|].
  split; [lia|].
  split.
  { unfold PriorityQueuePrefixPair.
    split; [reflexivity|].
    split.
    - unfold MinHeapPrefixPair. repeat split; try lia. exact Hord.
    - intros Hpos.
      rewrite <- Hentries.
      apply Hmin; exact Hpos. }
  split; [rewrite Znth_replace_Znth_Same by lia; reflexivity|].
  split; [rewrite Znth_replace_Znth_Same by lia; reflexivity|].
  split; [rewrite Znth_replace_Znth_Diff by lia; reflexivity|].
  split; [rewrite Znth_replace_Znth_Diff by lia; reflexivity|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [rewrite Zlength_replace_Znth; lia|].
  split; [rewrite Zlength_replace_Znth; lia|].
  split; [exact Hremaining|].
  split.
  - unfold HeapOrderExceptDownPair.
    split; [lia|].
    split; [lia|].
    intros child [Hchild_pos [Hchild_lt Hparent_neq]].
    destruct (heap_parent_bounds_pos_pair child Hchild_pos)
      as [Hparent0 Hparentlt].
    rewrite Znth_replace_Znth_Diff by lia.
    rewrite Znth_replace_Znth_Diff by lia.
    apply Hord.
    lia.
  - unfold PopHoleParentDominatesChildrenPair.
    left; reflexivity.
Qed.

Definition PopReadyStatePair
    (cost_before vertex_before cost_cur vertex_cur : list Z)
  (n cost vertex : Z) : Prop :=
  1 < n /\
  Zlength cost_before = n /\
  Zlength vertex_before = n /\
  Zlength cost_cur = n /\
  Zlength vertex_cur = n /\
  PriorityQueuePrefixPair
    cost_before vertex_before n
    (HeapEntriesPair cost_before vertex_before n) /\
  PrefixMinValuePair
    (HeapEntriesPair cost_before vertex_before n) cost vertex /\
  cost = Znth 0 cost_before 0 /\
  vertex = Znth 0 vertex_before 0 /\
  Znth (n - 1) cost_cur 0 = Znth (n - 1) cost_before 0 /\
  Znth (n - 1) vertex_cur 0 = Znth (n - 1) vertex_before 0 /\
  1 <= n /\
  n <= Zlength cost_before /\
  n <= Zlength vertex_before /\
  n <= Zlength cost_cur /\
  n <= Zlength vertex_cur /\
  Permutation
    (HeapEntriesPair cost_cur vertex_cur (n - 1))
    (sublist 1 n (HeapEntriesPair cost_before vertex_before n)) /\
  PriorityQueuePrefixPair
    cost_cur vertex_cur (n - 1)
    (HeapEntriesPair cost_cur vertex_cur (n - 1)).

Lemma pop_loop_pair_no_swap_to_ready :
  forall cost_before vertex_before cost_cur vertex_cur
         n idx smallest root_cost out_vertex,
    PopLoopStatePair cost_before vertex_before cost_cur vertex_cur n idx ->
    PopSelectedChildPair cost_cur (n - 1) idx smallest ->
    Znth idx cost_cur 0 <= Znth smallest cost_cur 0 ->
    root_cost = Znth 0 cost_before 0 ->
    out_vertex = Znth 0 vertex_before 0 ->
    PopReadyStatePair
      cost_before vertex_before cost_cur vertex_cur n root_cost out_vertex.
Proof.
  intros cost_before vertex_before cost_cur vertex_cur
         n idx smallest root_cost out_vertex
         Hstate Hsel Hcmp Hroot Hout.
  unfold PopLoopStatePair in Hstate.
  destruct Hstate as [Hn Hstate].
  destruct Hstate as [Hcost_before_len Hstate].
  destruct Hstate as [Hvertex_before_len Hstate].
  destruct Hstate as [Hcost_cur_len Hstate].
  destruct Hstate as [Hvertex_cur_len Hstate].
  destruct Hstate as [Hidx0 Hstate].
  destruct Hstate as [Hidxlt Hstate].
  destruct Hstate as [Hpq_before Hstate].
  destruct Hstate as [Hidx_cost Hstate].
  destruct Hstate as [Hidx_vertex Hstate].
  destruct Hstate as [Hlast_cost Hstate].
  destruct Hstate as [Hlast_vertex Hstate].
  destruct Hstate as [Hn1 Hstate].
  destruct Hstate as [Hn_cost_before Hstate].
  destruct Hstate as [Hn_vertex_before Hstate].
  destruct Hstate as [Hn_cost_cur Hstate].
  destruct Hstate as [Hn_vertex_cur Hstate].
  destruct Hstate as [Hremaining [Hexcept Hhole]].
  unfold PopSelectedChildPair in Hsel.
  destruct Hsel as
    [_ [_ [_ [_ [_ [Hsmallest_parent Hsmallest_dom]]]]]].
  assert (Hheap_cur : MinHeapPrefixPair cost_cur vertex_cur (n - 1)).
  {
    unfold MinHeapPrefixPair.
    split; [lia|].
    split; [lia|].
    split; [lia|].
    intros child [Hchild_pos Hchild_lt].
    destruct (Z.eq_dec (HeapParent child) idx) as [Hparent_eq | Hparent_neq].
    - assert (Znth smallest cost_cur 0 <= Znth child cost_cur 0).
      { apply Hsmallest_dom. lia. }
      rewrite Hparent_eq.
      lia.
    - unfold HeapOrderExceptDownPair in Hexcept.
      destruct Hexcept as [_ [_ Hexcept_ord]].
      apply Hexcept_ord.
      lia.
  }
  unfold PopReadyStatePair.
  split; [lia|].
  split; [exact Hcost_before_len|].
  split; [exact Hvertex_before_len|].
  split; [exact Hcost_cur_len|].
  split; [exact Hvertex_cur_len|].
  split; [exact Hpq_before|].
  split.
  - subst root_cost out_vertex.
    destruct Hpq_before as [_ [Hheap_before _]].
    apply min_heap_prefix_pair_root_min; try lia.
    exact Hheap_before.
  - split; [exact Hroot|].
    split; [exact Hout|].
    split; [exact Hlast_cost|].
    split; [exact Hlast_vertex|].
    split; [exact Hn1|].
    split; [exact Hn_cost_before|].
    split; [exact Hn_vertex_before|].
    split; [exact Hn_cost_cur|].
    split; [exact Hn_vertex_cur|].
    split; [exact Hremaining|].
    unfold PriorityQueuePrefixPair.
    split; [reflexivity|].
    split; [exact Hheap_cur|].
    intros Hactive_pos.
    apply min_heap_prefix_pair_root_min; try lia.
    exact Hheap_cur.
Qed.

Lemma sublist_prefix_swap_pair :
  forall {A : Type} (cur : list A) size i j d,
    0 <= i < size ->
    0 <= j < size ->
    size <= Zlength cur ->
    sublist 0 size
      (replace_Znth j (Znth i cur d) (replace_Znth i (Znth j cur d) cur)) =
    replace_Znth j (Znth i (sublist 0 size cur) d)
      (replace_Znth i (Znth j (sublist 0 size cur) d) (sublist 0 size cur)).
Proof.
  intros A cur size i j d Hi Hj Hsize.
  set (prefix := sublist 0 size cur).
  set (suffix := sublist size (Zlength cur) cur).
  assert (Hsplit : cur = prefix ++ suffix).
  {
    subst prefix suffix.
    rewrite <- (sublist_split 0 (Zlength cur) size cur) by lia.
    symmetry.
    apply sublist_self.
    reflexivity.
  }
  assert (Hinner :
    replace_Znth i (Znth j cur d) cur =
    replace_Znth i (Znth j cur d) prefix ++ suffix).
  {
    rewrite Hsplit.
    rewrite replace_Znth_app_l with (l1 := prefix) (l2 := suffix).
    2:{ lia. }
    2:{ subst prefix. rewrite Zlength_sublist by lia. lia. }
    reflexivity.
  }
  assert (Hwhole :
    replace_Znth j (Znth i cur d) (replace_Znth i (Znth j cur d) cur) =
    replace_Znth j (Znth i cur d)
      (replace_Znth i (Znth j cur d) prefix) ++ suffix).
  {
    rewrite Hinner.
    rewrite replace_Znth_app_l
      with (l1 := replace_Znth i (Znth j cur d) prefix) (l2 := suffix).
    2:{ lia. }
    2:{ rewrite Zlength_replace_Znth. subst prefix. rewrite Zlength_sublist by lia. lia. }
    reflexivity.
  }
  rewrite Hwhole.
  replace size with
    (Zlength
      (replace_Znth j (Znth i cur d) (replace_Znth i (Znth j cur d) prefix))).
  2:{ rewrite !Zlength_replace_Znth. subst prefix. rewrite Zlength_sublist by lia. lia. }
  rewrite sublist_app_exact1.
  subst prefix.
  rewrite Znth_sublist by lia.
  rewrite Znth_sublist by lia.
  replace (i - 0) with i by lia.
  replace (j - 0) with j by lia.
  replace (i + 0) with i by lia.
  replace (j + 0) with j by lia.
  reflexivity.
Qed.

Lemma HeapEntriesPair_prefix_swap :
  forall cost vertex n idx smallest,
    0 <= idx < n ->
    0 <= smallest < n ->
    idx <> smallest ->
    n <= Zlength cost ->
    n <= Zlength vertex ->
    HeapEntriesPair
      (replace_Znth smallest (Znth idx cost 0)
        (replace_Znth idx (Znth smallest cost 0) cost))
      (replace_Znth smallest (Znth idx vertex 0)
        (replace_Znth idx (Znth smallest vertex 0) vertex))
      n =
    replace_Znth smallest (Znth idx (HeapEntriesPair cost vertex n) (0, 0))
      (replace_Znth idx (Znth smallest (HeapEntriesPair cost vertex n) (0, 0))
        (HeapEntriesPair cost vertex n)).
Proof.
  intros cost vertex n idx smallest Hidx Hsmallest Hneq Hcost_len Hvertex_len.
  apply (proj2 (list_eq_ext _ _ (0, 0))).
  split.
  - rewrite Zlength_HeapEntriesPair by
      (rewrite ?Zlength_replace_Znth; lia).
    rewrite !Zlength_replace_Znth.
    rewrite Zlength_HeapEntriesPair by lia.
    reflexivity.
  - intros k Hk.
    rewrite Zlength_HeapEntriesPair in Hk by
      (rewrite ?Zlength_replace_Znth; lia).
    rewrite Znth_HeapEntriesPair by
      (rewrite ?Zlength_replace_Znth; lia).
    destruct (Z.eq_dec k smallest) as [Hks | Hks].
    + subst k.
      repeat rewrite Znth_replace_Znth_same_local by
        (rewrite ?Zlength_replace_Znth_local; lia).
      rewrite Znth_replace_Znth_Same
        with (i := smallest) by
        (rewrite ?Zlength_replace_Znth; rewrite ?Zlength_HeapEntriesPair; lia).
      rewrite Znth_HeapEntriesPair by lia.
      reflexivity.
    + destruct (Z.eq_dec k idx) as [Hki | Hki].
      * subst k.
        repeat rewrite Znth_replace_Znth_diff_local by
          (rewrite ?Zlength_replace_Znth_local; lia).
        repeat rewrite Znth_replace_Znth_same_local by
          (rewrite ?Zlength_replace_Znth_local; lia).
        replace (Znth idx
          (replace_Znth smallest
            (Znth idx (HeapEntriesPair cost vertex n) (0, 0))
            (replace_Znth idx
              (Znth smallest (HeapEntriesPair cost vertex n) (0, 0))
              (HeapEntriesPair cost vertex n))) (0, 0))
          with
            (Znth idx
              (replace_Znth idx
                (Znth smallest (HeapEntriesPair cost vertex n) (0, 0))
                (HeapEntriesPair cost vertex n)) (0, 0)).
        2:{
          symmetry.
          apply (Znth_replace_Znth_Diff (0, 0)
            (replace_Znth idx
              (Znth smallest (HeapEntriesPair cost vertex n) (0, 0))
              (HeapEntriesPair cost vertex n))
            smallest idx
            (Znth idx (HeapEntriesPair cost vertex n) (0, 0)));
            rewrite ?Zlength_replace_Znth; rewrite ?Zlength_HeapEntriesPair; lia.
        }
        replace (Znth idx
          (replace_Znth idx
            (Znth smallest (HeapEntriesPair cost vertex n) (0, 0))
            (HeapEntriesPair cost vertex n)) (0, 0))
          with (Znth smallest (HeapEntriesPair cost vertex n) (0, 0)).
        2:{
          symmetry.
          apply Znth_replace_Znth_Same.
          rewrite Zlength_HeapEntriesPair; lia.
        }
        rewrite !Znth_HeapEntriesPair by lia.
        replace (Znth idx
          (replace_Znth smallest (Znth idx cost 0, Znth idx vertex 0)
            (replace_Znth idx (Znth smallest cost 0, Znth smallest vertex 0)
              (HeapEntriesPair cost vertex n))) (0, 0))
          with (Znth smallest cost 0, Znth smallest vertex 0).
        2:{
          rewrite Znth_replace_Znth_Diff with (i := smallest) (j := idx) by
            (rewrite ?Zlength_replace_Znth; rewrite ?Zlength_HeapEntriesPair; lia).
          rewrite Znth_replace_Znth_Same by
            (rewrite ?Zlength_HeapEntriesPair; lia).
          reflexivity.
        }
        replace (Znth idx
          (replace_Znth smallest (Znth idx vertex 0)
            (replace_Znth idx (Znth smallest vertex 0) vertex)) 0)
          with (Znth smallest vertex 0).
        2:{
          rewrite Znth_replace_Znth_diff_local by
            (rewrite ?Zlength_replace_Znth_local; lia).
          rewrite Znth_replace_Znth_same_local by
            (rewrite ?Zlength_replace_Znth_local; lia).
          reflexivity.
        }
        symmetry.
        rewrite Znth_replace_Znth_Diff with (i := smallest) (j := idx) by
          (rewrite ?Zlength_replace_Znth; rewrite ?Zlength_HeapEntriesPair; lia).
        rewrite Znth_replace_Znth_Same by
          (rewrite ?Zlength_HeapEntriesPair; lia).
        reflexivity.
      * repeat rewrite Znth_replace_Znth_diff_local by
          (rewrite ?Zlength_replace_Znth_local; lia).
        rewrite Znth_replace_Znth_Diff
          with (i := smallest) (j := k) by
          (rewrite ?Zlength_replace_Znth; rewrite ?Zlength_HeapEntriesPair; lia).
        rewrite Znth_replace_Znth_Diff
          with (i := idx) (j := k) by
          (rewrite ?Zlength_replace_Znth; rewrite ?Zlength_HeapEntriesPair; lia).
        rewrite Znth_HeapEntriesPair by lia.
        reflexivity.
Qed.

Lemma pop_loop_pair_swap_down_preserve :
  forall cost_before vertex_before cost_cur vertex_cur n idx smallest,
    PopLoopStatePair cost_before vertex_before cost_cur vertex_cur n idx ->
    PopSelectedChildPair cost_cur (n - 1) idx smallest ->
    Znth idx cost_cur 0 > Znth smallest cost_cur 0 ->
    let cost_cur2 :=
      replace_Znth smallest (Znth idx cost_cur 0)
        (replace_Znth idx (Znth smallest cost_cur 0) cost_cur) in
    let vertex_cur2 :=
      replace_Znth smallest (Znth idx vertex_cur 0)
        (replace_Znth idx (Znth smallest vertex_cur 0) vertex_cur) in
    idx < smallest /\
    PopLoopStatePair
      cost_before vertex_before cost_cur2 vertex_cur2 n smallest.
Proof.
  intros cost_before vertex_before cost_cur vertex_cur n idx smallest
         Hstate Hsel Hgt.
  unfold PopLoopStatePair in Hstate.
  destruct Hstate as [Hn Hstate].
  destruct Hstate as [Hcost_before_len Hstate].
  destruct Hstate as [Hvertex_before_len Hstate].
  destruct Hstate as [Hcost_cur_len Hstate].
  destruct Hstate as [Hvertex_cur_len Hstate].
  destruct Hstate as [Hidx0 Hstate].
  destruct Hstate as [Hidxlt Hstate].
  destruct Hstate as [Hpq_before Hstate].
  destruct Hstate as [Hidx_cost Hstate].
  destruct Hstate as [Hidx_vertex Hstate].
  destruct Hstate as [Hlast_cost Hstate].
  destruct Hstate as [Hlast_vertex Hstate].
  destruct Hstate as [Hn1 Hstate].
  destruct Hstate as [Hn_cost_before Hstate].
  destruct Hstate as [Hn_vertex_before Hstate].
  destruct Hstate as [Hn_cost_cur Hstate].
  destruct Hstate as [Hn_vertex_cur Hstate].
  destruct Hstate as [Hremaining [Hexcept Hhole]].
  unfold PopSelectedChildPair in Hsel.
  destruct Hsel as
    [_ [_ [Hidx_smallest [Hsmallest0 [Hsmallestlt
      [Hsmallest_parent Hsmallest_dom]]]]]].
  unfold HeapOrderExceptDownPair in Hexcept.
  destruct Hexcept as [Hexcept0 [Hexcept_bound Hexcept_ord]].
  set (cost_cur2 :=
    replace_Znth smallest (Znth idx cost_cur 0)
      (replace_Znth idx (Znth smallest cost_cur 0) cost_cur)).
  set (vertex_cur2 :=
    replace_Znth smallest (Znth idx vertex_cur 0)
      (replace_Znth idx (Znth smallest vertex_cur 0) vertex_cur)).
  assert (Hidx_range_cost : 0 <= idx < Zlength cost_cur) by (rewrite Hcost_cur_len; lia).
  assert (Hsmallest_range_cost : 0 <= smallest < Zlength cost_cur) by (rewrite Hcost_cur_len; lia).
  assert (Hidx_range_vertex : 0 <= idx < Zlength vertex_cur) by (rewrite Hvertex_cur_len; lia).
  assert (Hsmallest_range_vertex : 0 <= smallest < Zlength vertex_cur) by (rewrite Hvertex_cur_len; lia).
  assert (Hswap_idx_cost : Znth idx cost_cur2 0 = Znth smallest cost_cur 0).
  {
    unfold cost_cur2.
    rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  }
  assert (Hswap_smallest_cost : Znth smallest cost_cur2 0 = Znth idx cost_cur 0).
  {
    unfold cost_cur2.
    rewrite Znth_replace_Znth_Same by (repeat rewrite Zlength_replace_Znth; lia).
    reflexivity.
  }
  assert (Hswap_other_cost :
    forall k,
      0 <= k < Zlength cost_cur ->
      k <> idx ->
      k <> smallest ->
      Znth k cost_cur2 0 = Znth k cost_cur 0).
  {
    intros k Hk Hk_idx Hk_smallest.
    unfold cost_cur2.
    rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by lia.
    reflexivity.
  }
  assert (Hswap_smallest_vertex : Znth smallest vertex_cur2 0 = Znth idx vertex_cur 0).
  {
    unfold vertex_cur2.
    rewrite Znth_replace_Znth_Same by (repeat rewrite Zlength_replace_Znth; lia).
    reflexivity.
  }
  assert (Hswap_other_vertex :
    forall k,
      0 <= k < Zlength vertex_cur ->
      k <> idx ->
      k <> smallest ->
      Znth k vertex_cur2 0 = Znth k vertex_cur 0).
  {
    intros k Hk Hk_idx Hk_smallest.
    unfold vertex_cur2.
    rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by lia.
    reflexivity.
  }
  split; [exact Hidx_smallest|].
  unfold PopLoopStatePair.
  split; [exact Hn|].
  split; [exact Hcost_before_len|].
  split; [exact Hvertex_before_len|].
  split.
  - unfold cost_cur2. repeat rewrite Zlength_replace_Znth. exact Hcost_cur_len.
  - split.
    + unfold vertex_cur2. repeat rewrite Zlength_replace_Znth. exact Hvertex_cur_len.
    + split; [exact Hsmallest0|].
      split; [exact Hsmallestlt|].
      split; [exact Hpq_before|].
      split.
      * rewrite Hswap_smallest_cost. exact Hidx_cost.
      * split.
        { rewrite Hswap_smallest_vertex. exact Hidx_vertex. }
        split.
        { assert (Hlast_range : 0 <= n - 1 < Zlength cost_cur) by (rewrite Hcost_cur_len; lia).
          rewrite (Hswap_other_cost (n - 1) Hlast_range) by lia.
          exact Hlast_cost. }
        split.
        { assert (Hlast_range : 0 <= n - 1 < Zlength vertex_cur) by (rewrite Hvertex_cur_len; lia).
          rewrite (Hswap_other_vertex (n - 1) Hlast_range) by lia.
          exact Hlast_vertex. }
        split; [exact Hn1|].
        split; [exact Hn_cost_before|].
        split; [exact Hn_vertex_before|].
        split.
        { unfold cost_cur2. repeat rewrite Zlength_replace_Znth. exact Hn_cost_cur. }
        split.
        { unfold vertex_cur2. repeat rewrite Zlength_replace_Znth. exact Hn_vertex_cur. }
        split.
        { assert (Hentries_swap :
            HeapEntriesPair cost_cur2 vertex_cur2 (n - 1) =
            replace_Znth smallest
              (Znth idx (HeapEntriesPair cost_cur vertex_cur (n - 1)) (0, 0))
              (replace_Znth idx
                (Znth smallest (HeapEntriesPair cost_cur vertex_cur (n - 1)) (0, 0))
                (HeapEntriesPair cost_cur vertex_cur (n - 1)))).
          {
            unfold cost_cur2, vertex_cur2.
        apply HeapEntriesPair_prefix_swap; lia.
          }
          rewrite Hentries_swap.
          eapply Permutation_trans with
            (l' := HeapEntriesPair cost_cur vertex_cur (n - 1)).
          { apply Permutation_sym.
            apply permutation_swap_Znth_any.
            - rewrite Zlength_HeapEntriesPair by lia; lia.
            - rewrite Zlength_HeapEntriesPair by lia; lia. }
          { exact Hremaining. } }
        split.
        { unfold HeapOrderExceptDownPair.
          split; [exact Hsmallest0|].
          split; [exact Hsmallestlt|].
          intros child [Hchild_pos [Hchild_lt Hparent_neq_smallest]].
          destruct (Z.eq_dec child smallest) as [Hchild_smallest | Hchild_not_smallest].
          - subst child.
            rewrite Hsmallest_parent.
            rewrite Hswap_idx_cost, Hswap_smallest_cost.
            lia.
          - destruct (Z.eq_dec child idx) as [Hchild_idx | Hchild_not_idx].
            + subst child.
              destruct Hhole as [Hidx_zero | Hhole'].
              * subst idx; lia.
              * assert (Hparent_dom_smallest :
                  Znth (HeapParent idx) cost_cur 0 <= Znth smallest cost_cur 0).
                {
                  apply Hhole'.
                  split; [lia|].
                  split; [exact Hsmallestlt|].
                  exact Hsmallest_parent.
                }
                assert (Hparent_idx_bounds : 0 <= HeapParent idx < idx).
                { apply heap_parent_bounds_pos_pair; lia. }
                destruct Hparent_idx_bounds as [Hparent_idx0 Hparent_idx_lt].
                assert (Hparent_idx_range : 0 <= HeapParent idx < Zlength cost_cur) by
                  (rewrite Hcost_cur_len; lia).
                rewrite (Hswap_other_cost (HeapParent idx) Hparent_idx_range) by lia.
                rewrite Hswap_idx_cost.
                exact Hparent_dom_smallest.
            + destruct (Z.eq_dec (HeapParent child) idx) as [Hparent_idx | Hparent_not_idx].
              * rewrite Hparent_idx.
                rewrite Hswap_idx_cost.
                assert (Hchild_range : 0 <= child < Zlength cost_cur) by
                  (rewrite Hcost_cur_len; lia).
                rewrite (Hswap_other_cost child Hchild_range Hchild_not_idx Hchild_not_smallest).
                apply Hsmallest_dom.
                split; [exact Hchild_pos|].
                split; [exact Hchild_lt|].
                exact Hparent_idx.
              * assert (Hparent_range : 0 <= HeapParent child < Zlength cost_cur).
                {
                  destruct (heap_parent_bounds_pos_pair child Hchild_pos) as [Hparent0 Hparentlt].
                  rewrite Hcost_cur_len; lia.
                }
                assert (Hchild_range : 0 <= child < Zlength cost_cur) by
                  (rewrite Hcost_cur_len; lia).
                rewrite (Hswap_other_cost (HeapParent child) Hparent_range Hparent_not_idx Hparent_neq_smallest).
                rewrite (Hswap_other_cost child Hchild_range Hchild_not_idx Hchild_not_smallest).
                apply Hexcept_ord.
                split; [exact Hchild_pos|].
                split; [exact Hchild_lt|].
                exact Hparent_not_idx. }
        { unfold PopHoleParentDominatesChildrenPair.
          right.
          intros child [Hchild_pos [Hchild_lt Hchild_parent]].
          rewrite Hsmallest_parent.
          rewrite Hswap_idx_cost.
          assert (Hchild_range : 0 <= child < Zlength cost_cur) by
            (rewrite Hcost_cur_len; lia).
          assert (Hchild_not_idx : child <> idx).
          {
            intro Heq.
            subst child.
            destruct (heap_parent_bounds_pos_pair idx ltac:(lia)) as [_ Hparentlt].
            rewrite Hchild_parent in Hparentlt.
            lia.
          }
          assert (Hchild_not_smallest : child <> smallest).
          {
            intro Heq.
            subst child.
            rewrite Hsmallest_parent in Hchild_parent.
            lia.
          }
          rewrite (Hswap_other_cost child Hchild_range Hchild_not_idx Hchild_not_smallest).
          rewrite <- Hchild_parent.
          apply Hexcept_ord.
          split; [exact Hchild_pos|].
          split; [exact Hchild_lt|].
          rewrite Hchild_parent.
          lia. }
Qed.

Lemma pop_loop_pair_no_child_to_ready :
  forall cost_before vertex_before cost_cur vertex_cur n idx root_cost out_vertex,
    PopLoopStatePair cost_before vertex_before cost_cur vertex_cur n idx ->
    idx * 2 + 1 >= n - 1 ->
    root_cost = Znth 0 cost_before 0 ->
    out_vertex = Znth 0 vertex_before 0 ->
    PopReadyStatePair
      cost_before vertex_before cost_cur vertex_cur n root_cost out_vertex.
Proof.
  intros cost_before vertex_before cost_cur vertex_cur n idx root_cost out_vertex
         Hstate Hno_child Hroot Hout.
  unfold PopLoopStatePair in Hstate.
  destruct Hstate as [Hn Hstate].
  destruct Hstate as [Hcost_before_len Hstate].
  destruct Hstate as [Hvertex_before_len Hstate].
  destruct Hstate as [Hcost_cur_len Hstate].
  destruct Hstate as [Hvertex_cur_len Hstate].
  destruct Hstate as [Hidx0 Hstate].
  destruct Hstate as [Hidxlt Hstate].
  destruct Hstate as [Hpq_before Hstate].
  destruct Hstate as [Hidx_cost Hstate].
  destruct Hstate as [Hidx_vertex Hstate].
  destruct Hstate as [Hlast_cost Hstate].
  destruct Hstate as [Hlast_vertex Hstate].
  destruct Hstate as [Hn1 Hstate].
  destruct Hstate as [Hn_cost_before Hstate].
  destruct Hstate as [Hn_vertex_before Hstate].
  destruct Hstate as [Hn_cost_cur Hstate].
  destruct Hstate as [Hn_vertex_cur Hstate].
  destruct Hstate as [Hremaining [Hexcept _]].
  unfold HeapOrderExceptDownPair in Hexcept.
  destruct Hexcept as [Hexcept0 [Hexcept_bound Hexcept_ord]].
  assert (Hheap_cur : MinHeapPrefixPair cost_cur vertex_cur (n - 1)).
  {
    unfold MinHeapPrefixPair.
    split; [lia|].
    split; [lia|].
    split; [lia|].
    intros child [Hchild_pos Hchild_lt].
    destruct (Z.eq_dec (HeapParent child) idx) as [Hparent_eq | Hparent_neq].
    - destruct (heap_parent_child_cases_pair idx child Hidx0 Hchild_pos Hparent_eq)
        as [Hcase | Hcase];
      subst child; lia.
    - apply Hexcept_ord.
      lia.
  }
  unfold PopReadyStatePair.
  split; [lia|].
  split; [exact Hcost_before_len|].
  split; [exact Hvertex_before_len|].
  split; [exact Hcost_cur_len|].
  split; [exact Hvertex_cur_len|].
  split; [exact Hpq_before|].
  split.
  - subst root_cost out_vertex.
    destruct Hpq_before as [_ [Hheap_before _]].
    apply min_heap_prefix_pair_root_min; try lia.
    exact Hheap_before.
  - split; [exact Hroot|].
    split; [exact Hout|].
    split; [exact Hlast_cost|].
    split; [exact Hlast_vertex|].
    split; [exact Hn1|].
    split; [exact Hn_cost_before|].
    split; [exact Hn_vertex_before|].
    split; [exact Hn_cost_cur|].
    split; [exact Hn_vertex_cur|].
    split; [exact Hremaining|].
    unfold PriorityQueuePrefixPair.
    split; [reflexivity|].
    split; [exact Hheap_cur|].
    intros Hactive.
    apply min_heap_prefix_pair_root_min; try lia.
    exact Hheap_cur.
Qed.

Lemma priority_queue_prefix_pair_replace_at_end :
  forall cost vertex size cost_v vertex_v entries,
    0 <= size ->
    size < Zlength cost ->
    size < Zlength vertex ->
    PriorityQueuePrefixPair cost vertex size entries ->
    PriorityQueuePrefixPair
      (replace_Znth size cost_v cost)
      (replace_Znth size vertex_v vertex)
      size
      (HeapEntriesPair
        (replace_Znth size cost_v cost)
        (replace_Znth size vertex_v vertex)
        size).
Proof.
  intros cost vertex size cost_v vertex_v entries Hsize Hcost_bound Hvertex_bound Hpq.
  destruct Hpq as [Hentries [Hheap Hmin]].
  assert (Hsame_cost : forall i,
    0 <= i < size ->
    Znth i (replace_Znth size cost_v cost) 0 = Znth i cost 0).
  { intros i Hi. rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
  assert (Hsame_vertex : forall i,
    0 <= i < size ->
    Znth i (replace_Znth size vertex_v vertex) 0 = Znth i vertex 0).
  { intros i Hi. rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
  unfold PriorityQueuePrefixPair.
  split; [reflexivity|].
  split.
  - unfold MinHeapPrefixPair in *.
    destruct Hheap as [Hheap0 [Hcost_heap_len [Hvertex_heap_len Hord]]].
    split; [lia|].
    split; [rewrite Zlength_replace_Znth; lia|].
    split; [rewrite Zlength_replace_Znth; lia|].
    intros child [Hchildpos Hchildlt].
    destruct (heap_parent_bounds_pos_pair child Hchildpos) as [Hparent0 Hparentlt].
    rewrite Hsame_cost by lia.
    rewrite Hsame_cost by lia.
    apply Hord.
    lia.
  - intros Hnonempty.
    specialize (Hmin Hnonempty).
    unfold PrefixMinValuePair in *.
    unfold min_object_of_subset in *.
    destruct Hmin as [Hin_min Hle].
    assert (Hentries_same :
      HeapEntriesPair
        (replace_Znth size cost_v cost)
        (replace_Znth size vertex_v vertex)
        size =
      HeapEntriesPair cost vertex size).
    {
      unfold HeapEntriesPair.
      apply map_ext_in.
      intros i Hi.
      rewrite <- In_Zrange in Hi.
      rewrite Hsame_cost by lia.
      rewrite Hsame_vertex by lia.
      reflexivity.
    }
    replace (Znth 0 (replace_Znth size cost_v cost) 0) with
      (Znth 0 cost 0) by (rewrite Hsame_cost by lia; reflexivity).
    replace (Znth 0 (replace_Znth size vertex_v vertex) 0) with
      (Znth 0 vertex 0) by (rewrite Hsame_vertex by lia; reflexivity).
    split.
    + rewrite Hentries_same.
      rewrite <- Hentries.
      exact Hin_min.
    + intros [c v] Hin.
      rewrite Hentries_same in Hin.
      change (In (c, v) (HeapEntriesPair cost vertex size)) in Hin.
      unfold HeapEntriesPair in Hin.
      rewrite in_map_iff in Hin.
      destruct Hin as [i [Hentry Hi]].
      rewrite <- In_Zrange in Hi.
      inversion Hentry; subst c v.
      apply Hle.
      change (In (Znth i cost 0, Znth i vertex 0) entries).
      rewrite Hentries.
      unfold HeapEntriesPair.
      rewrite in_map_iff.
      exists i.
      split; [reflexivity|].
      rewrite <- In_Zrange.
      lia.
Qed.

Lemma HeapEntriesPair_replace_at_end_same_prefix :
  forall cost vertex n cost_v vertex_v,
    1 < n ->
    n <= Zlength cost ->
    n <= Zlength vertex ->
    HeapEntriesPair
      (replace_Znth (n - 1) cost_v cost)
      (replace_Znth (n - 1) vertex_v vertex)
      (n - 1) =
    HeapEntriesPair cost vertex (n - 1).
Proof.
  intros cost vertex n cost_v vertex_v Hn Hcost_len Hvertex_len.
  unfold HeapEntriesPair.
  apply map_ext_in.
  intros i Hi.
  rewrite <- In_Zrange in Hi.
  rewrite Znth_replace_Znth_Diff by lia.
  rewrite Znth_replace_Znth_Diff by lia.
  reflexivity.
Qed.

Lemma heap_entries_vertex_range_pair_replace_at_end :
  forall bound cost vertex n cost_v vertex_v,
    1 < n ->
    n <= Zlength cost ->
    n <= Zlength vertex ->
    HeapEntriesVertexRangePair bound (HeapEntriesPair cost vertex (n - 1)) ->
    HeapEntriesVertexRangePair bound
      (HeapEntriesPair
        (replace_Znth (n - 1) cost_v cost)
        (replace_Znth (n - 1) vertex_v vertex)
        (n - 1)).
Proof.
  intros bound cost vertex n cost_v vertex_v Hn Hcost_len Hvertex_len Hrange.
  rewrite HeapEntriesPair_replace_at_end_same_prefix by lia.
  exact Hrange.
Qed.

Lemma pop_remaining_pair_replace_last_permutation :
  forall cost_before vertex_before cost_cur vertex_cur n root_cost out_vertex,
    1 < n ->
    root_cost = Znth 0 cost_before 0 ->
    out_vertex = Znth 0 vertex_before 0 ->
    Zlength cost_before = n ->
    Zlength vertex_before = n ->
    Zlength cost_cur = n ->
    Zlength vertex_cur = n ->
    Permutation
      (HeapEntriesPair cost_cur vertex_cur (n - 1))
      (sublist 1 n (HeapEntriesPair cost_before vertex_before n)) ->
    Permutation
      (HeapEntriesPair cost_before vertex_before n)
      ((root_cost, out_vertex) ::
        HeapEntriesPair
          (replace_Znth (n - 1) root_cost cost_cur)
          (replace_Znth (n - 1) out_vertex vertex_cur)
          (n - 1)).
Proof.
  intros cost_before vertex_before cost_cur vertex_cur n root_cost out_vertex
         Hn Hroot Hout Hcost_before_len Hvertex_before_len Hcost_cur_len Hvertex_cur_len Hperm.
  rewrite HeapEntriesPair_replace_at_end_same_prefix by lia.
  rewrite (heap_pair_list_head_tail_by_sublist
    (HeapEntriesPair cost_before vertex_before n) n (0, 0)).
  2:{ lia. }
  2:{ rewrite Zlength_HeapEntriesPair by lia. lia. }
  rewrite Znth_HeapEntriesPair by lia.
  rewrite Hroot, Hout.
  apply perm_skip.
  symmetry.
  exact Hperm.
Qed.

Lemma pop_ready_pair_final_write_to_result :
  forall S cost_before vertex_before cost_cur vertex_cur n root_cost out_vertex,
    heap_representation_pair S cost_before vertex_before n ->
    PopReadyStatePair
      cost_before vertex_before cost_cur vertex_cur n root_cost out_vertex ->
    PopResultPair S
      cost_before vertex_before
      (replace_Znth (n - 1) root_cost cost_cur)
      (replace_Znth (n - 1) out_vertex vertex_cur)
      n root_cost out_vertex /\
    PriorityQueuePrefixPair
      (replace_Znth (n - 1) root_cost cost_cur)
      (replace_Znth (n - 1) out_vertex vertex_cur)
      (n - 1)
      (HeapEntriesPair
        (replace_Znth (n - 1) root_cost cost_cur)
        (replace_Znth (n - 1) out_vertex vertex_cur)
        (n - 1)).
Proof.
  intros S cost_before vertex_before cost_cur vertex_cur n root_cost out_vertex
         Hrep Hready.
  unfold PopReadyStatePair in Hready.
  destruct Hready as [Hn Hready].
  destruct Hready as [Hcost_before_len Hready].
  destruct Hready as [Hvertex_before_len Hready].
  destruct Hready as [Hcost_cur_len Hready].
  destruct Hready as [Hvertex_cur_len Hready].
  destruct Hready as [Hpq_before Hready].
  destruct Hready as [Hprefix_min Hready].
  destruct Hready as [Hroot Hready].
  destruct Hready as [Hout Hready].
  destruct Hready as [Hlast_cost Hready].
  destruct Hready as [Hlast_vertex Hready].
  destruct Hready as [Hn1 Hready].
  destruct Hready as [Hn_cost_before Hready].
  destruct Hready as [Hn_vertex_before Hready].
  destruct Hready as [Hn_cost_cur Hready].
  destruct Hready as [Hn_vertex_cur Hready].
  destruct Hready as [Hperm Hpq_cur].
  assert (Hpq_after :
    PriorityQueuePrefixPair
      (replace_Znth (n - 1) root_cost cost_cur)
      (replace_Znth (n - 1) out_vertex vertex_cur)
      (n - 1)
      (HeapEntriesPair
        (replace_Znth (n - 1) root_cost cost_cur)
        (replace_Znth (n - 1) out_vertex vertex_cur)
        (n - 1))).
  {
    eapply priority_queue_prefix_pair_replace_at_end; try lia.
    exact Hpq_cur.
  }
  pose proof Hpq_after as Hpq_after_whole.
  destruct Hpq_after as [Hentries_after [Hheap_after Hprefix_after]].
  unfold MinHeapPrefixPair in Hheap_after.
  destruct Hheap_after as
    [Hheap_after_nonneg [Hheap_after_cost_bound
    [Hheap_after_vertex_bound Hheap_after_order]]].
  assert (Hafter_pos : 0 < n - 1) by lia.
  pose proof (Hprefix_after Hafter_pos) as Hprefix_after_root.
  unfold PrefixMinValuePair, min_object_of_subset in Hprefix_after_root.
  destruct Hprefix_after_root as [Hafter_root_in Hafter_root_le].
  destruct Hpq_before as [Hentries_before [Hheap_before Hprefix_before]].
  unfold MinHeapPrefixPair in Hheap_before.
  destruct Hheap_before as
    [Hheap_before_nonneg [Hheap_before_cost_bound
    [Hheap_before_vertex_bound Hheap_before_order]]].
  pose proof Hprefix_min as Hprefix_min_for_core.
  pose proof Hprefix_min as Hprefix_min_for_core_raw.
  unfold PrefixMinValuePair, min_object_of_subset in Hprefix_min_for_core_raw.
  destruct Hprefix_min_for_core_raw as
    [Hroot_cost_in_entries Hroot_cost_le_entries].
  pose proof Hprefix_min as Hprefix_before_root.
  rewrite Hroot in Hprefix_before_root.
  rewrite Hout in Hprefix_before_root.
  unfold PrefixMinValuePair, min_object_of_subset in Hprefix_before_root.
  destruct Hprefix_before_root as [Hroot_in_entries Hroot_le_entries].
  split.
  - unfold PopResultPair.
    split; [exact Hrep|].
    split.
    + unfold heap_representation_pair in Hrep.
      destruct Hrep as [_ [_ [_ [_ [Hrel _]]]]].
      unfold heap_relation_pair in Hrel.
      unfold PrefixMinValuePair, min_object_of_subset in Hprefix_min.
      destruct Hprefix_min as [Hin Hle].
      unfold heap_entry_set_minimum.
      split.
      * eapply Permutation_in.
        -- apply Permutation_sym. exact Hrel.
        -- exact Hin.
      * intros cost' vertex' HinS.
        specialize (Hle (cost', vertex')).
        assert (HinEntries :
          In (cost', vertex') (HeapEntriesPair cost_before vertex_before n)).
        {
          eapply Permutation_in; [exact Hrel | exact HinS].
        }
        specialize (Hle HinEntries).
        simpl in Hle.
        exact Hle.
    + unfold PopResultPairCore.
      repeat split; try lia; try assumption; try exact Hprefix_min_for_core;
        try exact Hentries_before;
        try exact Hheap_before_order;
        try exact Hroot_in_entries;
        try exact Hroot_cost_in_entries;
        try exact Hentries_after;
        try exact Hheap_after_order;
        try exact Hafter_root_in;
        try (intros [cost' vertex'] Hin';
             specialize (Hroot_le_entries (cost', vertex') Hin');
             simpl in Hroot_le_entries; exact Hroot_le_entries);
        try (intros [cost' vertex'] Hin';
             specialize (Hroot_cost_le_entries (cost', vertex') Hin');
             simpl in Hroot_cost_le_entries; exact Hroot_cost_le_entries);
        try (intros [cost' vertex'] Hin';
             specialize (Hafter_root_le (cost', vertex') Hin');
             simpl in Hafter_root_le; exact Hafter_root_le);
        try (intros _; rewrite <- Hroot; rewrite <- Hout;
             exact Hprefix_min_for_core);
        try (rewrite Zlength_replace_Znth; lia);
        try (rewrite Znth_replace_Znth_Same by lia; reflexivity);
        try exact Hpq_after_whole;
        try (eapply pop_remaining_pair_replace_last_permutation; eauto; lia).
  - exact Hpq_after_whole.
Qed.

Lemma pop_ready_pair_final_write_to_result_with_range :
  forall cost_before vertex_before cost_cur vertex_cur n root_cost out_vertex vertex_bound,
    PopReadyStatePair
      cost_before vertex_before cost_cur vertex_cur n root_cost out_vertex ->
    INT_MIN <= root_cost ->
    root_cost <= INT_MAX ->
    0 <= out_vertex ->
    out_vertex < vertex_bound ->
    vertex_bound <= INT_MAX ->
    (forall pos, 0 <= pos < n ->
      INT_MIN <= Znth pos cost_cur 0 <= INT_MAX) ->
    (forall pos, 0 <= pos < n ->
      INT_MIN <= Znth pos vertex_cur 0 <= INT_MAX) ->
    HeapEntriesVertexRangePair vertex_bound
      (HeapEntriesPair cost_cur vertex_cur (n - 1)) ->
    PopResultPair
      (heap_entries_to_set (HeapEntriesPair cost_before vertex_before n))
      cost_before vertex_before
      (replace_Znth (n - 1) root_cost cost_cur)
      (replace_Znth (n - 1) out_vertex vertex_cur)
      n root_cost out_vertex /\
    PriorityQueuePrefixPair
      (replace_Znth (n - 1) root_cost cost_cur)
      (replace_Znth (n - 1) out_vertex vertex_cur)
      (n - 1)
      (HeapEntriesPair
        (replace_Znth (n - 1) root_cost cost_cur)
        (replace_Znth (n - 1) out_vertex vertex_cur)
        (n - 1)) /\
    HeapEntriesVertexRangePair vertex_bound
      (HeapEntriesPair
        (replace_Znth (n - 1) root_cost cost_cur)
        (replace_Znth (n - 1) out_vertex vertex_cur)
        (n - 1)) /\
    (forall pos, 0 <= pos < n ->
      INT_MIN <= Znth pos (replace_Znth (n - 1) root_cost cost_cur) 0 <= INT_MAX) /\
    (forall pos, 0 <= pos < n ->
      INT_MIN <= Znth pos (replace_Znth (n - 1) out_vertex vertex_cur) 0 <= INT_MAX).
Proof.
  intros cost_before vertex_before cost_cur vertex_cur n root_cost out_vertex vertex_bound
         Hready Hroot_low Hroot_high Hout_low Hout_high Hvertex_bound_high
         Hcost_range Hvertex_range Hvertex_entries.
  unfold PopReadyStatePair in Hready.
  destruct Hready as [Hn Hready].
  destruct Hready as [Hcost_before_len Hready].
  destruct Hready as [Hvertex_before_len Hready].
  destruct Hready as [Hcost_cur_len Hready].
  destruct Hready as [Hvertex_cur_len Hready].
  destruct Hready as [Hpq_before Hready].
  destruct Hready as [Hprefix_min Hready].
  destruct Hready as [Hroot Hready].
  destruct Hready as [Hout Hready].
  destruct Hready as [Hlast_cost Hready].
  destruct Hready as [Hlast_vertex Hready].
  destruct Hready as [Hn1 Hready].
  destruct Hready as [Hn_cost_before Hready].
  destruct Hready as [Hn_vertex_before Hready].
  destruct Hready as [Hn_cost_cur Hready].
  destruct Hready as [Hn_vertex_cur Hready].
  destruct Hready as [Hperm Hpq_cur].
  assert (Hpq_after :
    PriorityQueuePrefixPair
      (replace_Znth (n - 1) root_cost cost_cur)
      (replace_Znth (n - 1) out_vertex vertex_cur)
      (n - 1)
      (HeapEntriesPair
        (replace_Znth (n - 1) root_cost cost_cur)
        (replace_Znth (n - 1) out_vertex vertex_cur)
        (n - 1))).
  {
    eapply priority_queue_prefix_pair_replace_at_end; try lia.
    exact Hpq_cur.
  }
  assert (Hrange_after :
    HeapEntriesVertexRangePair vertex_bound
      (HeapEntriesPair
        (replace_Znth (n - 1) root_cost cost_cur)
        (replace_Znth (n - 1) out_vertex vertex_cur)
        (n - 1))).
  {
    apply heap_entries_vertex_range_pair_replace_at_end; try lia.
    exact Hvertex_entries.
  }
  split.
  - unfold PopResultPair.
    split.
    { unfold heap_representation_pair, heap_relation_pair, heap_entries_to_set,
        list_to_multiset.
      split; [lia|].
      split; [exact Hcost_before_len|].
      split; [exact Hvertex_before_len|].
      split.
      { unfold multiset_size.
        cbn.
        rewrite Zlength_HeapEntriesPair by lia.
        reflexivity. }
      split; [reflexivity|].
      destruct Hpq_before as [_ [Hheap_before _]].
      exact Hheap_before. }
    split.
    { apply PrefixMinValuePair_heap_entry_set_minimum.
      exact Hprefix_min. }
    unfold PopResultPairCore.
    split; [lia|].
    split; [exact Hcost_before_len|].
    split; [exact Hvertex_before_len|].
    split; [rewrite Zlength_replace_Znth; exact Hcost_cur_len|].
    split; [rewrite Zlength_replace_Znth; exact Hvertex_cur_len|].
    split; [exact Hpq_before|].
    split; [exact Hprefix_min|].
    split; [exact Hroot|].
    split; [exact Hout|].
    split; [rewrite Znth_replace_Znth_Same by lia; reflexivity|].
    split; [rewrite Znth_replace_Znth_Same by lia; reflexivity|].
    split; [exact Hpq_after|].
    eapply pop_remaining_pair_replace_last_permutation; eauto.
  - split; [exact Hpq_after|].
    split; [exact Hrange_after|].
    split.
    + intros pos Hpos.
      destruct (Z.eq_dec pos (n - 1)) as [Heq | Hneq].
      * subst pos.
        rewrite Znth_replace_Znth_Same by lia.
        split; [exact Hroot_low | exact Hroot_high].
      * rewrite Znth_replace_Znth_Diff by lia.
        apply Hcost_range.
        exact Hpos.
    + intros pos Hpos.
      destruct (Z.eq_dec pos (n - 1)) as [Heq | Hneq].
      * subst pos.
        rewrite Znth_replace_Znth_Same by lia.
        split; [lia | lia].
      * rewrite Znth_replace_Znth_Diff by lia.
        apply Hvertex_range.
        exact Hpos.
Qed.



















(** * 堆与 Prim的关系 *)
  
Definition heap_entry_matches_candidate
    (g : G) (s : St)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entry : HeapEntry) : Prop :=
  let '(cost, vertex) := entry in
  candidate_vertex g s lowcost edge_parent inf vertex /\
  cost = Znth vertex lowcost 0.

Definition heap_contains_all_candidates
    (g : G) (s : St)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entries : list HeapEntry) : Prop :=
  forall vertex,
    candidate_vertex g s lowcost edge_parent inf vertex ->
    exists cost,
      In (cost, vertex) entries /\
      cost = Znth vertex lowcost 0.

Definition heap_current_entries_are_candidates
    (g : G) (s : St)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entries : list HeapEntry) : Prop :=
  forall cost vertex,
    In (cost, vertex) entries ->
    cost = Znth vertex lowcost 0 ->
    candidate_vertex g s lowcost edge_parent inf vertex.

Definition heap_entries_respect_lowcost
    (lowcost : list Z) (entries : list HeapEntry) : Prop :=
  forall cost vertex,
    In (cost, vertex) entries ->
    Znth vertex lowcost 0 <= cost.

Definition heap_matches_prim_state
    (g : G) (s : St)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entries : list HeapEntry) : Prop :=
  heap_contains_all_candidates g s lowcost edge_parent inf entries /\
  heap_current_entries_are_candidates g s lowcost edge_parent inf entries /\
  heap_entries_respect_lowcost lowcost entries /\
  NoDup entries.

(** 一条有向边在 lazy heap 中对应的候选 entry。 *)
Definition heap_entry_of_directed_edge
    (to_new : list DE) (wt_new : list Z) (de : DE) : HeapEntry :=
  (Znth de wt_new 0, Znth de to_new 0).

(** 堆 entry 的来源：lazy heap 不删除旧候选，所以堆大小不能只靠当前候选点数
    控制。真正的容量事实是：每个堆 entry 要么是初始的 [(0, src)]，
    要么来自某条有向边 [de] 被扫描时压入的
    [(weight_new[de], to_new[de])]。这个谓词只记录来源，不记录具体扫描顺序。 *)
Definition heap_entries_from_graph_edges
    (g : G) (src : V) (to_new : list DE) (wt_new : list Z)
    (entries : list HeapEntry) : Prop :=
  incl entries
    ((0, src) ::
       map (heap_entry_of_directed_edge to_new wt_new)
           (Zrange 0 (2 * graph_edge_count g))).

Lemma heap_entries_from_graph_edges_empty :
  forall g src to_new wt_new,
    heap_entries_from_graph_edges g src to_new wt_new nil.
Proof.
  intros g src to_new wt_new.
  unfold heap_entries_from_graph_edges, incl.
  intros x Hx. inversion Hx.
Qed.

Lemma heap_entries_from_graph_edges_initial :
  forall g src to_new wt_new entries,
    Permutation entries [(0, src)] ->
    heap_entries_from_graph_edges g src to_new wt_new entries.
Proof.
  intros g src to_new wt_new entries Hperm.
  unfold heap_entries_from_graph_edges, incl.
  intros x Hx.
  assert (Hin : In x [(0, src)]).
  { eapply Permutation_in; [exact Hperm | exact Hx]. }
  destruct Hin as [Hx_eq | []].
  subst x. simpl. auto.
Qed.

Lemma heap_entries_from_graph_edges_of_representation :
  forall g src to_new wt_new entries cost vertex size,
    heap_entries_from_graph_edges g src to_new wt_new entries ->
    heap_representation_pair (heap_entries_to_set entries) cost vertex size ->
    heap_entries_from_graph_edges g src to_new wt_new
      (HeapEntriesPair cost vertex size).
Proof.
  intros g src to_new wt_new entries cost vertex size Horigin Hrep.
  unfold heap_entries_from_graph_edges, incl in *.
  intros x Hx.
  apply Horigin.
  unfold heap_representation_pair, heap_relation_pair, heap_entries_to_set,
    list_to_multiset in Hrep.
  destruct Hrep as [_ [_ [_ [_ [Hperm _]]]]].
  eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hx].
Qed.

Lemma heap_entries_from_graph_edges_step :
  forall g src to_new wt_new entries_before entries_after de,
    heap_entries_from_graph_edges g src to_new wt_new entries_before ->
    0 <= de < 2 * graph_edge_count g ->
    Permutation entries_after
      (heap_entry_of_directed_edge to_new wt_new de :: entries_before) ->
    heap_entries_from_graph_edges g src to_new wt_new entries_after.
Proof.
  intros g src to_new wt_new entries_before entries_after de Horigin Hrange Hperm.
  unfold heap_entries_from_graph_edges, incl in *.
  intros x Hx.
  assert (Hin_cons :
    In x ((Znth de wt_new 0, Znth de to_new 0) :: entries_before)).
  { eapply Permutation_in; [exact Hperm | exact Hx]. }
  destruct Hin_cons as [Hx_eq | Hin_before].
  - subst x. right.
    change (Znth de wt_new 0, Znth de to_new 0)
      with (heap_entry_of_directed_edge to_new wt_new de).
    apply in_map.
    rewrite <- In_Zrange.
    exact Hrange.
  - exact (Horigin x Hin_before).
Qed.

Lemma heap_entries_from_graph_edges_keep :
  forall g src to_new wt_new entries_before entries_after,
    heap_entries_from_graph_edges g src to_new wt_new entries_before ->
    entries_after = entries_before ->
    heap_entries_from_graph_edges g src to_new wt_new entries_after.
Proof.
  intros g src to_new wt_new entries_before entries_after Horigin Heq.
  subst entries_after. exact Horigin.
Qed.

Lemma heap_entries_from_graph_edges_pop :
  forall g src to_new wt_new entries_before entries_after cost vertex,
    heap_entries_from_graph_edges g src to_new wt_new entries_before ->
    Permutation entries_before ((cost, vertex) :: entries_after) ->
    heap_entries_from_graph_edges g src to_new wt_new entries_after.
Proof.
  intros g src to_new wt_new entries_before entries_after cost vertex Horigin Hperm.
  unfold heap_entries_from_graph_edges, incl in *.
  intros x Hx.
  apply Horigin.
  eapply Permutation_in; [symmetry; exact Hperm |].
  right. exact Hx.
Qed.

Lemma heap_entries_from_graph_edges_after_pop_result :
  forall g src to_new wt_new
         cost_before vertex_before cost_after vertex_after
         active_cost active_vertex entries_before entries_after
         heap_size cost vertex,
    heap_entries_from_graph_edges g src to_new wt_new entries_before ->
    entries_before = HeapEntriesPair cost_before vertex_before heap_size ->
    active_cost = sublist 0 (heap_size - 1) cost_after ->
    active_vertex = sublist 0 (heap_size - 1) vertex_after ->
    PriorityQueuePrefixPair active_cost active_vertex
      (heap_size - 1) entries_after ->
    PopResultPair (heap_entries_to_set entries_before)
      cost_before vertex_before cost_after vertex_after
      heap_size cost vertex ->
    heap_entries_from_graph_edges g src to_new wt_new entries_after.
Proof.
  intros g src to_new wt_new
         cost_before vertex_before cost_after vertex_after
         active_cost active_vertex entries_before entries_after
         heap_size cost vertex Horigin Hentries_before Hactive_cost
         Hactive_vertex Hpq_active Hpop.
  unfold PriorityQueuePrefixPair in Hpq_active.
  destruct Hpq_active as [Hentries_after _].
  unfold PopResultPair in Hpop.
  destruct Hpop as [_ [_ Hpop]].
  unfold PopResultPairCore in Hpop.
  destruct Hpop as [Hheap_size_pos [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hperm]]]]]]]]]]]].
  subst entries_before active_cost active_vertex entries_after.
  rewrite HeapEntriesPair_sublist_prefix by lia.
  eapply heap_entries_from_graph_edges_pop; eauto.
Qed.

Lemma heap_entries_from_graph_edges_bound :
  forall g src to_new wt_new entries,
    NoDup entries ->
    heap_entries_from_graph_edges g src to_new wt_new entries ->
    0 <= graph_edge_count g ->
    Zlength entries <= 2 * graph_edge_count g + 1.
Proof.
  intros g src to_new wt_new entries Hnodup Horigin Hcount_nonneg.
  unfold heap_entries_from_graph_edges in Horigin.
  pose proof (NoDup_incl_length Hnodup Horigin) as Hlen.
  rewrite Zlength_correct.
  simpl in Hlen.
  rewrite length_map in Hlen.
  assert (Hrange_len :
    Z.of_nat (length (Zrange 0 (2 * graph_edge_count g))) =
    2 * graph_edge_count g).
  { rewrite <- Zlength_correct.
    rewrite Zlength_Zrange by lia. lia. }
  assert (HlenZ :
    Z.of_nat (length entries) <=
    Z.of_nat (S (length (Zrange 0 (2 * graph_edge_count g))))).
  { apply Nat2Z.inj_le. exact Hlen. }
  rewrite Nat2Z.inj_succ in HlenZ.
  rewrite Hrange_len in HlenZ.
  lia.
Qed.

Definition current_heap_min_entry
    (g : G) (s : St)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entries : list HeapEntry)
    (cost : Z) (vertex : V) : Prop :=
  min_object_of_subset Z_op_le
    (fun entry =>
       In entry entries /\
       heap_entry_matches_candidate g s lowcost edge_parent inf entry)
    (fun entry => Some (fst entry))
    (cost, vertex).

Definition heap_pop_selects_min_vertex
    (g : G) (s : St)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entries : list HeapEntry)
    (cost : Z) (vertex : V) : Prop :=
  current_heap_min_entry g s lowcost edge_parent inf entries cost vertex /\
  min_object_of_subset Z_op_le
    (fun v => candidate_vertex g s lowcost edge_parent inf v)
    (fun v => Some (Znth v lowcost 0))
    vertex.

Lemma heap_current_entries_are_candidates_pop_rest :
  forall g s lowcost edge_parent inf entries_before entries_after cost vertex,
    heap_current_entries_are_candidates
      g s lowcost edge_parent inf entries_before ->
    Permutation entries_before ((cost, vertex) :: entries_after) ->
    heap_current_entries_are_candidates
      g s lowcost edge_parent inf entries_after.
Proof.
  intros g s lowcost edge_parent inf entries_before entries_after cost vertex
         Hcurrent Hperm.
  unfold heap_current_entries_are_candidates in *.
  intros cost' vertex' Hin_after Hcost'.
  apply (Hcurrent cost' vertex'); [| exact Hcost'].
  eapply Permutation_in; [symmetry; exact Hperm |].
  right; exact Hin_after.
Qed.

Lemma heap_entries_respect_lowcost_pop_rest :
  forall lowcost entries_before entries_after cost vertex,
    heap_entries_respect_lowcost lowcost entries_before ->
    Permutation entries_before ((cost, vertex) :: entries_after) ->
    heap_entries_respect_lowcost lowcost entries_after.
Proof.
  intros lowcost entries_before entries_after cost vertex Hrespect Hperm.
  unfold heap_entries_respect_lowcost in *.
  intros cost' vertex' Hin_after.
  apply (Hrespect cost' vertex').
  eapply Permutation_in; [symmetry; exact Hperm |].
  right; exact Hin_after.
Qed.

Lemma heap_contains_all_candidates_pop_stale :
  forall g s lowcost edge_parent inf entries_before entries_after cost vertex,
    heap_contains_all_candidates
      g s lowcost edge_parent inf entries_before ->
    Permutation entries_before ((cost, vertex) :: entries_after) ->
    ~ heap_entry_matches_candidate g s lowcost edge_parent inf (cost, vertex) ->
    heap_contains_all_candidates
      g s lowcost edge_parent inf entries_after.
Proof.
  intros g s lowcost edge_parent inf entries_before entries_after cost vertex
         Hcontains Hperm Hstale.
  unfold heap_contains_all_candidates in *.
  intros vertex' Hcand.
  destruct (Hcontains vertex' Hcand) as [cost' [Hin_before Hcost']].
  exists cost'. split; [| exact Hcost'].
  assert (Hin_cons : In (cost', vertex') ((cost, vertex) :: entries_after)).
  { eapply Permutation_in; [exact Hperm | exact Hin_before]. }
  destruct Hin_cons as [Heq | Hin_after].
  - injection Heq as Hcost_eq Hvertex_eq.
    subst cost' vertex'.
    exfalso. apply Hstale.
    unfold heap_entry_matches_candidate.
    split; assumption.
  - exact Hin_after.
Qed.

Lemma heap_matches_prim_state_pop_stale :
  forall g s lowcost edge_parent inf entries_before entries_after cost vertex,
    heap_matches_prim_state
      g s lowcost edge_parent inf entries_before ->
    Permutation entries_before ((cost, vertex) :: entries_after) ->
    ~ heap_entry_matches_candidate g s lowcost edge_parent inf (cost, vertex) ->
    heap_matches_prim_state
      g s lowcost edge_parent inf entries_after.
Proof.
  intros g s lowcost edge_parent inf entries_before entries_after cost vertex
         [Hcontains [Hcurrent [Hrespect Hnodup_before]]] Hperm Hstale.
  split; [| split; [| split]].
  - apply (heap_contains_all_candidates_pop_stale
      g s lowcost edge_parent inf entries_before entries_after cost vertex);
      [exact Hcontains | exact Hperm | exact Hstale].
  - apply (heap_current_entries_are_candidates_pop_rest
      g s lowcost edge_parent inf entries_before entries_after cost vertex);
      [exact Hcurrent | exact Hperm].
  - apply (heap_entries_respect_lowcost_pop_rest
      lowcost entries_before entries_after cost vertex);
      [exact Hrespect | exact Hperm].
  - assert (Hnodup_cons : NoDup ((cost, vertex) :: entries_after)).
    { eapply Permutation_NoDup; [exact Hperm | exact Hnodup_before]. }
    inversion Hnodup_cons as [| ? ? Hnot_in Hnodup_after]; exact Hnodup_after.
Qed.

Lemma heap_size_positive_if_candidate_exists_pair :
  forall g s lowcost edge_parent inf cost vertex size entries n,
    candidate_vertex_exists_in_range n g s lowcost edge_parent inf ->
    heap_matches_prim_state g s lowcost edge_parent inf entries ->
    PriorityQueuePrefixPair cost vertex size entries ->
    size > 0.
Proof.
  intros g s lowcost edge_parent inf cost vertex size entries n
         Hexists Hmatches Hpq.
  unfold candidate_vertex_exists_in_range in Hexists.
  destruct Hexists as [v [_ Hcand]].
  unfold heap_matches_prim_state, heap_contains_all_candidates in Hmatches.
  destruct Hmatches as [Hcontains _].
  destruct (Hcontains v Hcand) as [c [Hin _]].
  unfold PriorityQueuePrefixPair in Hpq.
  destruct Hpq as [Hentries _].
  subst entries.
  destruct (Z_lt_le_dec 0 size) as [Hpos | Hnonpos]; [lia |].
  unfold HeapEntriesPair in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [idx [_ Hidx]].
  rewrite <- In_Zrange in Hidx.
  lia.
Qed.

Lemma heap_entry_not_candidate_if_visited_nonzero :
  forall g s visited lowcost edge_parent inf cost vertex,
    visited_matches_state g s visited ->
    Znth vertex visited 0 <> 0 ->
    ~ heap_entry_matches_candidate g s lowcost edge_parent inf (cost, vertex).
Proof.
  intros g s visited lowcost edge_parent inf cost vertex Hvisited Hnonzero Hentry.
  unfold heap_entry_matches_candidate in Hentry.
  destruct Hentry as [Hcandidate _].
  unfold candidate_vertex in Hcandidate.
  destruct Hcandidate as [Hin [Hnot_valid _]].
  apply Hnot_valid.
  apply Hvisited; assumption.
Qed.

Lemma heap_entry_not_candidate_if_cost_stale :
  forall g s lowcost edge_parent inf cost vertex,
    cost <> Znth vertex lowcost 0 ->
    ~ heap_entry_matches_candidate g s lowcost edge_parent inf (cost, vertex).
Proof.
  intros g s lowcost edge_parent inf cost vertex Hneq Hentry.
  unfold heap_entry_matches_candidate in Hentry.
  destruct Hentry as [_ Hcost].
  contradiction.
Qed.

Lemma heap_pop_current_selects_min_vertex :
  forall g s lowcost edge_parent inf
         entries_before entries_after cost vertex,
    heap_matches_prim_state
      g s lowcost edge_parent inf entries_before ->
    min_object_of_subset Z_op_le
      (fun entry => In entry entries_before)
      (fun entry => Some (fst entry))
      (cost, vertex) ->
    Permutation entries_before ((cost, vertex) :: entries_after) ->
    heap_entry_matches_candidate g s lowcost edge_parent inf (cost, vertex) ->
    heap_pop_selects_min_vertex
      g s lowcost edge_parent inf entries_before cost vertex.
Proof.
  intros g s lowcost edge_parent inf entries_before entries_after cost vertex
         [Hcontains [Hcurrent [Hrespect _]]] Hmin _ Hentry.
  unfold heap_pop_selects_min_vertex.
  split.
  - unfold current_heap_min_entry.
    unfold min_object_of_subset in *.
    destruct Hmin as [Hin_min Hle_min].
    split.
    + split; [exact Hin_min | exact Hentry].
    + intros [cost' vertex'] [Hin_entry _].
      exact (Hle_min (cost', vertex') Hin_entry).
  - unfold min_object_of_subset.
    unfold heap_entry_matches_candidate in Hentry.
    destruct Hentry as [Hcand_vertex Hcost_vertex].
    split; [exact Hcand_vertex |].
    intros vertex' Hcand'.
    destruct (Hcontains vertex' Hcand') as [cost' [Hin' Hcost']].
    unfold min_object_of_subset in Hmin.
    destruct Hmin as [_ Hle_min].
    specialize (Hle_min (cost', vertex') Hin').
    simpl in Hle_min.
    rewrite Hcost_vertex in Hle_min.
    rewrite Hcost' in Hle_min.
    exact Hle_min.
Qed.

Lemma heap_pop_result_current_selects_min_vertex :
  forall g s lowcost edge_parent inf
         cost_before vertex_before cost_after vertex_after
         heap_size cost vertex,
    heap_matches_prim_state
      g s lowcost edge_parent inf
      (HeapEntriesPair cost_before vertex_before heap_size) ->
    PopResultPair
      (heap_entries_to_set (HeapEntriesPair cost_before vertex_before heap_size))
      cost_before vertex_before cost_after vertex_after
      heap_size cost vertex ->
    heap_entry_matches_candidate g s lowcost edge_parent inf (cost, vertex) ->
    heap_pop_selects_min_vertex
      g s lowcost edge_parent inf
      (HeapEntriesPair cost_before vertex_before heap_size) cost vertex.
Proof.
  intros g s lowcost edge_parent inf
         cost_before vertex_before cost_after vertex_after
         heap_size cost vertex Hmatch Hpop Hentry.
  unfold PopResultPair in Hpop.
  destruct Hpop as [_ [_ Hpop]].
  unfold PopResultPairCore in Hpop.
  destruct Hpop as
    [_ [_ [_ [_ [_ [_ [Hmin [_ [_ [_ [_ [_ Hperm]]]]]]]]]]]].
  eapply (heap_pop_current_selects_min_vertex
    g s lowcost edge_parent inf
    (HeapEntriesPair cost_before vertex_before heap_size)
    (HeapEntriesPair cost_after vertex_after (heap_size - 1))
    cost vertex); eauto.
  Unshelve. all: eauto.
Qed.

Lemma heap_pop_result_unvisited_entry_matches_candidate :
  forall n m from to wt g s visited lowcost edge_parent inf
         cost_before vertex_before cost_after vertex_after
         heap_size entries_before cost vertex,
    array_graph n m from to wt g ->
    visited_matches_state g s visited ->
    lowcost_parent_match g s lowcost edge_parent inf ->
    heap_matches_prim_state g s lowcost edge_parent inf entries_before ->
    PriorityQueuePrefixPair cost_before vertex_before heap_size entries_before ->
    HeapEntriesVertexRangePair n entries_before ->
    PopResultPair (heap_entries_to_set entries_before)
      cost_before vertex_before cost_after vertex_after
      heap_size cost vertex ->
    candidate_vertex_exists_in_range n g s lowcost edge_parent inf ->
    Znth vertex visited 0 = 0 ->
    cost = Znth vertex lowcost 0 /\
    heap_entry_matches_candidate g s lowcost edge_parent inf (cost, vertex).
Proof.
  intros n m from to wt g s visited lowcost edge_parent inf
         cost_before vertex_before cost_after vertex_after
         heap_size entries_before cost vertex
         Hgraph Hvisited Hlow Hheap Hpq Hrange Hpop Hexists Hvisited_zero.
  destruct Hheap as [Hcontains [_ [Hrespect _]]].
  unfold PopResultPair in Hpop.
  destruct Hpop as [_ [_ Hpop]].
  unfold PopResultPairCore in Hpop.
  destruct Hpop as [_ [_ [_ [_ [_ [Hpq_pop [Hmin [_ [_ [_ [_ [_ _]]]]]]]]]]]].
  unfold PriorityQueuePrefixPair in Hpq.
  destruct Hpq as [Hentries _].
  rewrite <- Hentries in Hmin.
  unfold PrefixMinValuePair, min_object_of_subset in Hmin.
  destruct Hmin as [Hin_root Hle_root].
  assert (Hvertex_graph : In vertex (graph_vertices g)).
  {
    apply array_graph_vertex_in with (n := n) (m := m) (from := from) (to := to) (wt := wt).
    - exact Hgraph.
    - apply Hrange with (cost := cost). exact Hin_root.
  }
  assert (Hvertex_out : ~ vvalid s.(Prim.graph_in_state) vertex).
  {
    intro Hvalid.
    destruct (Hvisited vertex Hvertex_graph) as [_ Hvalid_to_visited].
    specialize (Hvalid_to_visited Hvalid).
    rewrite Hvisited_zero in Hvalid_to_visited.
    contradiction Hvalid_to_visited; reflexivity.
  }
  destruct Hlow as [_ Hlow].
  specialize (Hlow vertex Hvertex_graph Hvertex_out).
  destruct Hlow as [Hparent | Hnone].
  - destruct Hparent as
      [de [Hde_eq [Hde_not_minus [Hde_range [Hlow_lt [Hmin_edge Hweight]]]]]].
    assert (Hcand_vertex :
      candidate_vertex g s lowcost edge_parent inf vertex).
    {
      unfold candidate_vertex, vertex_has_parent_edge.
      split; [exact Hvertex_graph |].
      split; [exact Hvertex_out |].
      rewrite Hde_eq.
      split; [exact Hde_not_minus |].
      split; [exact Hde_range |].
      split; [exact Hlow_lt |].
      split; [exact Hmin_edge | exact Hweight].
    }
    destruct (Hcontains vertex Hcand_vertex) as [current_cost [Hin_current Hcurrent_cost]].
    specialize (Hle_root (current_cost, vertex) Hin_current).
    simpl in Hle_root.
    specialize (Hrespect cost vertex Hin_root).
    rewrite Hcurrent_cost in Hle_root.
    split.
    + lia.
    + unfold heap_entry_matches_candidate.
      split; [exact Hcand_vertex | lia].
  - destruct Hnone as [_ [_ Hlow_inf]].
    destruct Hexists as [candidate [Hin_candidate Hcand_candidate]].
    destruct (Hcontains candidate Hcand_candidate) as
      [candidate_cost [Hin_candidate_heap Hcandidate_cost]].
    specialize (Hle_root (candidate_cost, candidate) Hin_candidate_heap).
    simpl in Hle_root.
    specialize (Hrespect cost vertex Hin_root).
    rewrite Hlow_inf in Hrespect.
    unfold candidate_vertex, vertex_has_parent_edge in Hcand_candidate.
    destruct Hcand_candidate as [_ [_ [_ [_ [Hcandidate_low _]]]]].
    rewrite Hcandidate_cost in Hle_root.
    lia.
Qed.

Lemma heap_pop_selects_min_vertex_to_min_vertex_in_range :
  forall n m from to wt g s lowcost edge_parent inf entries cost vertex,
    array_graph n m from to wt g ->
    heap_pop_selects_min_vertex
      g s lowcost edge_parent inf entries cost vertex ->
    min_vertex_in_range g s n inf vertex lowcost edge_parent.
Proof.
  intros n m from to wt g s lowcost edge_parent inf entries cost vertex
         Hgraph Hselect.
  unfold heap_pop_selects_min_vertex in Hselect.
  destruct Hselect as [_ Hmin_vertex].
  unfold min_vertex_in_range.
  right.
  unfold min_object_of_subset in Hmin_vertex.
  destruct Hmin_vertex as [Hcand Hle].
  split; [exact Hcand |].
  split.
  - rewrite <- In_Zrange.
    destruct Hcand as [Hvin _].
    eapply array_graph_vertex_range; eauto.
  - unfold min_object_of_subset.
    split.
    + split.
      * rewrite <- In_Zrange.
        destruct Hcand as [Hvin _].
        eapply array_graph_vertex_range; eauto.
      * exact Hcand.
    + intros v [_ Hcand_v].
      exact (Hle v Hcand_v).
Qed.

Lemma heap_pop_selects_parent_edge_is_min_cut_edge :
  forall n m from to wt g s lowcost edge_parent inf entries cost vertex,
    array_graph n m from to wt g ->
    lowcost_parent_match g s lowcost edge_parent inf ->
    heap_pop_selects_min_vertex
      g s lowcost edge_parent inf entries cost vertex ->
    selected_parent_edge_is_min_cut_edge g s edge_parent vertex.
Proof.
  intros n m from to wt g s lowcost edge_parent inf entries cost vertex
         Hgraph Hlow Hselect.
  eapply min_vertex_parent_is_min_cut_edge with
    (n := n) (m := m) (from := from) (to := to) (wt := wt)
    (lowcost := lowcost) (inf := inf); eauto.
  - eapply heap_pop_selects_min_vertex_to_min_vertex_in_range; eauto.
  - unfold heap_pop_selects_min_vertex in Hselect.
    destruct Hselect as [_ Hmin].
    unfold min_object_of_subset in Hmin.
    destruct Hmin as [Hcand _].
    destruct Hcand as [Hvin _].
    pose proof (array_graph_vertex_range n m from to wt g vertex Hgraph Hvin).
    lia.
Qed.

(** 把 [minIndex] 标记为 visited 后，其他顶点在 [s_before]/[s_after]
    中的 vvalid 状态等价。 *)
Lemma visited_update_other_vertex_valid :
  forall g s_before s_after visited minIndex w,
    In w (graph_vertices g) ->
    0 <= minIndex < Zlength visited ->
    0 <= w < Zlength visited ->
    visited_matches_state g s_before visited ->
    visited_matches_state g s_after (replace_Znth minIndex 1 visited) ->
    w <> minIndex ->
    (vvalid s_after.(Prim.graph_in_state) w <->
     vvalid s_before.(Prim.graph_in_state) w).
Proof.
  intros g s_before s_after visited minIndex w
         Hw_graph Hmin_range Hw_range Hv_before Hv_after Hw_ne.
  unfold visited_matches_state in *.
  pose proof (Hv_after w Hw_graph) as Hafter.
  pose proof (Hv_before w Hw_graph) as Hbefore.
  rewrite Znth_replace_Znth_diff_local
    with (i := minIndex) (j := w) (v := 1) (l := visited) in Hafter
    by (first [exact Hmin_range | exact Hw_range | lia]).
  tauto.
Qed.


(** * 扫描邻接链时把新候选同步放进堆

    主循环扫描 [minIndex] 的邻接链时，每当一条有向边把某个顶点的
    [lowcost] 从 [inf] 或更大值压低成新的权重，就要把
    [(new_weight, vertex)] 推进堆。扫描前缀只描述了 [lowcost]/[edge_parent]
    怎么随扫描变化，还需要同时记录堆的前缀更新，扫描到 -1 之后才能推出
    完整的 [heap_matches_prim_state]。 *)

(** 扫描一条有向边时，堆的更新：若该边触发 [lowcost] 更新，则把
    [(weight, vertex)] 推进堆；否则堆不变。 *)
Definition heap_update_one_directed_edge
    (g : G) (s_next : St)
    (to_new : list DE) (wt_new : list Z)
    (lowcost_in : list Z) (de : DE)
    (heap_entries_in heap_entries_out : list HeapEntry) : Prop :=
  let v := Znth de to_new 0 in
  let w := Znth de wt_new 0 in
  (is_cut_edge_to_vertex g s_next v (de / 2) /\
   w < Znth v lowcost_in 0 /\
   Permutation heap_entries_out ((w, v) :: heap_entries_in)) \/
  ((~ is_cut_edge_to_vertex g s_next v (de / 2) \/
    Znth v lowcost_in 0 <= w) /\
   heap_entries_out = heap_entries_in).

Lemma heap_update_one_directed_edge_origin :
  forall g src s_next to_new wt_new lowcost_in de
         heap_entries_in heap_entries_out,
    heap_entries_from_graph_edges g src to_new wt_new heap_entries_in ->
    0 <= de < 2 * graph_edge_count g ->
    heap_update_one_directed_edge
      g s_next to_new wt_new lowcost_in de
      heap_entries_in heap_entries_out ->
    heap_entries_from_graph_edges g src to_new wt_new heap_entries_out.
Proof.
  intros g src s_next to_new wt_new lowcost_in de
         heap_entries_in heap_entries_out Horigin Hrange Hupdate.
  unfold heap_update_one_directed_edge in Hupdate.
  destruct Hupdate as [[_ [_ Hperm]] | [_ Heq]].
  - eapply heap_entries_from_graph_edges_step; eauto.
  - eapply heap_entries_from_graph_edges_keep; eauto.
Qed.

(** 扫描一串有向边时，[lowcost]/[edge_parent]/堆 的并行更新。
    这一版把三个分量放在同一个归纳里，避免证明时还要手工对齐两条链。 *)
Inductive scan_directed_edges_full_update
    (g : G) (s_next : St)
    (to_new : list DE) (wt_new : list Z) :
    list DE ->
    list Z -> list DE -> list HeapEntry ->
    list Z -> list DE -> list HeapEntry -> Prop :=
| scan_directed_edges_full_update_nil :
    forall lowcost edge_parent heap_entries,
      scan_directed_edges_full_update
        g s_next to_new wt_new nil
        lowcost edge_parent heap_entries
        lowcost edge_parent heap_entries
| scan_directed_edges_full_update_cons :
    forall de rest
           lowcost0 edge_parent0 heap_entries0
           lowcost1 edge_parent1 heap_entries1
           lowcost2 edge_parent2 heap_entries2,
      scan_one_directed_edge_update
        g s_next to_new wt_new
        lowcost0 edge_parent0 de lowcost1 edge_parent1 ->
      heap_update_one_directed_edge
        g s_next to_new wt_new lowcost0 de heap_entries0 heap_entries1 ->
      scan_directed_edges_full_update
        g s_next to_new wt_new rest
        lowcost1 edge_parent1 heap_entries1
        lowcost2 edge_parent2 heap_entries2 ->
      scan_directed_edges_full_update
        g s_next to_new wt_new (de :: rest)
        lowcost0 edge_parent0 heap_entries0
        lowcost2 edge_parent2 heap_entries2.

(** 扫描 [minIndex] 邻接链的前缀时，lowcost/edge_parent/堆 的并行更新。
    与 [scan_minIndex_adjacency_prefix_update] 结构一致，只是额外带堆。 *)
Definition scan_minIndex_adjacency_heap_prefix_update
    (g : G) (s_next : St)
    (from_new first link to_new : list DE) (wt_new : list Z)
    (minIndex : V) (current_e : DE)
    (lowcost_before : list Z) (edge_parent_before : list DE)
    (heap_entries_before : list HeapEntry)
    (lowcost_current : list Z) (edge_parent_current : list DE)
    (heap_entries_current : list HeapEntry) : Prop :=
  exists scanned_edges remaining_edges : list DE,
    is_first_link_chain link first minIndex (scanned_edges ++ remaining_edges) /\
    is_link_chain link current_e remaining_edges /\
    Permutation (scanned_edges ++ remaining_edges)
      (vertex_directed_edges g from_new minIndex) /\
    scan_directed_edges_full_update
      g s_next to_new wt_new scanned_edges
      lowcost_before edge_parent_before heap_entries_before
      lowcost_current edge_parent_current heap_entries_current.

(** 扫描完 [minIndex] 的全部邻接边后（[current_e = -1]），
    lowcost/edge_parent/堆 的完整更新。 *)
Definition scan_minIndex_adjacency_heap_update
    (g : G) (s_next : St)
    (from_new first link to_new : list DE) (wt_new : list Z)
    (minIndex : V)
    (lowcost_before : list Z) (edge_parent_before : list DE)
    (heap_entries_before : list HeapEntry)
    (lowcost_after : list Z) (edge_parent_after : list DE)
    (heap_entries_after : list HeapEntry) : Prop :=
  exists scanned_edges : list DE,
    is_first_link_chain link first minIndex scanned_edges /\
    Permutation scanned_edges (vertex_directed_edges g from_new minIndex) /\
    scan_directed_edges_full_update
      g s_next to_new wt_new scanned_edges
      lowcost_before edge_parent_before heap_entries_before
      lowcost_after edge_parent_after heap_entries_after.

Lemma scan_directed_edges_update_lengths_heap_lib :
  forall g s_next to_new wt_new scanned_edges
         lowcost_before edge_parent_before
         lowcost_after edge_parent_after,
    scan_directed_edges_update
      g s_next to_new wt_new scanned_edges
      lowcost_before edge_parent_before
      lowcost_after edge_parent_after ->
    Zlength lowcost_after = Zlength lowcost_before /\
    Zlength edge_parent_after = Zlength edge_parent_before.
Proof.
  intros g s_next to_new wt_new scanned_edges
         lowcost_before edge_parent_before
         lowcost_after edge_parent_after Hscan.
  induction Hscan.
  - split; reflexivity.
  - destruct (scan_one_directed_edge_update_lengths
                g s_next to_new wt_new
                lowcost0 edge_parent0 de lowcost1 edge_parent1 H)
      as [Hlow_one Hparent_one].
    destruct IHHscan as [Hlow_rest Hparent_rest].
    split; lia.
Qed.

Lemma scan_minIndex_adjacency_prefix_update_lengths_heap_lib :
  forall g s_next from_new first link to_new wt_new minIndex current_e
         lowcost_before edge_parent_before
         lowcost_current edge_parent_current,
    scan_minIndex_adjacency_prefix_update
      g s_next from_new first link to_new wt_new
      minIndex current_e
      lowcost_before edge_parent_before
      lowcost_current edge_parent_current ->
    Zlength lowcost_current = Zlength lowcost_before /\
    Zlength edge_parent_current = Zlength edge_parent_before.
Proof.
  intros g s_next from_new first link to_new wt_new minIndex current_e
         lowcost_before edge_parent_before
         lowcost_current edge_parent_current Hprefix.
  unfold scan_minIndex_adjacency_prefix_update in Hprefix.
  destruct Hprefix as
    [scanned_edges [remaining_edges
      [_ [_ [_ Hscan]]]]].
  eapply scan_directed_edges_update_lengths_heap_lib.
  exact Hscan.
Qed.

(** 参数化版本的候选点：把 [is_min_cut_edge_to_vertex] 换成
    “在 [edge_for_vertex] 集合中权重最小的边”。扫描过程中该集合只包含
    已经扫描过的边，扫描完成后实例化回真正的 min-cut 边。 *)
Definition heap_contains_all_candidates_by
    (g : G) (s : St)
    (edge_for_vertex : V -> E -> Prop)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entries : list HeapEntry) : Prop :=
  forall vertex,
    candidate_vertex_by g s edge_for_vertex lowcost edge_parent inf vertex ->
    exists cost,
      In (cost, vertex) entries /\
      cost = Znth vertex lowcost 0.

Definition heap_current_entries_are_candidates_by
    (g : G) (s : St)
    (edge_for_vertex : V -> E -> Prop)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entries : list HeapEntry) : Prop :=
  forall cost vertex,
    In (cost, vertex) entries ->
    cost = Znth vertex lowcost 0 ->
    candidate_vertex_by g s edge_for_vertex lowcost edge_parent inf vertex.

Definition heap_matches_prim_state_by
    (g : G) (s : St)
    (edge_for_vertex : V -> E -> Prop)
    (lowcost : list Z) (edge_parent : list DE)
    (inf : Z) (entries : list HeapEntry) : Prop :=
  heap_contains_all_candidates_by g s edge_for_vertex lowcost edge_parent inf entries /\
  heap_current_entries_are_candidates_by g s edge_for_vertex lowcost edge_parent inf entries /\
  heap_entries_respect_lowcost lowcost entries /\
  NoDup entries.

(** 把 [minIndex] 标记为 visited 后，其他顶点在 [s_before] 下的候选性
    等价于在 [s_after] 下、只考虑 [s_before] cut 边的参数化候选性。 *)
Lemma candidate_vertex_pop_iff :
  forall g s_before s_after visited lowcost edge_parent inf minIndex w,
    In w (graph_vertices g) ->
    0 <= minIndex < Zlength visited ->
    0 <= w < Zlength visited ->
    visited_matches_state g s_before visited ->
    visited_matches_state g s_after (replace_Znth minIndex 1 visited) ->
    w <> minIndex ->
    (candidate_vertex g s_before lowcost edge_parent inf w <->
     candidate_vertex_by g s_after
       (fun v e => is_cut_edge_to_vertex g s_before v e)
       lowcost edge_parent inf w).
Proof.
  intros g s_before s_after visited lowcost edge_parent inf minIndex w
         Hw_graph Hmin_range Hw_range Hv_before Hv_after Hw_ne.
  unfold candidate_vertex, candidate_vertex_by, vertex_has_parent_edge.
  unfold is_min_cut_edge_to_vertex.
  split.
  - intros [Hwg [Hnv Hparent]].
    split; [exact Hwg |].
    split.
    + intro Hvalid_after.
      apply Hnv.
      apply (proj1 (visited_update_other_vertex_valid
        g s_before s_after visited minIndex w Hw_graph
        Hmin_range Hw_range Hv_before Hv_after Hw_ne)).
      exact Hvalid_after.
    + destruct Hparent as
        [Hde_ne [Hde_range [Hlow_lt [Hmin Hweight]]]].
      split; [exact Hde_ne |].
      split; [exact Hde_range |].
      split; [exact Hlow_lt |].
      split; [exact Hmin | exact Hweight].
  - intros [Hwg [Hnv Hparent]].
    split; [exact Hwg |].
    split.
    + intro Hvalid_before.
      apply Hnv.
      apply (proj2 (visited_update_other_vertex_valid
        g s_before s_after visited minIndex w Hw_graph
        Hmin_range Hw_range Hv_before Hv_after Hw_ne)).
      exact Hvalid_before.
    + destruct Hparent as
        [Hde_ne [Hde_range [Hlow_lt [Hmin Hweight]]]].
      split; [exact Hde_ne |].
      split; [exact Hde_range |].
      split; [exact Hlow_lt |].
      split; [exact Hmin | exact Hweight].
Qed.

(** pop 出被选中的最小候选并把 [minIndex] 标记为 visited 后，
    pop 后的堆匹配 [s_after]（只考虑 [s_before] 的 cut 边）。 *)
Lemma heap_matches_prim_state_pop_selected_min :
  forall n m from to wt g src i s_before s_after
         from_new to_new edge_parent lowcost visited inf
         entries_before entries_after cost minIndex,
    array_graph n m from to wt g ->
    Zlength visited = n ->
    visited_matches_state g s_before visited ->
    lowcost_parent_match g s_before lowcost edge_parent inf ->
    heap_matches_prim_state g s_before lowcost edge_parent inf entries_before ->
    heap_pop_selects_min_vertex
      g s_before lowcost edge_parent inf entries_before cost minIndex ->
    Permutation entries_before ((cost, minIndex) :: entries_after) ->
    selected_state_after_add g src i n s_before s_after
      from_new to_new edge_parent lowcost visited minIndex ->
    heap_matches_prim_state_by g s_after
      (fun v e => is_cut_edge_to_vertex g s_before v e)
      lowcost edge_parent inf entries_after.
Proof.
  intros n m from to wt g src i s_before s_after
         from_new to_new edge_parent lowcost visited inf
         entries_before entries_after cost minIndex
         Hgraph Hvisited_len Hvisited_before Hlow Hmatch Hpop Hperm Hstate.
  destruct Hmatch as [Hcontains_before [Hcurrent_before [Hrespect_before Hnodup_before]]].
  assert (Hnodup_cons : NoDup ((cost, minIndex) :: entries_after)).
  { eapply Permutation_NoDup; [exact Hperm | exact Hnodup_before]. }
  inversion Hnodup_cons as [| ? ? Hnot_after Hnodup_after].
  pose proof (selected_state_after_add_visited g src i n s_before s_after
    from_new to_new edge_parent lowcost visited minIndex Hstate) as Hvisited_after.
  split; [| split; [| split]].
  - intros w Hcand_after.
    assert (Hw_ne : w <> minIndex).
    { intro Hw_eq; subst w.
      unfold candidate_vertex_by in Hcand_after.
      destruct Hcand_after as [_ [Hnot_valid _]].
      apply Hnot_valid.
      eapply selected_state_after_add_minIndex_vvalid; eauto. }
    assert (Hw_graph : In w (graph_vertices g)).
    { unfold candidate_vertex_by in Hcand_after.
      destruct Hcand_after as [Hw_graph _]. exact Hw_graph. }
    assert (Hw_range : 0 <= w < Zlength visited).
    { rewrite Hvisited_len.
      eapply array_graph_vertex_range.
      - exact Hgraph.
      - exact Hw_graph. }
    assert (Hmin_range : 0 <= minIndex < Zlength visited).
    { rewrite Hvisited_len.
      eapply array_graph_vertex_range.
      - exact Hgraph.
      - unfold heap_pop_selects_min_vertex in Hpop.
        destruct Hpop as [_ Hminv].
        unfold min_object_of_subset in Hminv.
        destruct Hminv as [Hcand _].
        unfold candidate_vertex in Hcand.
        destruct Hcand as [Hmin_graph _]. exact Hmin_graph. }
    assert (Hcand_before : candidate_vertex g s_before lowcost edge_parent inf w).
    { apply (proj2 (candidate_vertex_pop_iff
        g s_before s_after visited lowcost edge_parent inf minIndex w
        Hw_graph Hmin_range Hw_range Hvisited_before Hvisited_after Hw_ne)).
      exact Hcand_after. }
    destruct (Hcontains_before w Hcand_before) as [cost_w [Hin_before Hcost_w]].
    exists cost_w. split; [| exact Hcost_w].
    assert (Hin_cons : In (cost_w, w) ((cost, minIndex) :: entries_after)).
    { eapply Permutation_in; [exact Hperm | exact Hin_before]. }
    destruct Hin_cons as [Heq | Hin_after]; [| exact Hin_after].
    injection Heq as Hcost_eq Hvertex_eq.
    subst w. contradiction.
  - intros cost_w w Hin_after Hcost_w.
    assert (Hin_before : In (cost_w, w) entries_before).
    { eapply Permutation_in; [symmetry; exact Hperm | right; exact Hin_after]. }
    assert (Hw_ne : w <> minIndex).
    { intro Hw_eq; subst w.
      assert (Hcost_min : cost = Znth minIndex lowcost 0).
      { unfold heap_pop_selects_min_vertex in Hpop.
        destruct Hpop as [Hmin_entry _].
        unfold current_heap_min_entry in Hmin_entry.
        destruct Hmin_entry as [[_ [_ Hcost_pop]] _].
        exact Hcost_pop. }
      assert (Hcost_w_eq : cost_w = cost)
        by (rewrite Hcost_w; symmetry; exact Hcost_min).
      apply Hnot_after.
      rewrite <- Hcost_w_eq. exact Hin_after. }
    assert (Hcand_before : candidate_vertex g s_before lowcost edge_parent inf w).
    { apply (Hcurrent_before cost_w w Hin_before Hcost_w). }
    pose proof Hcand_before as Hcand_before_copy.
    unfold candidate_vertex in Hcand_before_copy.
    destruct Hcand_before_copy as [Hw_graph _].
    assert (Hw_range : 0 <= w < Zlength visited).
    { rewrite Hvisited_len.
      eapply array_graph_vertex_range.
      - exact Hgraph.
      - exact Hw_graph. }
    assert (Hmin_range : 0 <= minIndex < Zlength visited).
    { rewrite Hvisited_len.
      eapply array_graph_vertex_range.
      - exact Hgraph.
      - unfold heap_pop_selects_min_vertex in Hpop.
        destruct Hpop as [_ Hminv].
        unfold min_object_of_subset in Hminv.
        destruct Hminv as [Hcand _].
        unfold candidate_vertex in Hcand.
        destruct Hcand as [Hmin_graph _]. exact Hmin_graph. }
    apply (proj1 (candidate_vertex_pop_iff
      g s_before s_after visited lowcost edge_parent inf minIndex w
      Hw_graph Hmin_range Hw_range Hvisited_before Hvisited_after Hw_ne)).
    exact Hcand_before.
  - intros cost_w w Hin_after.
    apply (Hrespect_before cost_w w).
    eapply Permutation_in; [symmetry; exact Hperm | right; exact Hin_after].
  - exact Hnodup_after.
Qed.

(** 把非参数化的 heap 匹配实例化成参数化版本（edge_for_vertex =
    is_cut_edge_to_vertex）。 *)
Lemma heap_matches_prim_state_to_by :
  forall g s lowcost edge_parent inf entries,
    heap_matches_prim_state g s lowcost edge_parent inf entries ->
    heap_matches_prim_state_by
      g s (fun v e => is_cut_edge_to_vertex g s v e)
      lowcost edge_parent inf entries.
Proof.
  intros g s lowcost edge_parent inf entries Hmatch.
  unfold heap_matches_prim_state, heap_matches_prim_state_by in *.
  unfold heap_contains_all_candidates, heap_contains_all_candidates_by in *.
  unfold heap_current_entries_are_candidates,
    heap_current_entries_are_candidates_by in *.
  destruct Hmatch as [Hcontains [Hcurrent [Hrespect Hnodup]]].
  split; [| split; [| split]].
  - intros vertex Hcand.
    apply Hcontains.
    unfold candidate_vertex, candidate_vertex_by, vertex_has_parent_edge in *.
    unfold is_min_cut_edge_to_vertex in *.
    tauto.
  - intros cost vertex Hin Hcost.
    apply (Hcurrent cost vertex); [exact Hin | exact Hcost].
  - exact Hrespect.
  - exact Hnodup.
Qed.

(** 从 [lowcost_parent_match_by] 的 eligible 分支恢复参数化候选点。 *)
Lemma candidate_vertex_by_of_lowcost :
  forall g s edge_for_vertex lowcost edge_parent inf v,
    In v (graph_vertices g) ->
    ~ vvalid s.(Prim.graph_in_state) v ->
    Znth v lowcost 0 < inf ->
    lowcost_parent_match_by
      g (fun v' => ~ vvalid s.(Prim.graph_in_state) v')
      edge_for_vertex lowcost edge_parent inf ->
    candidate_vertex_by g s edge_for_vertex lowcost edge_parent inf v.
Proof.
  intros g s edge_for_vertex lowcost edge_parent inf v
         Hv_graph Hv_out Hlow_lt Hmatch.
  unfold candidate_vertex_by.
  split; [exact Hv_graph |].
  split; [exact Hv_out |].
  unfold lowcost_parent_match_by in Hmatch.
  destruct Hmatch as [_ Hmatch].
  specialize (Hmatch v Hv_graph Hv_out).
  destruct Hmatch as
    [[de [Hparent [Hde [Hde_range [Hlow [Hmin Hweight]]]]]]
    | [Hnone [Hparent Hlow_eq]]].
  - simpl.
    split; [rewrite Hparent; exact Hde |].
    split; [rewrite Hparent; exact Hde_range |].
    split; [exact Hlow |].
    split; [rewrite Hparent; exact Hmin |].
    rewrite Hparent; exact Hweight.
  - exfalso.
    rewrite Hlow_eq in Hlow_lt.
    lia.
Qed.

(** 在 edge_for_vertex 集合里加入一条权重不更优的边，不改变最小元。 *)
Lemma min_object_of_subset_add_non_better :
  forall g edge_for_vertex de w e_min,
    min_object_of_subset Z_op_le edge_for_vertex (weight g) e_min ->
    weight g de = Some w ->
    Z_op_le (weight g e_min) (weight g de) ->
    min_object_of_subset
      Z_op_le (fun e => edge_for_vertex e \/ e = de) (weight g) e_min.
Proof.
  intros g edge_for_vertex de w e_min Hmin Hweight_de Hle.
  unfold min_object_of_subset in *.
  destruct Hmin as [Hmember Hmin_le].
  split.
  - left; exact Hmember.
  - intros e He.
    destruct He as [Hold | Hde].
    + exact (Hmin_le e Hold).
    + subst e.
      rewrite Hweight_de.
      rewrite Hweight_de in Hle.
      simpl in Hle.
      exact Hle.
Qed.

(** 若扫描边指向的顶点与候选顶点不同，则把它加入 edge_for_vertex
    不改变候选。 *)
Lemma candidate_vertex_by_add_other_vertex :
  forall g s to_new edge_for_vertex de lowcost edge_parent inf vertex,
    candidate_vertex_by
      g s (add_scanned_edge_for_vertex g s to_new edge_for_vertex de)
      lowcost edge_parent inf vertex ->
    vertex <> Znth de to_new 0 ->
    candidate_vertex_by g s edge_for_vertex lowcost edge_parent inf vertex.
Proof.
  intros g s to_new edge_for_vertex de lowcost edge_parent inf vertex
         Hcand Hneq.
  unfold candidate_vertex_by in *.
  destruct Hcand as [Hv_graph [Hv_out Hparent_edge]].
  split; [exact Hv_graph |].
  split; [exact Hv_out |].
  simpl in *.
  destruct Hparent_edge as
    [Hde_ne [Hde_range [Hlow [Hmin Hweight]]]].
  split; [exact Hde_ne |].
  split; [exact Hde_range |].
  split; [exact Hlow |].
  split.
  - unfold add_scanned_edge_for_vertex in Hmin.
    unfold min_object_of_subset in *.
    destruct Hmin as [Hmember Hmin_le].
    split.
    + destruct Hmember as [Hold | [Hv_eq _]].
      * exact Hold.
      * exfalso. apply Hneq. exact Hv_eq.
    + intros e Hold.
      exact (Hmin_le e (or_introl Hold)).
  - exact Hweight.
Qed.

(** 若候选顶点不是扫描边指向的顶点，则把该扫描边加入
    edge_for_vertex 不改变候选（正向）。 *)
Lemma candidate_vertex_by_add_other_vertex_forw :
  forall g s to_new edge_for_vertex de lowcost edge_parent inf vertex,
    vertex <> Znth de to_new 0 ->
    candidate_vertex_by g s edge_for_vertex lowcost edge_parent inf vertex ->
    candidate_vertex_by
      g s (add_scanned_edge_for_vertex g s to_new edge_for_vertex de)
      lowcost edge_parent inf vertex.
Proof.
  intros g s to_new edge_for_vertex de lowcost edge_parent inf vertex
         Hneq Hcand.
  unfold candidate_vertex_by in *.
  destruct Hcand as
    [Hv_graph [Hv_out [Hde_ne [Hde_range [Hlow_lt [Hmin Hweight]]]]]].
  split; [exact Hv_graph |].
  split; [exact Hv_out |].
  split; [exact Hde_ne |].
  split; [exact Hde_range |].
  split; [exact Hlow_lt |].
  split.
  - unfold min_object_of_subset in *.
    destruct Hmin as [Hmember Hmin_le].
    split.
    + unfold add_scanned_edge_for_vertex; left; exact Hmember.
    + intros e He.
      unfold add_scanned_edge_for_vertex in He.
      destruct He as [Hold | [Hv_eq [Hde_eq Hcut]]].
      * exact (Hmin_le e Hold).
      * exfalso. apply Hneq; exact Hv_eq.
  - exact Hweight.
Qed.

(** 若某个顶点在扫描边中未被更新（lowcost/edge_parent 的 Znth 不变），
    则其候选性不变。 *)
Lemma candidate_vertex_by_unchanged :
  forall (g : G) (s : St)
    (edge_for_vertex : V -> E -> Prop)
    (lowcost_in lowcost_out : list Z)
    (edge_parent_in edge_parent_out : list DE)
    (inf : Z) (vertex : V),
    Znth vertex lowcost_in 0 = Znth vertex lowcost_out 0 ->
    Znth vertex edge_parent_in 0 = Znth vertex edge_parent_out 0 ->
    candidate_vertex_by g s edge_for_vertex lowcost_out edge_parent_out inf vertex ->
    candidate_vertex_by g s edge_for_vertex lowcost_in edge_parent_in inf vertex.
Proof.
  intros g s edge_for_vertex lowcost_in edge_parent_in lowcost_out edge_parent_out inf vertex
         Hlow_eq Hparent_eq Hcand.
  unfold candidate_vertex_by in Hcand.
  unfold candidate_vertex_by.
  rewrite Hparent_eq.
  rewrite Hlow_eq.
  exact Hcand.
Qed.

(** 若扫描边不触发更新，则把它加入 edge_for_vertex 不改变候选。 *)
Lemma candidate_vertex_by_add_non_better :
  forall g s to_new wt_new edge_for_vertex de lowcost edge_parent inf vertex,
    candidate_vertex_by
      g s (add_scanned_edge_for_vertex g s to_new edge_for_vertex de)
      lowcost edge_parent inf vertex ->
    (~ is_cut_edge_to_vertex g s vertex (de / 2) \/
     Znth vertex lowcost 0 <= Znth de wt_new 0) ->
    weight g (de / 2) = Some (Znth de wt_new 0) ->
    lowcost_parent_match_by
      g (fun v => ~ vvalid s.(Prim.graph_in_state) v)
      edge_for_vertex lowcost edge_parent inf ->
    candidate_vertex_by g s edge_for_vertex lowcost edge_parent inf vertex.
Proof.
  intros g s to_new wt_new edge_for_vertex de lowcost edge_parent inf vertex
         Hcand Hno_better Hweight_de Hlow.
  unfold candidate_vertex_by in *.
  destruct Hcand as [Hv_graph [Hv_out Hparent_edge]].
  split; [exact Hv_graph |].
  split; [exact Hv_out |].
  simpl in *.
  destruct Hparent_edge as
    [Hde_ne [Hde_range [Hlow_lt [Hmin Hweight]]]].
  split; [exact Hde_ne |].
  split; [exact Hde_range |].
  split; [exact Hlow_lt |].
  split.
  - unfold add_scanned_edge_for_vertex in Hmin.
    unfold min_object_of_subset in *.
    destruct Hmin as [Hmember Hmin_le].
    split.
    + destruct Hmember as [Hold | [Hv_eq [Hde_eq Hcut]]].
      * exact Hold.
      * subst vertex.
        (* edge_parent[Znth de to_new 0] = de，且 de/2 在旧 edge_for_vertex 中 *)
        destruct Hno_better as [Hnot_cut | Hle].
        -- exfalso. apply Hnot_cut. rewrite <- Hde_eq. exact Hcut.
        -- unfold lowcost_parent_match_by in Hlow.
           destruct Hlow as [_ Hlow].
           specialize (Hlow (Znth de to_new 0) Hv_graph Hv_out).
           destruct Hlow as
             [[de_old [Hparent_old [Hde_old [Hrange_old [Hlow_old [Hmin_old Hweight_old]]]]]]
             | [Hnone [Hparent_old Hlow_eq]]].
           ++ (* de_old = edge_parent[v] = de，且 de_old/2 ∈ edge_for_vertex *)
              unfold min_object_of_subset in Hmin_old.
              destruct Hmin_old as [Hmember_old _].
              rewrite Hparent_old.
              exact Hmember_old.
           ++ exfalso.
              rewrite Hlow_eq in Hlow_lt.
              lia.
    + intros e Hold.
      exact (Hmin_le e (or_introl Hold)).
  - exact Hweight.
Qed.

(** 若扫描边不触发更新（要么不是 cut edge，要么权重不更优），
    则把它加入 edge_for_vertex 不改变候选（正向）。 *)
Lemma candidate_vertex_by_add_non_better_forw :
  forall g s to_new wt_new edge_for_vertex de lowcost edge_parent inf vertex,
    candidate_vertex_by g s edge_for_vertex lowcost edge_parent inf vertex ->
    (~ is_cut_edge_to_vertex g s vertex (de / 2) \/
     Znth vertex lowcost 0 <= Znth de wt_new 0) ->
    weight g (de / 2) = Some (Znth de wt_new 0) ->
    candidate_vertex_by
      g s (add_scanned_edge_for_vertex g s to_new edge_for_vertex de)
      lowcost edge_parent inf vertex.
Proof.
  intros g s to_new wt_new edge_for_vertex de lowcost edge_parent inf vertex
         Hcand Hno_better Hweight_de.
  unfold candidate_vertex_by in *.
  destruct Hcand as
    [Hv_graph [Hv_out [Hde_ne [Hde_range [Hlow_lt [Hmin Hweight]]]]]].
  split; [exact Hv_graph |].
  split; [exact Hv_out |].
  split; [exact Hde_ne |].
  split; [exact Hde_range |].
  split; [exact Hlow_lt |].
  split.
  - unfold min_object_of_subset in *.
    destruct Hmin as [Hmember Hmin_le].
    split.
    + unfold add_scanned_edge_for_vertex; left; exact Hmember.
    + intros e He.
      unfold add_scanned_edge_for_vertex in He.
      destruct He as [Hold | [Hv_eq [Hde_eq Hcut]]].
      * exact (Hmin_le e Hold).
      * subst vertex e.
        assert (Hle' : Znth (Znth de to_new 0) lowcost 0 <= Znth de wt_new 0).
        { destruct Hno_better as [Hnot_cut | Hle].
          - exfalso. apply Hnot_cut. exact Hcut.
          - exact Hle. }
        unfold E in *.
        rewrite Hweight.
        rewrite Hweight_de.
        simpl.
        exact Hle'.
  - exact Hweight.
Qed.

(** 若扫描边不触发更新，则把它加入 edge_for_vertex 不改变候选。 *)

(** 把列表某个位置的值改成更小的值后，任意位置的 [Znth] 都不会变大。 *)
Lemma Znth_replace_Znth_le :
  forall (l : list Z) i v,
    0 <= i < Zlength l ->
    v <= Znth i l 0 ->
    forall j, 0 <= j < Zlength l ->
      Znth j (replace_Znth i v l) 0 <= Znth j l 0.
Proof.
  intros l i v Hi Hv j Hj.
  destruct (Z.eq_dec j i) as [Heq | Hneq].
  - subst j.
    rewrite Znth_replace_Znth_same_local by exact Hi.
    exact Hv.
  - rewrite Znth_replace_Znth_diff_local;
      [lia | exact Hi | exact Hj | intro Hc; apply Hneq; symmetry; exact Hc].
Qed.

(** 单条有向边扫描后，[heap_entries_respect_lowcost] 保持。 *)
Lemma heap_entries_respect_lowcost_one_directed_edge :
  forall g s to_new wt_new lowcost_in edge_parent_in de
         heap_entries_in heap_entries_out
         lowcost_out edge_parent_out,
    0 <= Znth de to_new 0 < Zlength lowcost_in ->
    heap_entries_respect_lowcost lowcost_in heap_entries_in ->
    (forall cost vertex, In (cost, vertex) heap_entries_in ->
      0 <= vertex < Zlength lowcost_in) ->
    scan_one_directed_edge_update
      g s to_new wt_new lowcost_in edge_parent_in de lowcost_out edge_parent_out ->
    heap_update_one_directed_edge
      g s to_new wt_new lowcost_in de heap_entries_in heap_entries_out ->
    heap_entries_respect_lowcost lowcost_out heap_entries_out.
Proof.
  intros g s to_new wt_new lowcost_in edge_parent_in de
         heap_entries_in heap_entries_out
         lowcost_out edge_parent_out
         Hv_range Hrespect Hheap_range Hscan Hheap.
  set (v := Znth de to_new 0) in *.
  set (w := Znth de wt_new 0) in *.
  unfold heap_entries_respect_lowcost in *.
  intros cost vertex Hin_out.
  unfold heap_update_one_directed_edge in Hheap.
  destruct Hheap as [[Hcut [Hlt Hperm_out]] | [Hno Hheap_out]].
  - assert (Hin_cons : In (cost, vertex) ((w, v) :: heap_entries_in)).
    { eapply Permutation_in; [exact Hperm_out | exact Hin_out]. }
    simpl in Hin_cons.
    destruct Hin_cons as [Heq_entry | Hin_rest].
    + injection Heq_entry as Hcost_eq Hvertex_eq.
      subst cost vertex.
      unfold scan_one_directed_edge_update in Hscan.
      destruct Hscan as
        [[Hcut' [Hlt' [Hlow_out Hparent_out]]] |
         [Hno' [Hlow_out Hparent_out]]].
      * subst lowcost_out.
        unfold v, w.
        rewrite Znth_replace_Znth_same_local by exact Hv_range.
        lia.
      * subst lowcost_out.
        exfalso.
        destruct Hno' as [Hno_cut | Hle].
        -- apply Hno_cut; exact Hcut.
        -- lia.
    + destruct Hscan as
        [[Hcut' [Hlt' [Hlow_out Hparent_out]]] |
         [Hno' [Hlow_out Hparent_out]]].
      * subst lowcost_out.
        pose proof (Hrespect cost vertex Hin_rest) as Hresp.
        pose proof (Hheap_range cost vertex Hin_rest) as Hvertex_range.
        assert (Hw_le : w <= Znth v lowcost_in 0).
        { unfold v, w in Hlt. apply Z.lt_le_incl. exact Hlt. }
        pose proof (Znth_replace_Znth_le lowcost_in v w Hv_range Hw_le vertex Hvertex_range) as Hmono.
        unfold v, w in Hmono.
        apply (Z.le_trans _ _ _ Hmono Hresp).
      * subst lowcost_out.
        pose proof (Hrespect cost vertex Hin_rest) as Hresp.
        lia.
  - subst heap_entries_out.
    destruct Hscan as
      [[Hcut' [Hlt' [Hlow_out Hparent_out]]] |
       [Hno' [Hlow_out Hparent_out]]]; subst lowcost_out.
    + exfalso.
      destruct Hno as [Hno_cut | Hle].
      * apply Hno_cut; exact Hcut'.
      * lia.
    + pose proof (Hrespect cost vertex Hin_out) as Hresp.
      lia.
Qed.

(** 扫描一条有向边后，参数化 heap 匹配保持。 *)
Lemma heap_matches_by_one_directed_edge :
  forall g s to_new wt_new edge_for_vertex de
         lowcost_in edge_parent_in heap_entries_in
         lowcost_out edge_parent_out heap_entries_out inf,
    In (Znth de to_new 0) (graph_vertices g) ->
    0 <= de < 2 * graph_edge_count g ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength lowcost_in) ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength edge_parent_in) ->
    Znth de wt_new 0 < inf ->
    weight g (de / 2) = Some (Znth de wt_new 0) ->
    (forall cost vertex, In (cost, vertex) heap_entries_in ->
      0 <= vertex < Zlength lowcost_in) ->
    lowcost_parent_match_by
      g (fun v => ~ vvalid s.(Prim.graph_in_state) v)
      edge_for_vertex lowcost_in edge_parent_in inf ->
    heap_matches_prim_state_by
      g s edge_for_vertex lowcost_in edge_parent_in inf heap_entries_in ->
    scan_one_directed_edge_update
      g s to_new wt_new lowcost_in edge_parent_in de lowcost_out edge_parent_out ->
    heap_update_one_directed_edge
      g s to_new wt_new lowcost_in de heap_entries_in heap_entries_out ->
    heap_matches_prim_state_by
      g s (add_scanned_edge_for_vertex g s to_new edge_for_vertex de)
      lowcost_out edge_parent_out inf heap_entries_out.
Proof.
  intros g s to_new wt_new edge_for_vertex de
         lowcost_in edge_parent_in heap_entries_in
         lowcost_out edge_parent_out heap_entries_out inf
         Htarget_graph Hde_range Hlow_all Hparent_all Hwt_inf Hweight_de
         Hheap_range Hlow_in Hmatch Hscan Hheap.
  destruct Hmatch as [Hcontains [Hcurrent [Hrespect Hnodup_in]]].
  assert (Hv_range : 0 <= Znth de to_new 0 < Zlength lowcost_in)
    by (apply Hlow_all; exact Htarget_graph).
  assert (Hv_parent_range : 0 <= Znth de to_new 0 < Zlength edge_parent_in)
    by (apply Hparent_all; exact Htarget_graph).
  pose proof (scan_one_directed_edge_update_lowcost_parent_match_by
    g s to_new wt_new (fun v => ~ vvalid s.(Prim.graph_in_state) v)
    edge_for_vertex lowcost_in edge_parent_in de lowcost_out edge_parent_out inf
    Hlow_in Hscan Htarget_graph Hde_range Hlow_all Hparent_all
    Hwt_inf Hweight_de) as Hlow_after.
  unfold heap_matches_prim_state_by.
  split; [| split; [| split]].
  - intros vertex Hcand.
    set (v := Znth de to_new 0) in *.
    set (w := Znth de wt_new 0) in *.
    destruct (Z.eq_dec vertex v) as [Hveq | Hvneq].
    + subst vertex.
      unfold heap_update_one_directed_edge in Hheap.
      unfold scan_one_directed_edge_update in Hscan.
      destruct Hheap as [[Hcut [Hlt Hheap_out]] | [Hno Hheap_out]];
        destruct Hscan as
          [[Hcut' [Hlt' [Hlow_out Hparent_out]]] |
           [Hno' [Hlow_out Hparent_out]]].
      * (* Hheap 更新 + Hscan 更新：新 push *)
        subst lowcost_out.
        exists w.
        split; [eapply Permutation_in; [exact (Permutation_sym Hheap_out) | simpl; left; reflexivity] |].
        unfold v, w.
        rewrite Znth_replace_Znth_same_local by exact Hv_range.
        reflexivity.
      * (* Hheap 更新 + Hscan 不更新：矛盾 *)
        exfalso.
        destruct Hno' as [Hno_cut | Hle].
        -- apply Hno_cut; exact Hcut.
        -- lia.
      * (* Hheap 不更新 + Hscan 更新：矛盾 *)
        exfalso.
        destruct Hno as [Hno_cut | Hle].
        -- apply Hno_cut; exact Hcut'.
        -- lia.
      * (* Hheap 不更新 + Hscan 不更新：用旧候选 *)
        subst heap_entries_out lowcost_out edge_parent_out.
        destruct (Hcontains v) as [cost' [Hin' Hcost']].
        { apply (candidate_vertex_by_add_non_better g s to_new wt_new edge_for_vertex de lowcost_in edge_parent_in inf v).
          - exact Hcand.
          - exact Hno.
          - exact Hweight_de.
          - exact Hlow_in. }
        exists cost'.
        split; [exact Hin' | exact Hcost'].
    + assert (Hv_graph_vertex : In vertex (graph_vertices g)).
      { unfold candidate_vertex_by in Hcand. destruct Hcand as [Hvg _]. exact Hvg. }
      destruct (scan_one_directed_edge_update_other_vertex
        g s to_new wt_new lowcost_in edge_parent_in de
        lowcost_out edge_parent_out vertex
        Hscan Hv_range Hv_parent_range
        (Hlow_all vertex Hv_graph_vertex)
        (Hparent_all vertex Hv_graph_vertex)
        Hvneq)
        as [Hlow_v Hparent_v].
      assert (Hcand_old : candidate_vertex_by g s edge_for_vertex lowcost_out edge_parent_out inf vertex).
      { apply (candidate_vertex_by_add_other_vertex g s to_new edge_for_vertex de lowcost_out edge_parent_out inf vertex).
        - exact Hcand.
        - intro Hc. apply Hvneq. exact Hc. }
      destruct (Hcontains vertex) as [cost' [Hin' Hcost']].
      { apply (candidate_vertex_by_unchanged g s edge_for_vertex lowcost_in lowcost_out edge_parent_in edge_parent_out inf vertex).
        - symmetry. exact Hlow_v.
        - symmetry. exact Hparent_v.
        - exact Hcand_old. }
      unfold heap_update_one_directed_edge in Hheap.
      destruct Hheap as [[Hcut [Hlt Hperm_out]] | [Hno Hheap_out]].
      * exists cost'.
        split; [eapply Permutation_in; [exact (Permutation_sym Hperm_out) | simpl; right; exact Hin'] |].
        rewrite Hcost'. symmetry. exact Hlow_v.
      * subst heap_entries_out.
        destruct Hscan as
          [[Hcut' [Hlt' [Hlow_out Hparent_out]]] |
           [Hno' [Hlow_out Hparent_out]]].
        -- exfalso.
           destruct Hno as [Hno_cut | Hle].
           ++ apply Hno_cut; exact Hcut'.
           ++ lia.
        -- subst lowcost_out edge_parent_out.
           exists cost'. split; [exact Hin' | exact Hcost'].
  - intros cost vertex Hin Hcost.
    set (v := Znth de to_new 0) in *.
    set (w := Znth de wt_new 0) in *.
    unfold heap_update_one_directed_edge in Hheap.
    destruct Hheap as [[Hcut [Hlt Hperm_out]] | [Hno Hheap_out]].
    + assert (Hin_cons : In (cost, vertex) ((w, v) :: heap_entries_in)).
      { eapply Permutation_in; [exact Hperm_out | exact Hin]. }
      simpl in Hin_cons.
      destruct Hin_cons as [Heq_entry | Hin_rest].
      * injection Heq_entry as Hcost_eq Hvertex_eq.
        subst cost vertex.
        eapply candidate_vertex_by_of_lowcost.
        -- exact Htarget_graph.
        -- unfold is_cut_edge_to_vertex in Hcut.
           destruct Hcut as [Hv_not_valid _].
           exact Hv_not_valid.
        -- unfold scan_one_directed_edge_update in Hscan.
           destruct Hscan as
             [[Hcut' [Hlt' [Hlow_out Hparent_out]]] |
              [Hno' [Hlow_out Hparent_out]]].
           ++ subst lowcost_out.
              unfold v, w.
              rewrite Znth_replace_Znth_same_local by exact Hv_range.
              exact Hwt_inf.
           ++ subst lowcost_out.
              exfalso.
              destruct Hno' as [Hno_cut | Hle].
              ** apply Hno_cut; exact Hcut.
              ** lia.
        -- exact Hlow_after.
      * destruct (Z.eq_dec vertex v) as [Hveq | Hvneq].
        { subst vertex.
          destruct Hscan as
            [[Hcut' [Hlt' [Hlow_out Hparent_out]]] |
             [Hno' [Hlow_out Hparent_out]]].
          { rewrite Hlow_out in Hcost.
            assert (Hcost_w : cost = w).
            { rewrite Hcost.
              rewrite Znth_replace_Znth_same_local by exact Hv_range.
              reflexivity. }
            pose proof (Hrespect cost v Hin_rest) as Hresp.
            unfold v, w in *.
            rewrite Hcost_w in Hresp.
            exfalso.
            pose proof (Z.lt_le_trans _ _ _ Hlt Hresp) as Hbad.
            apply (Z.lt_irrefl (Znth de wt_new 0)); exact Hbad. }
          { exfalso.
            destruct Hno' as [Hno_cut | Hle].
            - apply Hno_cut; exact Hcut.
            - lia. } }
        { pose proof Hscan as Hscan0.
          destruct Hscan as
            [[Hcut' [Hlt' [Hlow_out Hparent_out]]] |
             [Hno' [Hlow_out Hparent_out]]].
          { assert (Hlow_v : Znth vertex lowcost_out 0 = Znth vertex lowcost_in 0).
            { rewrite Hlow_out.
              apply Znth_replace_Znth_diff_local;
                [exact Hv_range | exact (Hheap_range cost vertex Hin_rest) |
                 intro Hc; apply Hvneq; symmetry; exact Hc]. }
            assert (Hcost_in : cost = Znth vertex lowcost_in 0).
            { rewrite Hcost. exact Hlow_v. }
            pose proof (Hcurrent cost vertex Hin_rest Hcost_in) as Hcand_old.
            pose proof Hcand_old as Hcand_old_for_graph.
            unfold candidate_vertex_by in Hcand_old_for_graph.
            destruct Hcand_old_for_graph as [Hv_graph _].
            destruct (scan_one_directed_edge_update_other_vertex
              g s to_new wt_new lowcost_in edge_parent_in de
              lowcost_out edge_parent_out vertex
              Hscan0 Hv_range Hv_parent_range
              (Hlow_all vertex Hv_graph) (Hparent_all vertex Hv_graph)
              Hvneq) as [Hlow_v2 Hparent_v].
            apply (candidate_vertex_by_unchanged g s
              (add_scanned_edge_for_vertex g s to_new edge_for_vertex de)
              lowcost_out lowcost_in edge_parent_out edge_parent_in inf vertex).
            - exact Hlow_v2.
            - exact Hparent_v.
            - apply (candidate_vertex_by_add_other_vertex_forw
                g s to_new edge_for_vertex de lowcost_in edge_parent_in inf vertex).
              + exact Hvneq.
              + exact Hcand_old. }
          { subst lowcost_out edge_parent_out.
            pose proof (Hcurrent cost vertex Hin_rest Hcost) as Hcand_old.
            apply (candidate_vertex_by_add_other_vertex_forw
              g s to_new edge_for_vertex de lowcost_in edge_parent_in inf vertex).
            - exact Hvneq.
            - exact Hcand_old. } }
    + subst heap_entries_out.
      destruct Hscan as
        [[Hcut' [Hlt' [Hlow_out Hparent_out]]] |
         [Hno' [Hlow_out Hparent_out]]].
      { exfalso.
        destruct Hno as [Hno_cut | Hle].
        - apply Hno_cut; exact Hcut'.
        - lia. }
      { subst lowcost_out edge_parent_out.
        destruct (Z.eq_dec vertex v) as [Hveq | Hvneq].
        { subst vertex.
          pose proof (Hcurrent cost v Hin Hcost) as Hcand_old.
          apply (candidate_vertex_by_add_non_better_forw
            g s to_new wt_new edge_for_vertex de lowcost_in edge_parent_in inf v).
          - exact Hcand_old.
          - exact Hno.
          - exact Hweight_de. }
        { pose proof (Hcurrent cost vertex Hin Hcost) as Hcand_old.
          apply (candidate_vertex_by_add_other_vertex_forw
            g s to_new edge_for_vertex de lowcost_in edge_parent_in inf vertex).
          - exact Hvneq.
          - exact Hcand_old. } }
  - exact (heap_entries_respect_lowcost_one_directed_edge
      g s to_new wt_new lowcost_in edge_parent_in de
      heap_entries_in heap_entries_out lowcost_out edge_parent_out
      Hv_range Hrespect Hheap_range Hscan Hheap).
  - destruct Hheap as [[Hcut [Hlt Hperm_out]] | [Hno Hheap_out]].
    + apply Permutation_NoDup with (l := (Znth de wt_new 0, Znth de to_new 0) :: heap_entries_in).
      * symmetry. exact Hperm_out.
      * apply NoDup_cons.
        -- intro Hin.
           pose proof (Hrespect (Znth de wt_new 0) (Znth de to_new 0) Hin) as Hresp.
           pose proof (Z.lt_le_trans _ _ _ Hlt Hresp) as Hbad.
           apply (Z.lt_irrefl (Znth de wt_new 0)); exact Hbad.
        -- exact Hnodup_in.
    + subst heap_entries_out. exact Hnodup_in.
Qed.

(** 单条有向边扫描后，堆里 entry 的顶点范围保持。 *)
Lemma heap_update_one_directed_edge_vertex_range :
  forall g s_next to_new wt_new lowcost_in de heap_entries_in heap_entries_out,
    0 <= Znth de to_new 0 < Zlength lowcost_in ->
    (forall cost vertex, In (cost, vertex) heap_entries_in ->
      0 <= vertex < Zlength lowcost_in) ->
    heap_update_one_directed_edge
      g s_next to_new wt_new lowcost_in de heap_entries_in heap_entries_out ->
    forall cost vertex, In (cost, vertex) heap_entries_out ->
      0 <= vertex < Zlength lowcost_in.
Proof.
  intros g s_next to_new wt_new lowcost_in de heap_entries_in heap_entries_out
         Hv_range Hheap_range Hheap cost vertex Hin.
  unfold heap_update_one_directed_edge in Hheap.
  destruct Hheap as [[Hcut [Hlt Hperm_out]] | [Hno Hout]].
  - assert (Hin_cons : In (cost, vertex) ((Znth de wt_new 0, Znth de to_new 0) :: heap_entries_in)).
    { eapply Permutation_in; [exact Hperm_out | exact Hin]. }
    simpl in Hin_cons.
    destruct Hin_cons as [Heq | Hin_rest].
    + injection Heq as Hcost_eq Hvertex_eq.
      subst cost vertex.
      exact Hv_range.
    + apply (Hheap_range cost vertex Hin_rest).
  - subst heap_entries_out.
    apply (Hheap_range cost vertex Hin).
Qed.

(** 扫描只会往堆里加条目，不会删除：扫描前堆的条目都在扫描后堆里。 *)
Lemma scan_directed_edges_full_update_heap_entries_subset :
  forall g s_next to_new wt_new edges
         low0 edge0 hp0 low2 edge2 hp2,
    scan_directed_edges_full_update
      g s_next to_new wt_new edges low0 edge0 hp0 low2 edge2 hp2 ->
    forall e, In e hp0 -> In e hp2.
Proof.
  intros g s_next to_new wt_new edges
         low0 edge0 hp0 low2 edge2 hp2 Hscan.
  induction Hscan as
    [low edge hp |
     de rest low0 edge0 hp0 low1 edge1 hp1 low2 edge2 hp2
       Hone Hheap_one Hrest IH]; intros.
  - exact H.
  - simpl in Hheap_one.
    unfold heap_update_one_directed_edge in Hheap_one.
    destruct Hheap_one as [[Hcut [Hlt Hperm]] | [Hno Hout]].
    + apply IH.
      eapply Permutation_in; [symmetry; exact Hperm | simpl; right; exact H].
    + subst hp1. apply IH. exact H.
Qed.

(** 扫描邻接边时，堆只会在严格改进 lowcost 的情况下加入新 entry；
    因此若扫描前堆条目无重复，则扫描后仍无重复。 *)
Lemma scan_directed_edges_full_update_heap_entries_nodup :
  forall g s_next to_new wt_new edges
         low0 edge0 hp0 low2 edge2 hp2,
    (forall de, In de edges ->
      0 <= Znth de to_new 0 < Zlength low0) ->
    (forall cost vertex, In (cost, vertex) hp0 ->
      0 <= vertex < Zlength low0) ->
    heap_entries_respect_lowcost low0 hp0 ->
    NoDup hp0 ->
    scan_directed_edges_full_update
      g s_next to_new wt_new edges low0 edge0 hp0 low2 edge2 hp2 ->
    NoDup hp2.
Proof.
  intros g s_next to_new wt_new edges
         low0 edge0 hp0 low2 edge2 hp2
         Htarget Hheap_range Hrespect Hnodup Hscan.
  revert Htarget Hheap_range Hrespect Hnodup.
  induction Hscan as
    [low edge hp |
     de rest low0' edge0' hp0' low1 edge1 hp1 low2' edge2' hp2'
       Hone Hheap_one Hrest IH].
  - intros. exact Hnodup.
  - intros Htarget Hheap_range Hrespect Hnodup.
    assert (Hv_range : 0 <= Znth de to_new 0 < Zlength low0')
      by (apply Htarget; simpl; left; reflexivity).
    assert (Hnodup1 : NoDup hp1).
    {
      unfold heap_update_one_directed_edge in Hheap_one.
      destruct Hheap_one as [[_ [Hlt Hperm_out]] | [_ Heq]].
      - apply Permutation_NoDup with
          (l := (Znth de wt_new 0, Znth de to_new 0) :: hp0').
        + symmetry. exact Hperm_out.
        + apply NoDup_cons.
          * intro Hin.
            pose proof (Hrespect (Znth de wt_new 0) (Znth de to_new 0) Hin) as Hresp.
            pose proof (Z.lt_le_trans _ _ _ Hlt Hresp) as Hbad.
            apply (Z.lt_irrefl (Znth de wt_new 0)); exact Hbad.
          * exact Hnodup.
      - subst hp1. exact Hnodup.
    }
    destruct (scan_one_directed_edge_update_lengths
      g s_next to_new wt_new low0' edge0' de low1 edge1 Hone)
      as [Hlen_low _].
    assert (Hrespect1 :
      heap_entries_respect_lowcost low1 hp1).
    {
      eapply heap_entries_respect_lowcost_one_directed_edge; eauto.
    }
    assert (Hheap_range1 :
      forall cost vertex, In (cost, vertex) hp1 ->
        0 <= vertex < Zlength low1).
    {
      intros cost vertex Hin.
      rewrite Hlen_low.
      eapply heap_update_one_directed_edge_vertex_range; eauto.
    }
    apply IH.
    + intros de' Hde'.
      rewrite Hlen_low.
      apply Htarget.
      simpl. right. exact Hde'.
    + exact Hheap_range1.
    + exact Hrespect1.
    + exact Hnodup1.
Qed.

(** 扫描一串有向边后，参数化 heap 匹配保持（归纳）。 *)
Lemma scan_directed_edges_full_update_heap_matches_by :
  forall g s_next to_new wt_new scanned_edges
         edge_for_vertex lowcost_in edge_parent_in heap_entries_in
         lowcost_out edge_parent_out heap_entries_out inf,
    lowcost_parent_match_by
      g (fun v => ~ vvalid s_next.(Prim.graph_in_state) v)
      edge_for_vertex lowcost_in edge_parent_in inf ->
    heap_matches_prim_state_by
      g s_next edge_for_vertex lowcost_in edge_parent_in inf heap_entries_in ->
    (forall cost vertex, In (cost, vertex) heap_entries_in ->
      0 <= vertex < Zlength lowcost_in) ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength lowcost_in) ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength edge_parent_in) ->
    (forall de, In de scanned_edges ->
      In (Znth de to_new 0) (graph_vertices g)) ->
    (forall de, In de scanned_edges ->
      0 <= de < 2 * graph_edge_count g) ->
    (forall de, In de scanned_edges -> Znth de wt_new 0 < inf) ->
    (forall de, In de scanned_edges ->
      weight g (de / 2) = Some (Znth de wt_new 0)) ->
    scan_directed_edges_full_update
      g s_next to_new wt_new scanned_edges
      lowcost_in edge_parent_in heap_entries_in
      lowcost_out edge_parent_out heap_entries_out ->
    heap_matches_prim_state_by
      g s_next
      (add_scanned_edges_for_vertex g s_next to_new edge_for_vertex scanned_edges)
      lowcost_out edge_parent_out inf heap_entries_out.
Proof.
  intros g s_next to_new wt_new scanned_edges
         edge_for_vertex lowcost_in edge_parent_in heap_entries_in
         lowcost_out edge_parent_out heap_entries_out inf
         Hmatch Hheapmatch Hheap_range Hlow_range Hparent_range
         Htarget Hde_range Hwt_inf Hweight Hscan.
  revert edge_for_vertex Hmatch Hheapmatch Hheap_range Hlow_range Hparent_range.
  induction Hscan as
    [lowcost edge_parent heap_entries |
     de rest lowcost0 edge_parent0 heap_entries0
       lowcost1 edge_parent1 heap_entries1
       lowcost2 edge_parent2 heap_entries2
       Hone Hheap_one Hrest IH].
  - intros edge_for_vertex Hmatch Hheapmatch Hheap_range Hlow_range Hparent_range.
    exact Hheapmatch.
  - intros edge_for_vertex Hmatch Hheapmatch Hheap_range Hlow_range Hparent_range.
    assert (Htarget_de : In (Znth de to_new 0) (graph_vertices g)).
    { apply Htarget; simpl; left; reflexivity. }
    assert (Hde_range_de : 0 <= de < 2 * graph_edge_count g).
    { apply Hde_range; simpl; left; reflexivity. }
    assert (Hwt_inf_de : Znth de wt_new 0 < inf).
    { apply Hwt_inf; simpl; left; reflexivity. }
    assert (Hweight_de : weight g (de / 2) = Some (Znth de wt_new 0)).
    { apply Hweight; simpl; left; reflexivity. }
    assert (Hmatch1 :
      lowcost_parent_match_by
        g (fun v => ~ vvalid s_next.(Prim.graph_in_state) v)
        (add_scanned_edge_for_vertex g s_next to_new edge_for_vertex de)
        lowcost1 edge_parent1 inf).
    { exact (scan_one_directed_edge_update_lowcost_parent_match_by
        g s_next to_new wt_new
        (fun v => ~ vvalid s_next.(Prim.graph_in_state) v)
        edge_for_vertex lowcost0 edge_parent0 de lowcost1 edge_parent1 inf
        Hmatch Hone Htarget_de Hde_range_de Hlow_range Hparent_range
        Hwt_inf_de Hweight_de). }
    assert (Hv_range : 0 <= Znth de to_new 0 < Zlength lowcost0).
    { apply Hlow_range; exact Htarget_de. }
    assert (Hv_parent_range : 0 <= Znth de to_new 0 < Zlength edge_parent0).
    { apply Hparent_range; exact Htarget_de. }
    assert (Hheapmatch1 :
      heap_matches_prim_state_by
        g s_next
        (add_scanned_edge_for_vertex g s_next to_new edge_for_vertex de)
        lowcost1 edge_parent1 inf heap_entries1).
    { exact (heap_matches_by_one_directed_edge
        g s_next to_new wt_new edge_for_vertex de
        lowcost0 edge_parent0 heap_entries0
        lowcost1 edge_parent1 heap_entries1 inf
        Htarget_de Hde_range_de Hlow_range Hparent_range
        Hwt_inf_de Hweight_de Hheap_range Hmatch Hheapmatch Hone Hheap_one). }
    destruct (scan_one_directed_edge_update_lengths
      g s_next to_new wt_new lowcost0 edge_parent0 de lowcost1 edge_parent1 Hone)
      as [Hlen_low Hlen_parent].
    assert (Hheap_range1 :
      forall cost vertex, In (cost, vertex) heap_entries1 ->
        0 <= vertex < Zlength lowcost1).
    { intros cost vertex Hin.
      pose proof (heap_update_one_directed_edge_vertex_range
        g s_next to_new wt_new lowcost0 de heap_entries0 heap_entries1
        Hv_range Hheap_range Hheap_one cost vertex Hin) as Hr.
      rewrite Hlen_low. exact Hr. }
    assert (Hlow_range1 :
      forall v, In v (graph_vertices g) -> 0 <= v < Zlength lowcost1).
    { intros v Hv_graph.
      rewrite Hlen_low. apply Hlow_range; exact Hv_graph. }
    assert (Hparent_range1 :
      forall v, In v (graph_vertices g) -> 0 <= v < Zlength edge_parent1).
    { intros v Hv_graph.
      rewrite Hlen_parent. apply Hparent_range; exact Hv_graph. }
    exact (IH
      (fun de' Hde' => Htarget de' (or_intror Hde'))
      (fun de' Hde' => Hde_range de' (or_intror Hde'))
      (fun de' Hde' => Hwt_inf de' (or_intror Hde'))
      (fun de' Hde' => Hweight de' (or_intror Hde'))
      (add_scanned_edge_for_vertex g s_next to_new edge_for_vertex de)
      Hmatch1 Hheapmatch1 Hheap_range1 Hlow_range1 Hparent_range1).
Qed.

(** 扫描 [minIndex] 邻接链到 -1 后，前缀更新退化为完整更新。 *)
Lemma scan_minIndex_adjacency_heap_prefix_update_terminates :
  forall g s_next from_new first link to_new wt_new minIndex
         lowcost_before edge_parent_before heap_entries_before
         lowcost_current edge_parent_current heap_entries_current,
    scan_minIndex_adjacency_heap_prefix_update
      g s_next from_new first link to_new wt_new minIndex (-1)
      lowcost_before edge_parent_before heap_entries_before
      lowcost_current edge_parent_current heap_entries_current ->
    scan_minIndex_adjacency_heap_update
      g s_next from_new first link to_new wt_new minIndex
      lowcost_before edge_parent_before heap_entries_before
      lowcost_current edge_parent_current heap_entries_current.
Proof.
  intros g s_next from_new first link to_new wt_new minIndex
         lowcost_before edge_parent_before heap_entries_before
         lowcost_current edge_parent_current heap_entries_current Hpre.
  unfold scan_minIndex_adjacency_heap_prefix_update in Hpre.
  unfold scan_minIndex_adjacency_heap_update.
  destruct Hpre as
    [scanned_edges [remaining_edges [Hchain [Hlink [Hperm Hscan]]]]].
  inversion Hlink; subst remaining_edges.
  - exists scanned_edges.
    rewrite app_nil_r in Hchain.
    rewrite app_nil_r in Hperm.
    split; [exact Hchain |].
    split; [exact Hperm | exact Hscan].
  - exfalso. apply H; reflexivity.
Qed.

(** 在已扫描列表末尾追加一条边：先扫描 [l]，再扫描 [de]。 *)
Lemma scan_directed_edges_full_update_snoc :
  forall g s_next to_new wt_new l
         lowcost0 edge_parent0 heap_entries0
         lowcost1 edge_parent1 heap_entries1
         de lowcost2 edge_parent2 heap_entries2,
    scan_directed_edges_full_update
      g s_next to_new wt_new l
      lowcost0 edge_parent0 heap_entries0
      lowcost1 edge_parent1 heap_entries1 ->
    scan_one_directed_edge_update
      g s_next to_new wt_new lowcost1 edge_parent1 de lowcost2 edge_parent2 ->
    heap_update_one_directed_edge
      g s_next to_new wt_new lowcost1 de heap_entries1 heap_entries2 ->
    scan_directed_edges_full_update
      g s_next to_new wt_new (l ++ de :: nil)
      lowcost0 edge_parent0 heap_entries0
      lowcost2 edge_parent2 heap_entries2.
Proof.
  intros g s_next to_new wt_new l
         lowcost0 edge_parent0 heap_entries0
         lowcost1 edge_parent1 heap_entries1
         de lowcost2 edge_parent2 heap_entries2
         Hscan Hone Hheap.
  revert de lowcost2 edge_parent2 heap_entries2 Hone Hheap.
  induction Hscan as [lowcost edge_parent heap_entries |
    de' rest lowcost0' edge_parent0' heap_entries0'
      lowcost1' edge_parent1' heap_entries1'
      lowcost2' edge_parent2' heap_entries2'
      Hone' Hheap' IHIH].
  all: intros de lowcost2 edge_parent2 heap_entries2 Hone Hheap.
  - eapply scan_directed_edges_full_update_cons.
    + exact Hone.
    + exact Hheap.
    + apply scan_directed_edges_full_update_nil.
  - eapply scan_directed_edges_full_update_cons.
    + exact Hone'.
    + exact Hheap'.
    + apply (IHIHIH de lowcost2 edge_parent2 heap_entries2 Hone Hheap).
Qed.

(** 扫描前缀从 [cur_edge] 推进到 [link[cur_edge]]：当前边被处理后，
    lowcost/edge_parent/堆 的前缀更新同时前进。 *)
Lemma scan_minIndex_adjacency_heap_prefix_update_step :
  forall g s_next from_new first link to_new wt_new minIndex cur_edge
         lowcost_before edge_parent_before heap_entries_before
         lowcost_cur edge_parent_cur heap_entries_cur
         lowcost_next edge_parent_next heap_entries_next,
    0 <= cur_edge ->
    scan_minIndex_adjacency_heap_prefix_update
      g s_next from_new first link to_new wt_new minIndex cur_edge
      lowcost_before edge_parent_before heap_entries_before
      lowcost_cur edge_parent_cur heap_entries_cur ->
    scan_one_directed_edge_update
      g s_next to_new wt_new lowcost_cur edge_parent_cur cur_edge
      lowcost_next edge_parent_next ->
    heap_update_one_directed_edge
      g s_next to_new wt_new lowcost_cur cur_edge
      heap_entries_cur heap_entries_next ->
    scan_minIndex_adjacency_heap_prefix_update
      g s_next from_new first link to_new wt_new minIndex
      (Znth cur_edge link 0)
      lowcost_before edge_parent_before heap_entries_before
      lowcost_next edge_parent_next heap_entries_next.
Proof.
  intros g s_next from_new first link to_new wt_new minIndex cur_edge
         lowcost_before edge_parent_before heap_entries_before
         lowcost_cur edge_parent_cur heap_entries_cur
         lowcost_next edge_parent_next heap_entries_next
         Hcur_nonneg Hpre Hone Hheap.
  unfold scan_minIndex_adjacency_heap_prefix_update in *.
  destruct Hpre as
    [scanned [remaining [Hchain [Hlink [Hperm Hscan]]]]].
  inversion Hlink as [Hneg | cur' l' Hcur_ne Hnext Heq]; subst remaining.
  - exfalso. subst cur_edge. lia.
  - exists (scanned ++ cur_edge :: nil), l'.
    split.
    + rewrite <- app_assoc.
      simpl.
      exact Hchain.
    + split.
      * exact Hnext.
      * split.
        -- rewrite <- app_assoc.
           simpl.
           exact Hperm.
        -- eapply scan_directed_edges_full_update_snoc; eauto.
Qed.

(** 扫描完成后，把参数化 heap 匹配里的候选边集合换回
    [is_cut_edge_to_vertex]。 *)
Lemma candidate_vertex_by_iff :
  forall g s edge_for1 edge_for2 lowcost edge_parent inf v,
    (forall e, ~ vvalid s.(Prim.graph_in_state) v ->
       edge_for1 v e <-> edge_for2 v e) ->
    candidate_vertex_by g s edge_for1 lowcost edge_parent inf v <->
    candidate_vertex_by g s edge_for2 lowcost edge_parent inf v.
Proof.
  intros g s edge_for1 edge_for2 lowcost edge_parent inf v Hedge.
  unfold candidate_vertex_by.
  split.
  - intros H.
    destruct H as
      [Hv_graph [Hv_out [Hde_ne [Hde_range [Hlow_lt [Hmin Hweight]]]]]].
    split; [exact Hv_graph |].
    split; [exact Hv_out |].
    split; [exact Hde_ne |].
    split; [exact Hde_range |].
    split; [exact Hlow_lt |].
    split.
    + unfold min_object_of_subset in *.
      destruct Hmin as [Hmember1 Hmin_le1].
      split; [apply (proj1 (Hedge _ Hv_out)); exact Hmember1 |].
      intros b Hb2. apply Hmin_le1. apply (proj2 (Hedge b Hv_out)); exact Hb2.
    + exact Hweight.
  - intros H.
    destruct H as
      [Hv_graph [Hv_out [Hde_ne [Hde_range [Hlow_lt [Hmin Hweight]]]]]].
    split; [exact Hv_graph |].
    split; [exact Hv_out |].
    split; [exact Hde_ne |].
    split; [exact Hde_range |].
    split; [exact Hlow_lt |].
    split.
    + unfold min_object_of_subset in *.
      destruct Hmin as [Hmember2 Hmin_le2].
      split; [apply (proj2 (Hedge _ Hv_out)); exact Hmember2 |].
      intros b Hb1. apply Hmin_le2. apply (proj1 (Hedge b Hv_out)); exact Hb1.
    + exact Hweight.
Qed.

Lemma heap_matches_prim_state_by_iff :
  forall g s edge_for1 edge_for2 lowcost edge_parent inf entries,
    (forall v e, ~ vvalid s.(Prim.graph_in_state) v ->
       edge_for1 v e <-> edge_for2 v e) ->
    heap_matches_prim_state_by g s edge_for1 lowcost edge_parent inf entries ->
    heap_matches_prim_state_by g s edge_for2 lowcost edge_parent inf entries.
Proof.
  intros g s edge_for1 edge_for2 lowcost edge_parent inf entries
         Hedge Hmatch.
  unfold heap_matches_prim_state_by, heap_contains_all_candidates_by,
    heap_current_entries_are_candidates_by in *.
  destruct Hmatch as [Hcontains [Hcurrent [Hrespect Hnodup]]].
  split; [| split; [| split]].
  - intros vertex Hcand.
    apply Hcontains.
    apply (proj2 (candidate_vertex_by_iff
      g s edge_for1 edge_for2 lowcost edge_parent inf vertex (Hedge vertex))).
    exact Hcand.
  - intros cost vertex Hin Hcost.
    apply (proj1 (candidate_vertex_by_iff
      g s edge_for1 edge_for2 lowcost edge_parent inf vertex (Hedge vertex))).
    apply (Hcurrent cost vertex); [exact Hin | exact Hcost].
  - exact Hrespect.
  - exact Hnodup.
Qed.

Lemma add_vertex_directed_edges_for_vertex_is_cut :
  forall g s_next from_new to_new minIndex v e,
    add_vertex_directed_edges_for_vertex g s_next from_new to_new minIndex
      (fun v e => is_cut_edge_to_vertex g s_next v e) v e <->
    is_cut_edge_to_vertex g s_next v e.
Proof.
  intros g s_next from_new to_new minIndex v e.
  unfold add_vertex_directed_edges_for_vertex.
  split.
  - intros [Hcut | [de [Hin [Hv [He Hcut]]]]].
    + exact Hcut.
    + subst v e. exact Hcut.
  - intros Hcut. left. exact Hcut.
Qed.

(** 反方向：把参数化版本实例化回非参数化的 heap 匹配。 *)
Lemma heap_matches_prim_state_by_to :
  forall g s lowcost edge_parent inf entries,
    heap_matches_prim_state_by
      g s (fun v e => is_cut_edge_to_vertex g s v e)
      lowcost edge_parent inf entries ->
    heap_matches_prim_state g s lowcost edge_parent inf entries.
Proof.
  intros g s lowcost edge_parent inf entries Hmatch.
  unfold heap_matches_prim_state, heap_matches_prim_state_by in *.
  unfold heap_contains_all_candidates, heap_contains_all_candidates_by in *.
  unfold heap_current_entries_are_candidates,
    heap_current_entries_are_candidates_by in *.
  destruct Hmatch as [Hcontains [Hcurrent [Hrespect Hnodup]]].
  split; [| split; [| split]].
  - intros vertex Hcand.
    apply Hcontains.
    unfold candidate_vertex, candidate_vertex_by, vertex_has_parent_edge in *.
    unfold is_min_cut_edge_to_vertex in *.
    tauto.
  - intros cost vertex Hin Hcost.
    apply (Hcurrent cost vertex); [exact Hin | exact Hcost].
  - exact Hrespect.
  - exact Hnodup.
Qed.

(** 扫描完 [minIndex] 的全部邻接边后，堆匹配完整 Prim 状态。 *)
Lemma scan_minIndex_adjacency_heap_update_heap_matches :
  forall n m from to wt g s_before s_next
         from_new first link to_new wt_new minIndex
         lowcost_before edge_parent_before heap_entries_before
         lowcost_after edge_parent_after heap_entries_after inf,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    (forall e, 0 <= e < m -> Znth e wt 0 < inf) ->
    directed_array_graph g from_new to_new wt_new ->
    selected_parent_add_to_mst g s_before s_next from_new to_new
      edge_parent_before minIndex ->
    lowcost_parent_match_by
      g (fun v => ~ vvalid s_next.(Prim.graph_in_state) v)
      (fun v e => is_cut_edge_to_vertex g s_before v e)
      lowcost_before edge_parent_before inf ->
    heap_matches_prim_state_by g s_next
      (fun v e => is_cut_edge_to_vertex g s_before v e)
      lowcost_before edge_parent_before inf heap_entries_before ->
    (forall cost vertex, In (cost, vertex) heap_entries_before ->
      0 <= vertex < Zlength lowcost_before) ->
    scan_minIndex_adjacency_heap_update
      g s_next from_new first link to_new wt_new minIndex
      lowcost_before edge_parent_before heap_entries_before
      lowcost_after edge_parent_after heap_entries_after ->
    heap_matches_prim_state g s_next lowcost_after edge_parent_after inf heap_entries_after.
Proof.
  intros n m from to wt g s_before s_next
         from_new first link to_new wt_new minIndex
         lowcost_before edge_parent_before heap_entries_before
         lowcost_after edge_parent_after heap_entries_after inf
         Hgraph Hfrom_range Hto_range Hwt_range Hdir Hadd
         Hmatch_by Hheapmatch_by Hheap_range Hscan.
  destruct Hscan as [scanned_edges [Hchain [Hperm Hfull]]].
  pose proof Hmatch_by as Hmatch_by_full.
  unfold lowcost_parent_match_by in Hmatch_by_full.
  destruct Hmatch_by_full as [Hrange _].
  assert (Hlow_range :
    forall v, In v (graph_vertices g) -> 0 <= v < Zlength lowcost_before).
  { intros v Hv_graph. apply (Hrange v Hv_graph). }
  assert (Hparent_range :
    forall v, In v (graph_vertices g) -> 0 <= v < Zlength edge_parent_before).
  { intros v Hv_graph. apply (Hrange v Hv_graph). }
  assert (Hheap_by :
    heap_matches_prim_state_by g s_next
      (add_scanned_edges_for_vertex g s_next to_new
        (fun v e => is_cut_edge_to_vertex g s_before v e) scanned_edges)
      lowcost_after edge_parent_after inf heap_entries_after).
  { eapply scan_directed_edges_full_update_heap_matches_by.
    - exact Hmatch_by.
    - exact Hheapmatch_by.
    - exact Hheap_range.
    - exact Hlow_range.
    - exact Hparent_range.
    - intros de Hde.
      eapply vertex_directed_edges_to_graph_vertex; eauto.
      eapply Permutation_in; [exact Hperm | exact Hde].
    - intros de Hde.
      eapply vertex_directed_edges_range.
      eapply Permutation_in; [exact Hperm | exact Hde].
    - intros de Hde.
      eapply vertex_directed_edges_weight_lt; eauto.
      eapply Permutation_in; [exact Hperm | exact Hde].
    - intros de Hde.
      eapply directed_array_graph_weight; eauto.
      eapply vertex_directed_edges_range.
      eapply Permutation_in; [exact Hperm | exact Hde].
    - exact Hfull. }
  assert (Hheap_by_vertex :
    heap_matches_prim_state_by g s_next
      (add_vertex_directed_edges_for_vertex g s_next from_new to_new minIndex
        (fun v e => is_cut_edge_to_vertex g s_before v e))
      lowcost_after edge_parent_after inf heap_entries_after).
  { apply (heap_matches_prim_state_by_iff g s_next
      (add_scanned_edges_for_vertex g s_next to_new
        (fun v e => is_cut_edge_to_vertex g s_before v e) scanned_edges)
      (add_vertex_directed_edges_for_vertex g s_next from_new to_new minIndex
        (fun v e => is_cut_edge_to_vertex g s_before v e))
      lowcost_after edge_parent_after inf heap_entries_after).
    - intros v e _. apply add_scanned_edges_for_vertex_perm. exact Hperm.
    - exact Hheap_by. }
  apply heap_matches_prim_state_by_to.
  apply (heap_matches_prim_state_by_iff g s_next
    (add_vertex_directed_edges_for_vertex g s_next from_new to_new minIndex
      (fun v e => is_cut_edge_to_vertex g s_before v e))
    (fun v e => is_cut_edge_to_vertex g s_next v e)
    lowcost_after edge_parent_after inf heap_entries_after).
  - intros v e Hnvout.
    apply (selected_parent_add_to_mst_cut_edges_match
      n m from to wt g s_before s_next
      from_new to_new wt_new edge_parent_before minIndex
      Hgraph Hdir Hadd v e Hnvout).
  - exact Hheap_by_vertex.
Qed.

(** 初始状态（[chosen = 1]，首次扫描 [src] 的邻边）下，扫描完成后堆匹配
    [s_after]（即 [initSt g src]）。base 用空边集合 + 空堆。 *)
Lemma scan_minIndex_adjacency_heap_update_heap_matches_init :
  forall n m from to wt g src s_after
         from_new first link to_new wt_new minIndex
         lowcost_before edge_parent_before heap_entries_before
         lowcost_after edge_parent_after heap_entries_after inf,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    (forall e, 0 <= e < m -> Znth e wt 0 < inf) ->
    directed_array_graph g from_new to_new wt_new ->
    In src (graph_vertices g) ->
    initStPred g src s_after ->
    minIndex = src ->
    lowcost_parent_match_by
      g (fun v => ~ vvalid s_after.(Prim.graph_in_state) v)
      (fun _ _ => False) lowcost_before edge_parent_before inf ->
    heap_matches_prim_state_by g s_after (fun _ _ => False)
      lowcost_before edge_parent_before inf heap_entries_before ->
    (forall cost vertex, In (cost, vertex) heap_entries_before ->
      0 <= vertex < Zlength lowcost_before) ->
    scan_minIndex_adjacency_heap_update
      g s_after from_new first link to_new wt_new minIndex
      lowcost_before edge_parent_before heap_entries_before
      lowcost_after edge_parent_after heap_entries_after ->
    heap_matches_prim_state g s_after lowcost_after edge_parent_after inf heap_entries_after.
Proof.
  intros n m from to wt g src s_after
         from_new first link to_new wt_new minIndex
         lowcost_before edge_parent_before heap_entries_before
         lowcost_after edge_parent_after heap_entries_after inf
         Hgraph Hfrom_range Hto_range Hwt_range Hdir Hsrc Hinit
         Hmin_src Hmatch_by Hheapmatch_by Hheap_range Hscan.
  destruct Hscan as [scanned_edges [Hchain [Hperm Hfull]]].
  pose proof Hmatch_by as Hmatch_by_full.
  unfold lowcost_parent_match_by in Hmatch_by_full.
  destruct Hmatch_by_full as [Hrange _].
  assert (Hlow_range :
    forall v, In v (graph_vertices g) -> 0 <= v < Zlength lowcost_before).
  { intros v Hv_graph. apply (Hrange v Hv_graph). }
  assert (Hparent_range :
    forall v, In v (graph_vertices g) -> 0 <= v < Zlength edge_parent_before).
  { intros v Hv_graph. apply (Hrange v Hv_graph). }
  assert (Hheap_by :
    heap_matches_prim_state_by g s_after
      (add_scanned_edges_for_vertex g s_after to_new
        (fun _ _ => False) scanned_edges)
      lowcost_after edge_parent_after inf heap_entries_after).
  { eapply scan_directed_edges_full_update_heap_matches_by.
    - exact Hmatch_by.
    - exact Hheapmatch_by.
    - exact Hheap_range.
    - exact Hlow_range.
    - exact Hparent_range.
    - intros de Hde.
      eapply vertex_directed_edges_to_graph_vertex; eauto.
      eapply Permutation_in; [exact Hperm | exact Hde].
    - intros de Hde.
      eapply vertex_directed_edges_range.
      eapply Permutation_in; [exact Hperm | exact Hde].
    - intros de Hde.
      eapply vertex_directed_edges_weight_lt; eauto.
      eapply Permutation_in; [exact Hperm | exact Hde].
    - intros de Hde.
      eapply directed_array_graph_weight; eauto.
      eapply vertex_directed_edges_range.
      eapply Permutation_in; [exact Hperm | exact Hde].
    - exact Hfull. }
  assert (Hheap_by_vertex :
    heap_matches_prim_state_by g s_after
      (add_vertex_directed_edges_for_vertex g s_after from_new to_new minIndex
        (fun _ _ => False))
      lowcost_after edge_parent_after inf heap_entries_after).
  { apply (heap_matches_prim_state_by_iff g s_after
      (add_scanned_edges_for_vertex g s_after to_new
        (fun _ _ => False) scanned_edges)
      (add_vertex_directed_edges_for_vertex g s_after from_new to_new minIndex
        (fun _ _ => False))
      lowcost_after edge_parent_after inf heap_entries_after).
    - intros v e _. apply add_scanned_edges_for_vertex_perm. exact Hperm.
    - exact Hheap_by. }
  unfold initStPred in Hinit.
  subst s_after.
  apply heap_matches_prim_state_by_to.
  apply (heap_matches_prim_state_by_iff g (initSt g src)
    (add_vertex_directed_edges_for_vertex g (initSt g src) from_new to_new minIndex
      (fun _ _ => False))
    (fun v e => is_cut_edge_to_vertex g (initSt g src) v e)
    lowcost_after edge_parent_after inf heap_entries_after).
  - intros v e Hnvout.
    subst minIndex.
    apply (initSt_cut_edges_match n m from to wt g src from_new to_new wt_new
      Hgraph Hdir v e Hnvout).
  - exact Hheap_by_vertex.
Qed.


(** 扫描 [minIndex] 邻接链的起点：0 条边已扫描时，lowcost/edge_parent/
    堆都不变。 *)
Lemma scan_minIndex_adjacency_heap_prefix_start :
  forall g s_next from_new first link to_new wt_new minIndex
         lowcost edge_parent heap_entries,
    first_link_matches_vertex_directed_edges g from_new first link ->
    In minIndex (graph_vertices g) ->
    scan_minIndex_adjacency_heap_prefix_update
      g s_next from_new first link to_new wt_new minIndex
      (Znth minIndex first 0)
      lowcost edge_parent heap_entries
      lowcost edge_parent heap_entries.
Proof.
  intros g s_next from_new first link to_new wt_new minIndex
         lowcost edge_parent heap_entries Hmatch Hmin_graph.
  unfold scan_minIndex_adjacency_heap_prefix_update.
  destruct (Hmatch minIndex Hmin_graph) as [cl [Hchain Hperm]].
  exists nil, cl.
  simpl.
  repeat split; auto.
  constructor.
Qed.

Lemma partial_map_minimum_present :
  forall M item,
    partial_map_minimum M item ->
    partial_map_present M (item_data item) (item_key item).
Proof.
  intros M item Hmin.
  unfold partial_map_minimum, partial_map_item in Hmin.
  tauto.
Qed.

Lemma partial_map_minimum_add_empty_inv :
  forall data key item,
    partial_map_minimum (partial_map_add partial_map_empty data key) item ->
    item_data item = data /\ item_key item = key.
Proof.
  intros data key item Hmin.
  pose proof (partial_map_minimum_present _ _ Hmin) as Hpresent.
  unfold partial_map_present, partial_map_get, partial_map_add,
    partial_map_empty in Hpresent.
  destruct (Z.eq_dec (item_data item) data) as [Heq | Hneq];
    [| discriminate].
  inversion Hpresent.
  split; congruence.
Qed.

Lemma partial_map_minimum_to_min_vertex_in_range :
  forall n m from to wt g s lowcost edge_parent inf M key vertex,
    array_graph n m from to wt g ->
    prim_heap_map_matches_state g s lowcost edge_parent inf M ->
    partial_map_minimum M (heap_item key vertex) ->
    min_vertex_in_range g s n inf vertex lowcost edge_parent.
Proof.
  intros n m from to wt g s lowcost edge_parent inf M key vertex
         Hgraph Hmatch Hmin.
  pose proof (partial_map_minimum_present _ _ Hmin) as Hpresent.
  destruct Hmatch as [Hpresent_match Hcandidate_match].
  destruct (Hpresent_match vertex key Hpresent) as [Hcandidate Hkey].
  unfold min_vertex_in_range.
  right.
  split; [exact Hcandidate |].
  split.
  - destruct Hcandidate as [Hv_graph _].
    rewrite <- In_Zrange.
    eapply array_graph_vertex_range; eauto.
  - unfold min_object_of_subset.
    split.
    + split.
      * destruct Hcandidate as [Hv_graph _].
        rewrite <- In_Zrange.
        eapply array_graph_vertex_range; eauto.
      * exact Hcandidate.
    + intros v [_ Hcandidate_v].
      destruct Hmin as [_ Hmin_key].
      specialize (Hcandidate_match v Hcandidate_v).
      specialize (Hmin_key v (Znth v lowcost 0) Hcandidate_match).
      simpl in Hmin_key.
      simpl.
      rewrite <- Hkey.
      exact Hmin_key.
Qed.

Lemma partial_map_minimum_to_min_vertex_in_lowcost_range :
  forall g s lowcost edge_parent inf M key vertex,
    lowcost_parent_match g s lowcost edge_parent inf ->
    prim_heap_map_matches_state g s lowcost edge_parent inf M ->
    partial_map_minimum M (heap_item key vertex) ->
    min_vertex_in_range
      g s (Zlength lowcost) inf vertex lowcost edge_parent.
Proof.
  intros g s lowcost edge_parent inf M key vertex
         Hlow_match Hmatch Hmin.
  pose proof (partial_map_minimum_present _ _ Hmin) as Hpresent.
  destruct Hmatch as [Hpresent_match Hcandidate_match].
  destruct (Hpresent_match vertex key Hpresent) as [Hcandidate Hkey].
  destruct Hlow_match as [Hrange _].
  unfold min_vertex_in_range.
  right.
  split; [exact Hcandidate |].
  split.
  - destruct Hcandidate as [Hv_graph _].
    rewrite <- In_Zrange.
    destruct (Hrange vertex Hv_graph) as [Hv_range _].
    exact Hv_range.
  - unfold min_object_of_subset.
    split.
    + split.
      * destruct Hcandidate as [Hv_graph _].
        rewrite <- In_Zrange.
        destruct (Hrange vertex Hv_graph) as [Hv_range _].
        exact Hv_range.
      * exact Hcandidate.
    + intros v [_ Hcandidate_v].
      destruct Hmin as [_ Hmin_key].
      specialize (Hcandidate_match v Hcandidate_v).
      specialize (Hmin_key v (Znth v lowcost 0) Hcandidate_match).
      simpl in Hmin_key.
      simpl.
      rewrite <- Hkey.
      exact Hmin_key.
Qed.

Lemma candidate_vertex_lowcost_int_range :
  forall n m from to wt g s lowcost edge_parent vertex,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m ->
      0 <= Znth e wt 0 /\ Znth e wt 0 < 1000000000) ->
    candidate_vertex g s lowcost edge_parent 1000000000 vertex ->
    INT_MIN <= Znth vertex lowcost 0 <= INT_MAX.
Proof.
  intros n m from to wt g s lowcost edge_parent vertex
         Hgraph Hwt_range Hcandidate.
  unfold candidate_vertex, vertex_has_parent_edge in Hcandidate.
  destruct Hcandidate as
    [_ [_ [_ [Hde_range [Hlow_lt [_ Hweight]]]]]].
  pose proof (array_graph_edge_count n m from to wt g Hgraph) as Hcount.
  pose proof (directed_edge_div2_bound g (Znth vertex edge_parent 0)
    Hde_range) as Hhalf.
  rewrite Hcount in Hhalf.
  pose proof (Hwt_range (Znth vertex edge_parent 0 / 2) Hhalf)
    as Hwt.
  destruct Hwt as [Hwt_nonneg Hwt_lt].
  assert (Hgraph_weight :
    graph_weight g (Znth vertex edge_parent 0 / 2) =
    Znth (Znth vertex edge_parent 0 / 2) wt 0).
  {
    unfold array_graph in Hgraph.
    destruct Hgraph as [_ [_ [_ [_ [_ [_ [_ Hedges]]]]]]].
    specialize (Hedges (Znth vertex edge_parent 0 / 2)).
    assert (Hin : In (Znth vertex edge_parent 0 / 2) (Zrange 0 m)).
    { rewrite <- In_Zrange. exact Hhalf. }
    specialize (Hedges Hin).
    tauto.
  }
  change (Some (graph_weight g (Znth vertex edge_parent 0 / 2)) =
          Some (Znth vertex lowcost 0)) in Hweight.
  injection Hweight as Hlow_eq.
  rewrite <- Hlow_eq.
  rewrite Hgraph_weight.
  split; lia.
Qed.

Lemma prim_heap_loop_pop_after :
  forall n m from to wt g src chosen s lowcost visited edge_parent
         M_before key vertex X,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m ->
      0 <= Znth e wt 0 /\ Znth e wt 0 < 1000000000) ->
    In src (graph_vertices g) ->
    0 <= chosen < n ->
    prim_heap_loop_state
      g src chosen s lowcost visited edge_parent M_before X ->
    partial_map_minimum M_before (heap_item key vertex) ->
    prim_queue_map_pop
      M_before (partial_map_remove M_before vertex) vertex key /\
    prim_heap_after_pop_state
      g src chosen s lowcost visited edge_parent
      M_before (partial_map_remove M_before vertex) vertex key X /\
    0 <= vertex < n /\
    INT_MIN <= key <= INT_MAX.
Proof.
  intros n m from to wt g src chosen s lowcost visited edge_parent
         M_before key vertex X Hgraph Hwt_range Hsrc_graph Hchosen
         Hloop Hmin.
  assert (Hpop :
    prim_queue_map_pop M_before
      (partial_map_remove M_before vertex) vertex key).
  {
    unfold prim_queue_map_pop.
    split; [exact Hmin | reflexivity].
  }
  destruct Hloop as
    [[Hchosen0 [Hs [Hlow [Hvisited [Hparent [HM Hsafe]]]]]] |
     [Hchosen1 [Hgrowing [Hvisited_match [Hcount
       [Hselected [Hlow_match [Hmap_match Hsafe]]]]]]]].
  - subst chosen s M_before.
    pose proof (partial_map_minimum_add_empty_inv
      src 0 (heap_item key vertex) Hmin) as Hinv.
    simpl in Hinv.
    destruct Hinv as [Hvertex Hkey].
    subst vertex key.
    split; [exact Hpop |].
    split.
    + unfold prim_heap_after_pop_state.
      split.
      * left. repeat split; assumption.
      * split; [exact Hpop |].
        left.
        repeat split; reflexivity.
    + split.
      * eapply array_graph_vertex_range; eauto.
      * lia.
  - pose proof Hmap_match as Hmap_match_all.
    destruct Hmap_match as [Hpresent_match Hcandidate_match].
    pose proof (partial_map_minimum_present _ _ Hmin) as Hpresent.
    destruct (Hpresent_match vertex key Hpresent) as [Hcandidate Hkey].
    assert (Hmin_vertex :
      min_vertex_in_range g s n 1000000000 vertex lowcost edge_parent).
    {
      eapply partial_map_minimum_to_min_vertex_in_range; eauto.
    }
    assert (Hmin_vertex_len :
      min_vertex_in_range
        g s (Zlength lowcost) 1000000000 vertex lowcost edge_parent).
    {
      eapply partial_map_minimum_to_min_vertex_in_lowcost_range; eauto.
    }
    assert (Hselect :
      prim_heap_map_pop_selects_min_vertex
        g s lowcost edge_parent 1000000000 M_before key vertex).
    {
      unfold prim_heap_map_pop_selects_min_vertex.
      split; [exact Hmin |].
      split; [exact Hmap_match_all |].
      split; [exact Hkey | exact Hmin_vertex_len].
    }
    split; [exact Hpop |].
    split.
    + unfold prim_heap_after_pop_state.
      split.
      * right.
        split; [exact Hchosen1 |].
        split; [exact Hgrowing |].
        split; [exact Hvisited_match |].
        split; [exact Hcount |].
        split; [exact Hselected |].
        split; [exact Hlow_match |].
        split; [exact Hmap_match_all | exact Hsafe].
      * split; [exact Hpop |].
        right.
        split; [lia | exact Hselect].
    + split.
      * destruct Hcandidate as [Hv_graph _].
        eapply array_graph_vertex_range; eauto.
      * rewrite Hkey.
        eapply candidate_vertex_lowcost_int_range; eauto.
Qed.

Lemma prim_heap_map_after_pop_by_selected_add :
  forall n m from to wt g s_before s_after
         from_new to_new lowcost visited edge_parent
         M_before M_after minIndex minCost,
    array_graph n m from to wt g ->
    Zlength visited = n ->
    In minIndex (graph_vertices g) ->
    visited_matches_state g s_before visited ->
    prim_heap_map_matches_state
      g s_before lowcost edge_parent 1000000000 M_before ->
    prim_queue_map_pop M_before M_after minIndex minCost ->
    selected_parent_add_to_mst
      g s_before s_after from_new to_new edge_parent minIndex ->
    prim_heap_map_matches_state_by
      g s_after
      (fun v e => is_cut_edge_to_vertex g s_before v e)
      lowcost edge_parent 1000000000 M_after.
Proof.
  intros n m from to wt g s_before s_after
         from_new to_new lowcost visited edge_parent
         M_before M_after minIndex minCost
         Hgraph Hvisited_len Hmin_graph Hvisited_before Hmap_before
         Hpop Hadd.
  unfold prim_queue_map_pop in Hpop.
  destruct Hpop as [_ HM_after].
  subst M_after.
  assert (Hvisited_after :
    visited_matches_state g s_after (replace_Znth minIndex 1 visited)).
  {
    eapply selected_parent_add_to_mst_visited_matches; eauto.
  }
  split.
  - intros vertex key Hpresent_after.
    apply partial_map_remove_present_inv in Hpresent_after
      as [Hvertex_ne Hpresent_before].
    destruct Hmap_before as [Hpresent_match _].
    destruct (Hpresent_match vertex key Hpresent_before)
      as [Hcandidate_before Hkey].
    assert (Hvertex_graph : In vertex (graph_vertices g)).
    { unfold candidate_vertex in Hcandidate_before.
      tauto. }
    assert (Hvertex_range : 0 <= vertex < Zlength visited).
    { rewrite Hvisited_len.
      eapply array_graph_vertex_range; eauto. }
    assert (Hmin_range : 0 <= minIndex < Zlength visited).
    { rewrite Hvisited_len.
      eapply array_graph_vertex_range; eauto. }
    split; [| exact Hkey].
    apply (proj1 (candidate_vertex_pop_iff
      g s_before s_after visited lowcost edge_parent 1000000000
      minIndex vertex Hvertex_graph Hmin_range Hvertex_range
      Hvisited_before Hvisited_after Hvertex_ne)).
    exact Hcandidate_before.
  - intros vertex Hcandidate_after.
    assert (Hvertex_ne : vertex <> minIndex).
    {
      intro Hvertex_eq.
      subst vertex.
      unfold candidate_vertex_by in Hcandidate_after.
      destruct Hcandidate_after as [_ [Hout _]].
      apply Hout.
      eapply selected_parent_add_to_mst_minIndex_vvalid; eauto.
    }
    assert (Hvertex_graph : In vertex (graph_vertices g)).
    { unfold candidate_vertex_by in Hcandidate_after.
      tauto. }
    assert (Hvertex_range : 0 <= vertex < Zlength visited).
    { rewrite Hvisited_len.
      eapply array_graph_vertex_range; eauto. }
    assert (Hmin_range : 0 <= minIndex < Zlength visited).
    { rewrite Hvisited_len.
      eapply array_graph_vertex_range; eauto. }
    destruct Hmap_before as [_ Hcandidate_match].
    apply partial_map_remove_present_other; [exact Hvertex_ne |].
    apply Hcandidate_match.
    apply (proj2 (candidate_vertex_pop_iff
      g s_before s_after visited lowcost edge_parent 1000000000
      minIndex vertex Hvertex_graph Hmin_range Hvertex_range
      Hvisited_before Hvisited_after Hvertex_ne)).
    exact Hcandidate_after.
Qed.

Lemma prim_heap_after_pop_scan_start :
  forall n m from to wt g src chosen s_before
         from_new first link to_new wt_new
         lowcost visited edge_parent M_before M_after
         minIndex minCost X,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    (forall e, 0 <= e < m ->
      0 <= Znth e wt 0 /\ Znth e wt 0 < 1000000000) ->
    directed_array_graph g from_new to_new wt_new ->
    first_link_matches_vertex_directed_edges g from_new first link ->
    In src (graph_vertices g) ->
    Zlength lowcost = n ->
    Zlength visited = n ->
    Zlength edge_parent = n ->
    0 <= chosen < n ->
    0 <= minIndex < n ->
    prim_heap_after_pop_state
      g src chosen s_before lowcost visited edge_parent
      M_before M_after minIndex minCost X ->
    exists s_after,
      prim_heap_scan_state
        g src (chosen + 1) s_before s_after
        from_new first link to_new wt_new
        lowcost (replace_Znth minIndex 1 visited) edge_parent
        lowcost edge_parent (Znth minIndex first 0)
        minIndex minCost M_after
        lowcost edge_parent M_after X.
Proof.
  intros n m from to wt g src chosen s_before
         from_new first link to_new wt_new
         lowcost visited edge_parent M_before M_after
         minIndex minCost X
         Hgraph Hfrom_range Hto_range Hwt_range Hdir Hfirst Hsrc
         Hlow_len Hvisited_len Hparent_len Hchosen Hmin_range Hafter.
  unfold prim_heap_after_pop_state in Hafter.
  destruct Hafter as [Hloop [Hpop Hcase]].
  destruct Hcase as
    [[Hchosen0 [Hmin_src [Hmin_cost Hs_before]]]
    | [Hchosen_pos Hselect]].
  - destruct Hloop as
      [[_ [Hs_loop [Hlow_init [Hvisited_init
        [Hparent_init [HM_before Hsafe]]]]]]
      | [Hchosen_loop _]]; [| lia].
    subst chosen minIndex minCost s_before.
    exists (initSt g src).
    assert (Hlow_init_n :
      lowcost = replace_Znth src 0
        (repeat 1000000000 (Z.to_nat n))).
    { rewrite Hlow_init, Hlow_len. reflexivity. }
    assert (Hvisited_init_n :
      visited = repeat 0 (Z.to_nat n)).
    { rewrite Hvisited_init, Hvisited_len. reflexivity. }
    assert (Hparent_init_n :
      edge_parent = repeat (-1) (Z.to_nat n)).
    { rewrite Hparent_init, Hparent_len. reflexivity. }
    assert (Hvisited_after :
      visited_matches_state g (initSt g src)
        (replace_Znth src 1 visited)).
    {
      rewrite Hvisited_init_n.
      unfold visited_matches_state.
      intros v Hv_graph.
      rewrite initSt_vvalid.
      destruct (Z.eq_dec v src) as [Hv_eq | Hv_ne].
      + subst v.
        rewrite Znth_replace_Znth_same_local.
        * split; intros _; [reflexivity | lia].
        * rewrite Zlength_correct, repeat_length.
          rewrite Z2Nat.id by lia.
          eapply array_graph_vertex_range; eauto.
      + assert (Hv_range : 0 <= v < n)
          by (eapply array_graph_vertex_range; eauto).
        assert (Hsrc_range : 0 <= src < n)
          by (eapply array_graph_vertex_range; eauto).
        rewrite Znth_replace_Znth_diff_local.
        * rewrite Znth_repeat_lt by
            (rewrite Z2Nat.id by lia; exact Hv_range).
          split; intros H; [contradiction | contradiction].
        * rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
          exact Hsrc_range.
        * rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
          exact Hv_range.
        * intro Heq; apply Hv_ne; symmetry; exact Heq.
    }
    assert (Hparent_after :
      selected_edges_match_state g src (initSt g src) edge_parent).
    {
      unfold selected_edges_match_state, parent_edges_match_state.
      split.
      + apply initSt_vvalid; reflexivity.
      + split.
        * intros v _ Hv_not_src Hv_valid.
          apply initSt_vvalid in Hv_valid.
          contradiction.
        * intros e.
          split.
          -- intro He.
             unfold initSt in He.
             simpl in He.
             unfold empty_graph_of, graph_instance, edge_valid in He.
             simpl in He.
             contradiction.
          -- intros [v [_ [Hv_not_src [Hv _]]]].
             apply initSt_vvalid in Hv.
             contradiction.
    }
    assert (Hlow_by :
      lowcost_parent_match_by
        g
        (fun v => ~ vvalid (Prim.graph_in_state (initSt g src)) v)
        (fun _ _ => False)
        lowcost edge_parent 1000000000).
    {
      rewrite Hlow_init_n, Hparent_init_n.
      eapply init_lowcost_parent_match_by_empty; eauto.
    }
    assert (Hmap_by :
      prim_heap_map_matches_state_by
        g (initSt g src) (fun _ _ => False)
        lowcost edge_parent 1000000000 M_after).
    {
      unfold prim_queue_map_pop in Hpop.
      destruct Hpop as [_ HM_after].
      subst M_after M_before.
      split.
      - intros vertex key Hpresent.
        unfold partial_map_present, partial_map_get,
          partial_map_remove, partial_map_add, partial_map_empty in Hpresent.
        destruct (Z.eq_dec vertex src); discriminate.
      - intros vertex Hcandidate.
        unfold candidate_vertex_by in Hcandidate.
        destruct Hcandidate as [Hvertex_graph [_ [Hparent_ne _]]].
        rewrite Hparent_init_n in Hparent_ne.
        assert (Hvertex_range : 0 <= vertex < n).
        { eapply array_graph_vertex_range; eauto. }
        rewrite Znth_repeat_lt in Hparent_ne by
          (rewrite Z2Nat.id by lia; exact Hvertex_range).
        contradiction.
    }
    assert (Hscan_prefix :
      scan_minIndex_adjacency_map_prefix_update
        g (initSt g src) from_new first link to_new wt_new src
        (Znth src first 0)
        lowcost edge_parent M_after
        lowcost edge_parent M_after).
    {
      unfold scan_minIndex_adjacency_map_prefix_update.
      destruct (Hfirst src Hsrc) as [cl [Hchain Hperm]].
      exists (fun _ _ => False), nil, cl.
      simpl.
      split; [exact Hchain |].
      split; [exact Hchain |].
      split; [exact Hperm |].
      split; [constructor |].
      split; [exact Hlow_by |].
      split; [exact Hmap_by |].
      intros v e Hvout.
      eapply initSt_cut_edges_match
        with (n := n) (m := m) (from := from) (to := to)
             (wt := wt) (wt_new := wt_new); eauto.
    }
    assert (Hsafe_loop :
      safeExec (prim_state_is (initSt g src)) (Prim2_loop g 0) X).
    {
      unfold Prim2, Prim2_loop, initStPred, prim_state_is in *.
      exact Hsafe.
    }
    unfold prim_heap_scan_state.
    split; [lia |].
    split; [eapply initSt_growing_subgraph_state; eauto |].
    split; [exact Hvisited_after |].
    split; [rewrite initSt_state_vertex_count; lia |].
    split; [exact Hparent_after |].
    split; [exact Hscan_prefix |].
    split; [reflexivity |].
    split; [reflexivity |].
    exact Hsafe_loop.
  - unfold prim_heap_map_pop_selects_min_vertex in Hselect.
    destruct Hselect as [Hmin_map [Hmap_before [Hmin_key Hmin_vertex_len]]].
    assert (Hmin_vertex :
      min_vertex_in_range g s_before n 1000000000
        minIndex lowcost edge_parent).
    { rewrite <- Hlow_len. exact Hmin_vertex_len. }
    assert (Hmin_graph : In minIndex (graph_vertices g)).
    { eapply array_graph_vertex_in; eauto; lia. }
    destruct Hloop as
      [[Hchosen_init _]
      | [Hchosen_loop [Hgrowing [Hvisited_before [Hcount
        [Hparent_before [Hlow_before [Hmap_loop Hsafe]]]]]]]];
      [lia |].
    assert (Hselected_edge :
      selected_parent_edge_is_min_cut_edge
        g s_before edge_parent minIndex).
    {
      eapply min_vertex_parent_is_min_cut_edge
        with (n := n) (m := m) (from := from) (to := to)
             (wt := wt) (lowcost := lowcost) (inf := 1000000000);
        eauto; lia.
    }
    destruct (selected_parent_add_to_mst_exists
      n m from to wt g s_before from_new to_new lowcost edge_parent
      minIndex Hgraph Hfrom_range Hto_range Hgrowing
      Hmin_vertex ltac:(lia))
      as [u [v [s_after [Hpair [Hadd Hcount_after]]]]].
    exists s_after.
    assert (Hvisited_after :
      visited_matches_state g s_after
        (replace_Znth minIndex 1 visited)).
    {
      eapply selected_parent_add_to_mst_visited_matches; eauto.
    }
    assert (Hparent_min_range :
      0 <= Znth minIndex edge_parent 0 < 2 * graph_edge_count g).
    {
      destruct Hmin_vertex as [[Hminus _] | [Hcandidate _]];
        [lia |].
      unfold candidate_vertex, vertex_has_parent_edge in Hcandidate.
      tauto.
    }
    assert (Hparent_after :
      selected_edges_match_state g src s_after edge_parent).
    {
      eapply selected_parent_add_to_mst_parent_edges_match; eauto.
    }
    assert (Hlow_by :
      lowcost_parent_match_by
        g
        (fun v => ~ vvalid (Prim.graph_in_state s_after) v)
        (fun v e => is_cut_edge_to_vertex g s_before v e)
        lowcost edge_parent 1000000000).
    {
      eapply lowcost_parent_match_by_iff.
      - eapply lowcost_parent_match_to_by; eauto.
      - intros x _ Hout_after Hvalid_before.
        apply Hout_after.
        eapply selected_parent_add_to_mst_old_vvalid; eauto.
      - intros x e _ _.
        reflexivity.
    }
    assert (Hmap_by :
      prim_heap_map_matches_state_by
        g s_after
        (fun v e => is_cut_edge_to_vertex g s_before v e)
        lowcost edge_parent 1000000000 M_after).
    {
      eapply prim_heap_map_after_pop_by_selected_add.
      - exact Hgraph.
      - exact Hvisited_len.
      - exact Hmin_graph.
      - exact Hvisited_before.
      - exact Hmap_before.
      - exact Hpop.
      - exact Hadd.
    }
    assert (Hscan_prefix :
      scan_minIndex_adjacency_map_prefix_update
        g s_after from_new first link to_new wt_new minIndex
        (Znth minIndex first 0)
        lowcost edge_parent M_after
        lowcost edge_parent M_after).
    {
      unfold scan_minIndex_adjacency_map_prefix_update.
      destruct (Hfirst minIndex Hmin_graph) as [cl [Hchain Hperm]].
      exists (fun v e => is_cut_edge_to_vertex g s_before v e), nil, cl.
      simpl.
      split; [exact Hchain |].
      split; [exact Hchain |].
      split; [exact Hperm |].
      split; [constructor |].
      split; [exact Hlow_by |].
      split; [exact Hmap_by |].
      intros x e Hout_after.
      eapply selected_parent_add_to_mst_cut_edges_match
        with (n := n) (m := m) (from := from) (to := to)
             (wt := wt) (wt_new := wt_new)
             (edge_parent := edge_parent); eauto.
    }
    assert (Hsafe_after :
      safeExec (prim_state_is s_after) (Prim2_loop g chosen) X).
    {
      eapply selected_parent_prim2_loop_step
        with (n := n) (m := m) (from := from) (to := to)
             (wt := wt) (s := s_before) (from_new := from_new)
             (to_new := to_new) (edge_parent := edge_parent)
             (minIndex := minIndex).
      - eapply array_graph_gvalid; eauto.
      - exact Hgraph.
      - lia.
      - lia.
      - exact Hsafe.
      - exact Hselected_edge.
      - exact Hadd.
    }
    unfold prim_heap_scan_state.
    split; [lia |].
    split; [eapply selected_parent_add_to_mst_growing; eauto |].
    split; [exact Hvisited_after |].
    split; [rewrite Hcount_after, Hcount; lia |].
    split; [exact Hparent_after |].
    split; [exact Hscan_prefix |].
    split; [reflexivity |].
    split; [reflexivity |].
    replace (chosen + 1 - 1) with chosen by lia.
    exact Hsafe_after.
Qed.

Lemma partial_map_update_or_add_pre_from_key_le :
  forall M data key,
    (forall old_key, partial_map_present M data old_key -> key <= old_key) ->
    partial_map_update_or_add_pre M data key.
Proof.
  intros M data key Hle.
  destruct (M data) as [old_key |] eqn:Hget.
  - right.
    exists old_key.
    split.
    + unfold heap_key_of, partial_map_present, partial_map_get.
      exact Hget.
    + apply Hle.
      unfold partial_map_present, partial_map_get.
      exact Hget.
  - left.
    unfold heap_data_absent, partial_map_absent, partial_map_get.
    exact Hget.
Qed.

Lemma scan_directed_edges_partial_map_update_to_scan :
  forall g s_next to_new wt_new scanned_edges
         lowcost_before edge_parent_before M_before
         lowcost_after edge_parent_after M_after,
    scan_directed_edges_partial_map_update
      g s_next to_new wt_new scanned_edges
      lowcost_before edge_parent_before M_before
      lowcost_after edge_parent_after M_after ->
    scan_directed_edges_update
      g s_next to_new wt_new scanned_edges
      lowcost_before edge_parent_before
      lowcost_after edge_parent_after.
Proof.
  intros g s_next to_new wt_new scanned_edges
         lowcost_before edge_parent_before M_before
         lowcost_after edge_parent_after M_after Hscan.
  induction Hscan.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma scan_directed_edges_partial_map_update_app :
  forall g s_next to_new wt_new l1 l2
         lowcost0 edge_parent0 M0
         lowcost1 edge_parent1 M1
         lowcost2 edge_parent2 M2,
    scan_directed_edges_partial_map_update
      g s_next to_new wt_new l1
      lowcost0 edge_parent0 M0
      lowcost1 edge_parent1 M1 ->
    scan_directed_edges_partial_map_update
      g s_next to_new wt_new l2
      lowcost1 edge_parent1 M1
      lowcost2 edge_parent2 M2 ->
    scan_directed_edges_partial_map_update
      g s_next to_new wt_new (l1 ++ l2)
      lowcost0 edge_parent0 M0
      lowcost2 edge_parent2 M2.
Proof.
  intros g s_next to_new wt_new l1 l2
         lowcost0 edge_parent0 M0
         lowcost1 edge_parent1 M1
         lowcost2 edge_parent2 M2 Hscan1 Hscan2.
  induction Hscan1.
  - simpl. exact Hscan2.
  - simpl. econstructor; eauto.
Qed.

Lemma scan_directed_edges_partial_map_update_snoc :
  forall g s_next to_new wt_new scanned_edges
         lowcost0 edge_parent0 M0
         lowcost1 edge_parent1 M1
         de lowcost2 edge_parent2 M2,
    scan_directed_edges_partial_map_update
      g s_next to_new wt_new scanned_edges
      lowcost0 edge_parent0 M0
      lowcost1 edge_parent1 M1 ->
    scan_one_directed_edge_update
      g s_next to_new wt_new
      lowcost1 edge_parent1 de
      lowcost2 edge_parent2 ->
    partial_map_update_one_directed_edge
      g s_next to_new wt_new lowcost1 de M1 M2 ->
    scan_directed_edges_partial_map_update
      g s_next to_new wt_new (scanned_edges ++ de :: nil)
      lowcost0 edge_parent0 M0
      lowcost2 edge_parent2 M2.
Proof.
  intros.
  eapply scan_directed_edges_partial_map_update_app; [eauto |].
  simpl.
  econstructor; [eauto | eauto | constructor].
Qed.

Lemma add_scanned_edges_for_vertex_snoc_iff :
  forall g s_next to_new edge_for_vertex scanned_edges de v e,
    add_scanned_edges_for_vertex
      g s_next to_new edge_for_vertex (scanned_edges ++ de :: nil) v e <->
    add_scanned_edge_for_vertex
      g s_next to_new
      (add_scanned_edges_for_vertex
        g s_next to_new edge_for_vertex scanned_edges)
      de v e.
Proof.
  intros g s_next to_new edge_for_vertex scanned_edges.
  revert edge_for_vertex.
  induction scanned_edges as [| de0 rest IH]; intros edge_for_vertex de v e; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma prim_heap_map_matches_state_by_iff :
  forall g s edge_for1 edge_for2 lowcost edge_parent inf M,
    prim_heap_map_matches_state_by g s edge_for1 lowcost edge_parent inf M ->
    (forall v e,
      ~ vvalid s.(Prim.graph_in_state) v ->
      edge_for1 v e <-> edge_for2 v e) ->
    prim_heap_map_matches_state_by g s edge_for2 lowcost edge_parent inf M.
Proof.
  intros g s edge_for1 edge_for2 lowcost edge_parent inf M
         [Hpresent Hcandidate] Hedge.
  split.
  - intros vertex key Hmap.
    destruct (Hpresent vertex key Hmap) as [Hcand Hkey].
    split; [| exact Hkey].
    apply (proj1 (candidate_vertex_by_iff
      g s edge_for1 edge_for2 lowcost edge_parent inf vertex
      (fun e Hout => Hedge vertex e Hout))).
    exact Hcand.
  - intros vertex Hcand.
    apply Hcandidate.
    apply (proj2 (candidate_vertex_by_iff
      g s edge_for1 edge_for2 lowcost edge_parent inf vertex
      (fun e Hout => Hedge vertex e Hout))).
    exact Hcand.
Qed.

Lemma prim_heap_map_matches_state_by_to_state :
  forall g s edge_for lowcost edge_parent inf M,
    prim_heap_map_matches_state_by g s edge_for lowcost edge_parent inf M ->
    (forall v e,
      In v (graph_vertices g) ->
      ~ vvalid s.(Prim.graph_in_state) v ->
      edge_for v e <-> is_cut_edge_to_vertex g s v e) ->
    prim_heap_map_matches_state g s lowcost edge_parent inf M.
Proof.
  intros g s edge_for lowcost edge_parent inf M Hmatch Hedge.
  unfold prim_heap_map_matches_state.
  split.
  - intros vertex key Hpresent.
    destruct Hmatch as [Hmap _].
    destruct (Hmap vertex key Hpresent) as [Hcand_by Hkey].
    split; [| exact Hkey].
    unfold candidate_vertex, vertex_has_parent_edge.
    unfold candidate_vertex_by in Hcand_by.
    destruct Hcand_by as
      [Hv_graph [Hv_out [Hde_ne [Hde_range [Hlow [Hmin Hweight]]]]]].
    split.
    + exact Hv_graph.
    + split; [exact Hv_out |].
      split; [exact Hde_ne |].
      split; [exact Hde_range |].
      split; [exact Hlow |].
      split.
      * unfold is_min_cut_edge_to_vertex.
        unfold min_object_of_subset in *.
        destruct Hmin as [Hedge_member Hmin].
        split.
        -- apply (proj1 (Hedge vertex (Znth vertex edge_parent 0 / 2)
             Hv_graph Hv_out)).
           exact Hedge_member.
        -- intros e Hcut.
           apply Hmin.
           apply (proj2 (Hedge vertex e Hv_graph Hv_out)).
           exact Hcut.
      * exact Hweight.
  - intros vertex Hcandidate.
    destruct Hmatch as [_ Hmap].
    apply Hmap.
    unfold candidate_vertex, vertex_has_parent_edge in Hcandidate.
    unfold candidate_vertex_by.
    destruct Hcandidate as
      [Hv_graph [Hv_out [Hde_ne [Hde_range [Hlow [Hmin Hweight]]]]]].
    split.
    + exact Hv_graph.
    + split; [exact Hv_out |].
      split; [exact Hde_ne |].
      split; [exact Hde_range |].
      split; [exact Hlow |].
      split.
      * unfold is_min_cut_edge_to_vertex in Hmin.
        unfold min_object_of_subset in *.
        destruct Hmin as [Hedge_member Hmin].
        split.
        -- apply (proj2 (Hedge vertex (Znth vertex edge_parent 0 / 2)
             Hv_graph Hv_out)).
           exact Hedge_member.
        -- intros e Hedge_member2.
           apply Hmin.
           apply (proj1 (Hedge vertex e Hv_graph Hv_out)).
           exact Hedge_member2.
      * exact Hweight.
Qed.

Lemma prim_heap_map_matches_state_to_by_state :
  forall g s edge_for lowcost edge_parent inf M,
    prim_heap_map_matches_state g s lowcost edge_parent inf M ->
    (forall v e,
      In v (graph_vertices g) ->
      ~ vvalid s.(Prim.graph_in_state) v ->
      edge_for v e <-> is_cut_edge_to_vertex g s v e) ->
    prim_heap_map_matches_state_by g s edge_for lowcost edge_parent inf M.
Proof.
  intros g s edge_for lowcost edge_parent inf M Hmatch Hedge.
  split.
  - intros vertex key Hpresent.
    destruct Hmatch as [Hmap _].
    destruct (Hmap vertex key Hpresent) as [Hcandidate Hkey].
    split; [| exact Hkey].
    unfold candidate_vertex, vertex_has_parent_edge in Hcandidate.
    unfold candidate_vertex_by.
    destruct Hcandidate as
      [Hv_graph [Hv_out [Hde_ne [Hde_range [Hlow [Hmin Hweight]]]]]].
    split.
    + exact Hv_graph.
    + split; [exact Hv_out |].
      split; [exact Hde_ne |].
      split; [exact Hde_range |].
      split; [exact Hlow |].
      split.
      * unfold is_min_cut_edge_to_vertex in Hmin.
        unfold min_object_of_subset in *.
        destruct Hmin as [Hedge_member Hmin].
        split.
        -- apply (proj2 (Hedge vertex (Znth vertex edge_parent 0 / 2)
             Hv_graph Hv_out)).
           exact Hedge_member.
        -- intros e Hedge_member2.
           apply Hmin.
           apply (proj1 (Hedge vertex e Hv_graph Hv_out)).
           exact Hedge_member2.
      * exact Hweight.
  - intros vertex Hcand_by.
    destruct Hmatch as [_ Hmap].
    apply Hmap.
    unfold candidate_vertex, vertex_has_parent_edge.
    unfold candidate_vertex_by in Hcand_by.
    destruct Hcand_by as
      [Hv_graph [Hv_out [Hde_ne [Hde_range [Hlow [Hmin Hweight]]]]]].
    split.
    + exact Hv_graph.
    + split; [exact Hv_out |].
      split; [exact Hde_ne |].
      split; [exact Hde_range |].
      split; [exact Hlow |].
      split.
      * unfold is_min_cut_edge_to_vertex.
        unfold min_object_of_subset in *.
        destruct Hmin as [Hedge_member Hmin].
        split.
        -- apply (proj1 (Hedge vertex (Znth vertex edge_parent 0 / 2)
             Hv_graph Hv_out)).
           exact Hedge_member.
        -- intros e Hcut.
           apply Hmin.
           apply (proj2 (Hedge vertex e Hv_graph Hv_out)).
           exact Hcut.
      * exact Hweight.
Qed.

Lemma prim_heap_map_matches_state_by_one_directed_edge :
  forall g s_next to_new wt_new edge_for_vertex de
         lowcost_in edge_parent_in M_in
         lowcost_out edge_parent_out M_out inf,
    In (Znth de to_new 0) (graph_vertices g) ->
    0 <= de < 2 * graph_edge_count g ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength lowcost_in) ->
    (forall v, In v (graph_vertices g) -> 0 <= v < Zlength edge_parent_in) ->
    Znth de wt_new 0 < inf ->
    weight g (de / 2) = Some (Znth de wt_new 0) ->
    lowcost_parent_match_by
      g (fun v => ~ vvalid s_next.(Prim.graph_in_state) v)
      edge_for_vertex lowcost_in edge_parent_in inf ->
    prim_heap_map_matches_state_by
      g s_next edge_for_vertex lowcost_in edge_parent_in inf M_in ->
    scan_one_directed_edge_update
      g s_next to_new wt_new
      lowcost_in edge_parent_in de
      lowcost_out edge_parent_out ->
    partial_map_update_one_directed_edge
      g s_next to_new wt_new lowcost_in de M_in M_out ->
    prim_heap_map_matches_state_by
      g s_next
      (add_scanned_edge_for_vertex g s_next to_new edge_for_vertex de)
      lowcost_out edge_parent_out inf M_out.
Proof.
  intros g s_next to_new wt_new edge_for_vertex de
         lowcost_in edge_parent_in M_in
         lowcost_out edge_parent_out M_out inf
         Htarget_graph Hde_range Hlow_range Hparent_range Hwt_inf Hweight
         Hlow_match Hmap_match Hscan Hmap_step.
  assert (Hv_range : 0 <= Znth de to_new 0 < Zlength lowcost_in)
    by (apply Hlow_range; exact Htarget_graph).
  assert (Hv_parent_range : 0 <= Znth de to_new 0 < Zlength edge_parent_in)
    by (apply Hparent_range; exact Htarget_graph).
  pose proof (scan_one_directed_edge_update_lowcost_parent_match_by
    g s_next to_new wt_new
    (fun v => ~ vvalid s_next.(Prim.graph_in_state) v)
    edge_for_vertex lowcost_in edge_parent_in de
    lowcost_out edge_parent_out inf
    Hlow_match Hscan Htarget_graph Hde_range Hlow_range Hparent_range
    Hwt_inf Hweight) as Hlow_after.
  unfold scan_one_directed_edge_update in Hscan.
  unfold partial_map_update_one_directed_edge in Hmap_step.
  set (v := Znth de to_new 0) in *.
  set (w := Znth de wt_new 0) in *.
  destruct Hscan as
    [[Hcut [Hlt [Hlow_out Hparent_out]]] |
     [Hno_update [Hlow_out Hparent_out]]];
    destruct Hmap_step as
      [[Hcut_map [Hlt_map Hmap_out]] |
       [Hno_map Hmap_out]].
  - subst lowcost_out edge_parent_out M_out.
    split.
    + intros vertex key Hpresent.
      pose proof (partial_map_update_or_add_present_inv
        M_in v w vertex key Hpresent) as Hinv.
      destruct Hinv as [[Hvertex Hkey] | [Hneq Hpresent_old]].
      * subst vertex key.
        split.
        -- eapply candidate_vertex_by_of_lowcost.
           ++ exact Htarget_graph.
           ++ unfold is_cut_edge_to_vertex in Hcut.
              tauto.
           ++ rewrite Znth_replace_Znth_same_local by exact Hv_range.
              exact Hwt_inf.
           ++ exact Hlow_after.
        -- rewrite Znth_replace_Znth_same_local by exact Hv_range.
           reflexivity.
      * destruct Hmap_match as [Hmap_present _].
        destruct (Hmap_present vertex key Hpresent_old) as [Hcand_old Hkey_old].
        assert (Hvertex_graph : In vertex (graph_vertices g)).
        { unfold candidate_vertex_by in Hcand_old. tauto. }
        assert (Hvertex_low_range : 0 <= vertex < Zlength lowcost_in)
          by (apply Hlow_range; exact Hvertex_graph).
        assert (Hvertex_parent_range : 0 <= vertex < Zlength edge_parent_in)
          by (apply Hparent_range; exact Hvertex_graph).
        assert (Hlow_same :
          Znth vertex (replace_Znth v w lowcost_in) 0 =
          Znth vertex lowcost_in 0).
        { rewrite Znth_replace_Znth_diff_local; auto. }
        assert (Hparent_same :
          Znth vertex (replace_Znth v de edge_parent_in) 0 =
          Znth vertex edge_parent_in 0).
        { rewrite Znth_replace_Znth_diff_local; auto. }
        split.
        -- apply (candidate_vertex_by_unchanged g s_next
             (add_scanned_edge_for_vertex g s_next to_new edge_for_vertex de)
             (replace_Znth v w lowcost_in) lowcost_in
             (replace_Znth v de edge_parent_in) edge_parent_in inf vertex);
             try exact Hlow_same; try exact Hparent_same.
           apply (candidate_vertex_by_add_other_vertex_forw
             g s_next to_new edge_for_vertex de
             lowcost_in edge_parent_in inf vertex);
             auto.
        -- rewrite Hkey_old.
           symmetry.
           exact Hlow_same.
    + intros vertex Hcand.
      destruct (Z.eq_dec vertex v) as [Hvertex_eq | Hvertex_neq].
      * subst vertex.
        rewrite Znth_replace_Znth_same_local by exact Hv_range.
        apply partial_map_update_or_add_present_same.
      * assert (Hvertex_graph : In vertex (graph_vertices g)).
        { unfold candidate_vertex_by in Hcand. tauto. }
        assert (Hvertex_low_range : 0 <= vertex < Zlength lowcost_in)
          by (apply Hlow_range; exact Hvertex_graph).
        assert (Hvertex_parent_range : 0 <= vertex < Zlength edge_parent_in)
          by (apply Hparent_range; exact Hvertex_graph).
        assert (Hlow_same :
          Znth vertex (replace_Znth v w lowcost_in) 0 =
          Znth vertex lowcost_in 0).
        { rewrite Znth_replace_Znth_diff_local; auto. }
        assert (Hparent_same :
          Znth vertex (replace_Znth v de edge_parent_in) 0 =
          Znth vertex edge_parent_in 0).
        { rewrite Znth_replace_Znth_diff_local; auto. }
        eapply partial_map_update_or_add_present_other_rewrite.
        { unfold v in Hvertex_neq. exact Hvertex_neq. }
        destruct Hmap_match as [_ Hmap_candidate].
        { apply Hmap_candidate.
          apply (candidate_vertex_by_unchanged g s_next
          edge_for_vertex lowcost_in (replace_Znth v w lowcost_in)
          edge_parent_in (replace_Znth v de edge_parent_in) inf vertex).
          - symmetry. exact Hlow_same.
          - symmetry. exact Hparent_same.
          - apply (candidate_vertex_by_add_other_vertex
               g s_next to_new edge_for_vertex de
               (replace_Znth v w lowcost_in)
               (replace_Znth v de edge_parent_in) inf vertex); auto. }
        { unfold v in Hlow_same. exact Hlow_same. }
  - exfalso.
    destruct Hno_map as [Hnot_cut | Hle]; [contradiction | lia].
  - exfalso.
    destruct Hno_update as [Hnot_cut | Hle]; [contradiction | lia].
  - subst lowcost_out edge_parent_out M_out.
    split.
    + intros vertex key Hpresent.
      destruct Hmap_match as [Hmap_present _].
      destruct (Hmap_present vertex key Hpresent) as [Hcand_old Hkey_old].
      split; [| exact Hkey_old].
      destruct (Z.eq_dec vertex v) as [Hvertex_eq | Hvertex_neq].
      * subst vertex.
        apply (candidate_vertex_by_add_non_better_forw
          g s_next to_new wt_new edge_for_vertex de
          lowcost_in edge_parent_in inf v); auto.
      * apply (candidate_vertex_by_add_other_vertex_forw
          g s_next to_new edge_for_vertex de
          lowcost_in edge_parent_in inf vertex); auto.
    + intros vertex Hcand.
      destruct Hmap_match as [_ Hmap_candidate].
      destruct (Z.eq_dec vertex v) as [Hvertex_eq | Hvertex_neq].
      * subst vertex.
        apply Hmap_candidate.
        apply (candidate_vertex_by_add_non_better
          g s_next to_new wt_new edge_for_vertex de
          lowcost_in edge_parent_in inf v); auto.
      * apply Hmap_candidate.
        apply (candidate_vertex_by_add_other_vertex
          g s_next to_new edge_for_vertex de
          lowcost_in edge_parent_in inf vertex); auto.
Qed.

Lemma scan_minIndex_adjacency_map_prefix_start :
  forall g s_next from_new first link to_new wt_new minIndex
         lowcost edge_parent M edge_for_base,
    first_link_matches_vertex_directed_edges g from_new first link ->
    In minIndex (graph_vertices g) ->
    lowcost_parent_match_by
      g (fun v => ~ vvalid s_next.(Prim.graph_in_state) v)
      edge_for_base lowcost edge_parent 1000000000 ->
    prim_heap_map_matches_state_by
      g s_next edge_for_base lowcost edge_parent 1000000000 M ->
    (forall v e,
      ~ vvalid s_next.(Prim.graph_in_state) v ->
      add_vertex_directed_edges_for_vertex
        g s_next from_new to_new minIndex edge_for_base v e <->
      is_cut_edge_to_vertex g s_next v e) ->
    scan_minIndex_adjacency_map_prefix_update
      g s_next from_new first link to_new wt_new minIndex
      (Znth minIndex first 0)
      lowcost edge_parent M
      lowcost edge_parent M.
Proof.
  intros g s_next from_new first link to_new wt_new minIndex
         lowcost edge_parent M edge_for_base
         Hfirst Hmin_graph Hlow Hmap Hcut.
  unfold scan_minIndex_adjacency_map_prefix_update.
  destruct (Hfirst minIndex Hmin_graph) as [cl [Hchain Hperm]].
  exists edge_for_base, nil, cl.
  simpl.
  split; [exact Hchain |].
  split; [exact Hchain |].
  split; [exact Hperm |].
  split; [constructor |].
  split; [exact Hlow |].
  split; [exact Hmap |].
  exact Hcut.
Qed.

Lemma scan_minIndex_adjacency_map_prefix_step :
  forall n m from to wt g s_next from_new first link to_new wt_new
         minIndex current_e
         lowcost_before edge_parent_before M_before
         lowcost_current edge_parent_current M_current
         lowcost_next edge_parent_next M_next,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    (forall e, 0 <= e < m -> Znth e wt 0 < 1000000000) ->
    directed_array_graph g from_new to_new wt_new ->
    current_e <> -1 ->
    scan_minIndex_adjacency_map_prefix_update
      g s_next from_new first link to_new wt_new minIndex current_e
      lowcost_before edge_parent_before M_before
      lowcost_current edge_parent_current M_current ->
    scan_one_directed_edge_update
      g s_next to_new wt_new
      lowcost_current edge_parent_current current_e
      lowcost_next edge_parent_next ->
    partial_map_update_one_directed_edge
      g s_next to_new wt_new lowcost_current current_e M_current M_next ->
    scan_minIndex_adjacency_map_prefix_update
      g s_next from_new first link to_new wt_new minIndex
      (Znth current_e link 0)
      lowcost_before edge_parent_before M_before
      lowcost_next edge_parent_next M_next.
Proof.
  intros n m from to wt g s_next from_new first link to_new wt_new
         minIndex current_e
         lowcost_before edge_parent_before M_before
         lowcost_current edge_parent_current M_current
         lowcost_next edge_parent_next M_next
         Hgraph Hfrom Hto Hwt Hdir Hcur_ne Hprefix Hone Hmapone.
  unfold scan_minIndex_adjacency_map_prefix_update in *.
  destruct Hprefix as
    [edge_for_base [scanned_edges [remaining_edges
      [Hchain [Hlink [Hperm [Hscan [Hlow [Hmap Hcut]]]]]]]]].
  inversion Hlink as [| current_e' rest Hcur_cons Hlink_next Heq_current];
    subst remaining_edges.
  { exfalso. apply Hcur_ne. symmetry; assumption. }
  assert (Hcurrent_in :
    In current_e (vertex_directed_edges g from_new minIndex)).
  {
    eapply Permutation_in; [exact Hperm |].
    rewrite in_app_iff.
    right. simpl. auto.
  }
  assert (Htarget_graph :
    In (Znth current_e to_new 0) (graph_vertices g)).
  { eapply vertex_directed_edges_to_graph_vertex; eauto. }
  assert (Hde_range :
    0 <= current_e < 2 * graph_edge_count g).
  { eapply vertex_directed_edges_range; eauto. }
  assert (Hwt_inf :
    Znth current_e wt_new 0 < 1000000000).
  { eapply vertex_directed_edges_weight_lt; eauto. }
  assert (Hweight :
    weight g (current_e / 2) = Some (Znth current_e wt_new 0)).
  { eapply directed_array_graph_weight; eauto. }
  pose proof Hlow as Hlow_for_range.
  destruct Hlow_for_range as [Hrange _].
  assert (Hlow_range :
    forall v, In v (graph_vertices g) -> 0 <= v < Zlength lowcost_current).
  { intros v Hv. apply Hrange; exact Hv. }
  assert (Hparent_range :
    forall v, In v (graph_vertices g) -> 0 <= v < Zlength edge_parent_current).
  { intros v Hv. apply Hrange; exact Hv. }
  assert (Hlow_next_raw :
    lowcost_parent_match_by
      g (fun v => ~ vvalid s_next.(Prim.graph_in_state) v)
      (add_scanned_edge_for_vertex g s_next to_new
        (add_scanned_edges_for_vertex g s_next to_new edge_for_base scanned_edges)
        current_e)
      lowcost_next edge_parent_next 1000000000).
  {
    eapply scan_one_directed_edge_update_lowcost_parent_match_by; eauto.
  }
  assert (Hmap_next_raw :
    prim_heap_map_matches_state_by
      g s_next
      (add_scanned_edge_for_vertex g s_next to_new
        (add_scanned_edges_for_vertex g s_next to_new edge_for_base scanned_edges)
        current_e)
      lowcost_next edge_parent_next 1000000000 M_next).
  {
    eapply (prim_heap_map_matches_state_by_one_directed_edge
      g s_next to_new wt_new
      (add_scanned_edges_for_vertex
        g s_next to_new edge_for_base scanned_edges)
      current_e lowcost_current edge_parent_current M_current
      lowcost_next edge_parent_next M_next 1000000000);
      eauto.
  }
  exists edge_for_base, (scanned_edges ++ current_e :: nil), rest.
  split.
  { rewrite <- app_assoc. simpl. exact Hchain. }
  split.
  { exact Hlink_next. }
  split.
  { rewrite <- app_assoc. simpl. exact Hperm. }
  split.
  { eapply scan_directed_edges_partial_map_update_snoc; eauto. }
  split.
  { eapply lowcost_parent_match_by_iff.
    { exact Hlow_next_raw. }
    { intros vertex Hv Helig; exact Helig. }
    { intros vertex edge Hv Helig.
      exact (iff_sym
        (add_scanned_edges_for_vertex_snoc_iff
          g s_next to_new edge_for_base scanned_edges current_e vertex edge)). } }
  split.
  { eapply prim_heap_map_matches_state_by_iff.
    { exact Hmap_next_raw. }
    { intros vertex edge Helig.
      exact (iff_sym
        (add_scanned_edges_for_vertex_snoc_iff
          g s_next to_new edge_for_base scanned_edges current_e vertex edge)). } }
  exact Hcut.
Qed.

Lemma scan_minIndex_adjacency_map_prefix_finish :
  forall g s_next from_new first link to_new wt_new minIndex
         lowcost_before edge_parent_before M_before
         lowcost_after edge_parent_after M_after,
    scan_minIndex_adjacency_map_prefix_update
      g s_next from_new first link to_new wt_new minIndex (-1)
      lowcost_before edge_parent_before M_before
      lowcost_after edge_parent_after M_after ->
    scan_minIndex_adjacency_map_update
      g s_next from_new first link to_new wt_new minIndex
      lowcost_before edge_parent_before M_before
      lowcost_after edge_parent_after M_after.
Proof.
  intros g s_next from_new first link to_new wt_new minIndex
         lowcost_before edge_parent_before M_before
         lowcost_after edge_parent_after M_after Hprefix.
  unfold scan_minIndex_adjacency_map_prefix_update in Hprefix.
  destruct Hprefix as
    [edge_for_base [scanned_edges [remaining_edges
      [Hchain [Hlink [Hperm [Hscan [Hlow [Hmap Hcut]]]]]]]]].
  pose proof (is_link_chain_minus1_inv link remaining_edges Hlink) as Hnil.
  subst remaining_edges.
  unfold scan_minIndex_adjacency_map_update.
  split.
  - unfold scan_minIndex_adjacency_update.
    exists scanned_edges.
    rewrite app_nil_r in Hchain, Hperm.
    repeat split; auto.
    eapply scan_directed_edges_partial_map_update_to_scan; eauto.
  - rewrite app_nil_r in Hperm.
    eapply prim_heap_map_matches_state_by_to_state.
    + eapply prim_heap_map_matches_state_by_iff.
      * exact Hmap.
      * intros v e Hnot_valid.
        transitivity
          (add_vertex_directed_edges_for_vertex
            g s_next from_new to_new minIndex edge_for_base v e).
        -- apply add_scanned_edges_for_vertex_perm. exact Hperm.
        -- apply Hcut. exact Hnot_valid.
    + intros v e Hv_graph Hnot_valid.
      reflexivity.
Qed.

Lemma scan_minIndex_adjacency_map_prefix_finish_lowcost_parent :
  forall g s_next from_new first link to_new wt_new minIndex
         lowcost_before edge_parent_before M_before
         lowcost_after edge_parent_after M_after,
    scan_minIndex_adjacency_map_prefix_update
      g s_next from_new first link to_new wt_new minIndex (-1)
      lowcost_before edge_parent_before M_before
      lowcost_after edge_parent_after M_after ->
    lowcost_parent_match g s_next lowcost_after edge_parent_after 1000000000.
Proof.
  intros g s_next from_new first link to_new wt_new minIndex
         lowcost_before edge_parent_before M_before
         lowcost_after edge_parent_after M_after Hprefix.
  unfold scan_minIndex_adjacency_map_prefix_update in Hprefix.
  destruct Hprefix as
    [edge_for_base [scanned_edges [remaining_edges
      [Hchain [Hlink [Hperm [Hscan [Hlow [Hmap Hcut]]]]]]]]].
  pose proof (is_link_chain_minus1_inv link remaining_edges Hlink) as Hnil.
  subst remaining_edges.
  rewrite app_nil_r in Hperm.
  apply lowcost_parent_match_by_to.
  eapply lowcost_parent_match_by_iff.
  - exact Hlow.
  - intros v Hv Helig; exact Helig.
  - intros v e Hv Helig.
    transitivity
      (add_vertex_directed_edges_for_vertex
        g s_next from_new to_new minIndex edge_for_base v e).
    + apply add_scanned_edges_for_vertex_perm. exact Hperm.
    + apply Hcut. exact Helig.
Qed.

Lemma prim_heap_scan_state_update_or_add_pre :
  forall g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current current_e minIndex minCost
         M_before lowcost_out edge_parent_out M_current X
         data key,
    prim_heap_scan_state
      g src chosen s_before s_after
      from_new first link to_new wt_new
      lowcost_before visited_after edge_parent_before
      lowcost_current edge_parent_current current_e minIndex minCost
      M_before lowcost_out edge_parent_out M_current X ->
    data = Znth current_e to_new 0 ->
    key = Znth current_e wt_new 0 ->
    key < Znth data lowcost_current 0 ->
    partial_map_update_or_add_pre M_current data key.
Proof.
  intros g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current current_e minIndex minCost
         M_before lowcost_out edge_parent_out M_current X
         data key Hscan Hdata Hkey Hlt.
  subst data key.
  unfold prim_heap_scan_state in Hscan.
  destruct Hscan as
    [_ [_ [_ [_ [_ [Hprefix [_ [_ _]]]]]]]].
  unfold scan_minIndex_adjacency_map_prefix_update in Hprefix.
  destruct Hprefix as
    [edge_for_base [scanned_edges [remaining_edges
      [_ [_ [_ [_ [_ [Hmap _]]]]]]]]].
  apply partial_map_update_or_add_pre_from_key_le.
  intros old_key Hpresent.
  destruct Hmap as [Hpresent_map _].
  destruct (Hpresent_map (Znth current_e to_new 0) old_key Hpresent)
    as [_ Hkey_old].
  lia.
Qed.

Lemma prim_heap_scan_state_current_edge_in :
  forall g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current current_e minIndex minCost
         M_before lowcost_out edge_parent_out M_current X,
    current_e <> -1 ->
    prim_heap_scan_state
      g src chosen s_before s_after
      from_new first link to_new wt_new
      lowcost_before visited_after edge_parent_before
      lowcost_current edge_parent_current current_e minIndex minCost
      M_before lowcost_out edge_parent_out M_current X ->
    In current_e (vertex_directed_edges g from_new minIndex).
Proof.
  intros g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current current_e minIndex minCost
         M_before lowcost_out edge_parent_out M_current X
         Hcur_ne Hstate.
  unfold prim_heap_scan_state in Hstate.
  destruct Hstate as
    [_ [_ [_ [_ [_ [Hprefix [_ [_ _]]]]]]]].
  unfold scan_minIndex_adjacency_map_prefix_update in Hprefix.
  destruct Hprefix as
    [edge_for_base [scanned_edges [remaining_edges
      [_ [Hlink [Hperm _]]]]]].
  inversion Hlink; subst remaining_edges.
  - subst current_e. contradiction Hcur_ne. reflexivity.
  - eapply Permutation_in; [exact Hperm |].
    rewrite in_app_iff.
    right. simpl. auto.
Qed.

Lemma prim_heap_scan_state_current_edge_range :
  forall g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current current_e minIndex minCost
         M_before lowcost_out edge_parent_out M_current X,
    current_e <> -1 ->
    prim_heap_scan_state
      g src chosen s_before s_after
      from_new first link to_new wt_new
      lowcost_before visited_after edge_parent_before
      lowcost_current edge_parent_current current_e minIndex minCost
      M_before lowcost_out edge_parent_out M_current X ->
    0 <= current_e < 2 * graph_edge_count g.
Proof.
  intros.
  eapply vertex_directed_edges_range.
  eapply prim_heap_scan_state_current_edge_in; eauto.
Qed.

Lemma prim_heap_scan_state_current_edge_to_range :
  forall n m from to wt g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current current_e minIndex minCost
         M_before lowcost_out edge_parent_out M_current X,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    directed_array_graph g from_new to_new wt_new ->
    current_e <> -1 ->
    prim_heap_scan_state
      g src chosen s_before s_after
      from_new first link to_new wt_new
      lowcost_before visited_after edge_parent_before
      lowcost_current edge_parent_current current_e minIndex minCost
      M_before lowcost_out edge_parent_out M_current X ->
    0 <= Znth current_e to_new 0 < n.
Proof.
  intros n m from to wt g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current current_e minIndex minCost
         M_before lowcost_out edge_parent_out M_current X
         Hgraph Hfrom Hto Hdir Hcur_ne Hstate.
  pose proof (array_graph_edge_count n m from to wt g Hgraph) as Hcount.
  pose proof (prim_heap_scan_state_current_edge_range
    g src chosen s_before s_after from_new first link to_new wt_new
    lowcost_before visited_after edge_parent_before
    lowcost_current edge_parent_current current_e minIndex minCost
    M_before lowcost_out edge_parent_out M_current X Hcur_ne Hstate)
    as Hrange_g.
  eapply directed_array_graph_to_range; eauto.
  lia.
Qed.

Lemma prim_heap_scan_state_visited_valid :
  forall g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current current_e minIndex minCost
         M_before lowcost_out edge_parent_out M_current X v,
    prim_heap_scan_state
      g src chosen s_before s_after
      from_new first link to_new wt_new
      lowcost_before visited_after edge_parent_before
      lowcost_current edge_parent_current current_e minIndex minCost
      M_before lowcost_out edge_parent_out M_current X ->
    In v (graph_vertices g) ->
    Znth v visited_after 0 <> 0 ->
    vvalid s_after.(Prim.graph_in_state) v.
Proof.
  intros g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current current_e minIndex minCost
         M_before lowcost_out edge_parent_out M_current X v
         Hstate Hv Hvisited.
  unfold prim_heap_scan_state in Hstate.
  destruct Hstate as [_ [_ [Hvisited_match _]]].
  destruct (Hvisited_match v Hv) as [Hnz_to_valid _].
  exact (Hnz_to_valid Hvisited).
Qed.

Lemma prim_heap_scan_state_current_edge_not_cut_when_visited :
  forall n m from to wt g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current current_e minIndex minCost
         M_before lowcost_out edge_parent_out M_current X,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    directed_array_graph g from_new to_new wt_new ->
    current_e <> -1 ->
    Znth (Znth current_e to_new 0) visited_after 0 <> 0 ->
    prim_heap_scan_state
      g src chosen s_before s_after
      from_new first link to_new wt_new
      lowcost_before visited_after edge_parent_before
      lowcost_current edge_parent_current current_e minIndex minCost
      M_before lowcost_out edge_parent_out M_current X ->
    ~ is_cut_edge_to_vertex g s_after (Znth current_e to_new 0)
        (current_e / 2).
Proof.
  intros n m from to wt g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current current_e minIndex minCost
         M_before lowcost_out edge_parent_out M_current X
         Hgraph Hfrom Hto Hdir Hcur_ne Hvisited_nonzero Hstate.
  pose proof (prim_heap_scan_state_current_edge_in
    g src chosen s_before s_after from_new first link to_new wt_new
    lowcost_before visited_after edge_parent_before
    lowcost_current edge_parent_current current_e minIndex minCost
    M_before lowcost_out edge_parent_out M_current X Hcur_ne Hstate)
    as Hin.
  assert (Htarget_graph :
    In (Znth current_e to_new 0) (graph_vertices g)).
  { eapply vertex_directed_edges_to_graph_vertex; eauto. }
  unfold prim_heap_scan_state in Hstate.
  destruct Hstate as [_ [_ [Hvisited_match _]]].
  eapply visited_nonzero_not_cut_edge_to_vertex; eauto.
Qed.

Lemma prim_heap_scan_state_current_edge_update :
  forall n m from to wt g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current current_e minIndex minCost
         M_before M_current X,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    directed_array_graph g from_new to_new wt_new ->
    PrimEnv g src ->
    current_e <> -1 ->
    vvalid s_after.(Prim.graph_in_state) minIndex ->
    Znth current_e wt_new 0 <
      Znth (Znth current_e to_new 0) lowcost_current 0 ->
    Znth (Znth current_e to_new 0) visited_after 0 = 0 ->
    prim_heap_scan_state
      g src chosen s_before s_after
      from_new first link to_new wt_new
      lowcost_before visited_after edge_parent_before
      lowcost_current edge_parent_current current_e minIndex minCost
      M_before lowcost_current edge_parent_current M_current X ->
    scan_one_directed_edge_update
      g s_after to_new wt_new lowcost_current edge_parent_current current_e
      (replace_Znth (Znth current_e to_new 0)
        (Znth current_e wt_new 0) lowcost_current)
      (replace_Znth (Znth current_e to_new 0) current_e edge_parent_current) /\
    partial_map_update_one_directed_edge
      g s_after to_new wt_new lowcost_current current_e M_current
      (partial_map_update_or_add M_current
        (Znth current_e to_new 0) (Znth current_e wt_new 0)).
Proof.
  intros n m from to wt g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current current_e minIndex minCost
         M_before M_current X
         Hgraph Hfrom Hto Hdir Henv Hcur_ne Hmin_valid Hbetter
         Hto_unvisited Hstate.
  pose proof (array_graph_edge_count n m from to wt g Hgraph)
    as Hedge_count_eq.
  pose proof (prim_heap_scan_state_current_edge_in
    g src chosen s_before s_after from_new first link to_new wt_new
    lowcost_before visited_after edge_parent_before
    lowcost_current edge_parent_current current_e minIndex minCost
    M_before lowcost_current edge_parent_current M_current X
    Hcur_ne Hstate) as Hcurrent_in.
  assert (Hde_range : 0 <= current_e < 2 * graph_edge_count g).
  { eapply vertex_directed_edges_range; eauto. }
  assert (Htarget_graph :
    In (Znth current_e to_new 0) (graph_vertices g)).
  { eapply vertex_directed_edges_to_graph_vertex; eauto. }
  assert (Hedge_valid : edge_valid g (current_e / 2)).
  {
    unfold edge_valid.
    unfold array_graph in Hgraph.
    destruct Hgraph as [_ [Hedges _]].
    rewrite Hedges.
    rewrite <- In_Zrange.
    rewrite <- Hedge_count_eq.
    eapply directed_edge_div2_bound; eauto.
  }
  assert (Hfrom_valid :
    vvalid s_after.(Prim.graph_in_state) (Znth current_e from_new 0)).
  {
    apply vertex_directed_edges_In in Hcurrent_in as [_ Hfrom_eq].
    rewrite Hfrom_eq.
    exact Hmin_valid.
  }
  assert (Hto_not_valid :
    ~ vvalid s_after.(Prim.graph_in_state) (Znth current_e to_new 0)).
  {
    intro Hto_valid.
    unfold prim_heap_scan_state in Hstate.
    destruct Hstate as [_ [_ [Hvisited _]]].
    destruct (Hvisited (Znth current_e to_new 0) Htarget_graph)
      as [_ Hvalid_to_nonzero].
    specialize (Hvalid_to_nonzero Hto_valid).
    congruence.
  }
  assert (Hcut :
    is_cut_edge_to_vertex
      g s_after (Znth current_e to_new 0) (current_e / 2)).
  {
    exact (directed_edge_is_cut_edge_to_vertex
      g s_after from_new to_new wt_new current_e
      Hdir (prim_graph_valid g src Henv) Hde_range Hedge_valid
      Hfrom_valid Hto_not_valid).
  }
  split.
  - unfold scan_one_directed_edge_update.
    left.
    split; [exact Hcut |].
    split; [exact Hbetter |].
    split; reflexivity.
  - unfold partial_map_update_one_directed_edge.
    left.
    split; [exact Hcut |].
    split; [exact Hbetter | reflexivity].
Qed.

Lemma prim_heap_scan_state_step_update :
  forall n m from to wt g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current current_e minIndex minCost
         M_before M_current lowcost_next edge_parent_next M_next X,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    (forall e, 0 <= e < m -> Znth e wt 0 < 1000000000) ->
    directed_array_graph g from_new to_new wt_new ->
    current_e <> -1 ->
    prim_heap_scan_state
      g src chosen s_before s_after
      from_new first link to_new wt_new
      lowcost_before visited_after edge_parent_before
      lowcost_current edge_parent_current current_e minIndex minCost
      M_before lowcost_current edge_parent_current M_current X ->
    scan_one_directed_edge_update
      g s_after to_new wt_new
      lowcost_current edge_parent_current current_e
      lowcost_next edge_parent_next ->
    partial_map_update_one_directed_edge
      g s_after to_new wt_new lowcost_current current_e M_current M_next ->
    prim_heap_scan_state
      g src chosen s_before s_after
      from_new first link to_new wt_new
      lowcost_before visited_after edge_parent_before
      lowcost_next edge_parent_next (Znth current_e link 0) minIndex minCost
      M_before lowcost_next edge_parent_next M_next X.
Proof.
  intros n m from to wt g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current current_e minIndex minCost
         M_before M_current lowcost_next edge_parent_next M_next X
         Hgraph Hfrom Hto Hwt Hdir Hcur_ne Hstate Hone Hmapone.
  unfold prim_heap_scan_state in *.
  destruct Hstate as [Hchosen Hstate].
  destruct Hstate as [Hgrow Hstate].
  destruct Hstate as [Hvisited Hstate].
  destruct Hstate as [Hcount Hstate].
  destruct Hstate as [Hselected Hstate].
  destruct Hstate as [Hprefix Hstate].
  destruct Hstate as [Hlow_out [Hedge_out Hsafe]].
  split; [exact Hchosen |].
  split; [exact Hgrow |].
  split; [exact Hvisited |].
  split; [exact Hcount |].
  split; [exact Hselected |].
  split.
  - eapply scan_minIndex_adjacency_map_prefix_step; eauto.
  - split; [reflexivity |].
    split; [reflexivity | exact Hsafe].
Qed.

Lemma prim_heap_scan_state_step_no_update :
  forall n m from to wt g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current current_e minIndex minCost
         M_before M_current X,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    (forall e, 0 <= e < m -> Znth e wt 0 < 1000000000) ->
    directed_array_graph g from_new to_new wt_new ->
    current_e <> -1 ->
    prim_heap_scan_state
      g src chosen s_before s_after
      from_new first link to_new wt_new
      lowcost_before visited_after edge_parent_before
      lowcost_current edge_parent_current current_e minIndex minCost
      M_before lowcost_current edge_parent_current M_current X ->
    (~ is_cut_edge_to_vertex g s_after (Znth current_e to_new 0)
       (current_e / 2) \/
     Znth (Znth current_e to_new 0) lowcost_current 0 <=
       Znth current_e wt_new 0) ->
    prim_heap_scan_state
      g src chosen s_before s_after
      from_new first link to_new wt_new
      lowcost_before visited_after edge_parent_before
      lowcost_current edge_parent_current (Znth current_e link 0)
      minIndex minCost
      M_before lowcost_current edge_parent_current M_current X.
Proof.
  intros n m from to wt g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current current_e minIndex minCost
         M_before M_current X
         Hgraph Hfrom Hto Hwt Hdir Hcur_ne Hstate Hno_update.
  eapply prim_heap_scan_state_step_update; eauto.
  - unfold scan_one_directed_edge_update.
    right.
    split; [exact Hno_update |].
    split; reflexivity.
  - unfold partial_map_update_one_directed_edge.
    right.
    split; [exact Hno_update | reflexivity].
Qed.

Lemma heap_representation_present_size_positive :
  forall M key_values data_values pos_values data_bound size data key,
    heap_representation M key_values data_values pos_values data_bound size ->
    partial_map_present M data key ->
    size > 0.
Proof.
  intros M key_values data_values pos_values data_bound size data key
         Hrepr Hpresent.
  unfold heap_representation in Hrepr.
  destruct Hrepr as [_ [_ [Hrel _]]].
  unfold heap_map_relation in Hrel.
  destruct Hrel as [_ [_ [_ [_ Hback]]]].
  destruct (Hback data key Hpresent) as [idx [Hidx _]].
  lia.
Qed.

Lemma heap_data_unique_NoDup :
  forall data_values size,
    Zlength data_values = size ->
    heap_data_unique data_values size ->
    NoDup data_values.
Proof.
  intros data_values size Hlen Hunique.
  apply (proj2 (@NoDup_nth Z data_values 0)).
  intros i j Hi Hj Heq.
  apply Nat2Z.inj.
  apply Hunique.
  - rewrite <- Hlen, Zlength_correct. lia.
  - rewrite <- Hlen, Zlength_correct. lia.
  - unfold Znth.
    rewrite !Nat2Z.id.
    exact Heq.
Qed.

Lemma heap_representation_size_le_data_bound :
  forall M key_values data_values pos_values data_bound size,
    heap_representation M key_values data_values pos_values data_bound size ->
    size <= data_bound.
Proof.
  intros M key_values data_values pos_values data_bound size Hrepr.
  unfold heap_representation in Hrepr.
  destruct Hrepr as [Hsize_nonneg [_ [Hrel [_ Hpos]]]].
  unfold heap_map_relation in Hrel.
  destruct Hrel as [_ [Hdata_len [Hunique _]]].
  unfold heap_pos_consistent in Hpos.
  destruct Hpos as [Hdata_bound_nonneg [_ [Hdata_valid _]]].
  pose proof (heap_data_unique_NoDup data_values size Hdata_len Hunique)
    as Hnodup.
  assert (Hincl : incl data_values (Zrange 0 data_bound)).
  {
    intros x Hx.
    destruct (In_nth data_values x 0 Hx) as [i [Hi Hnth]].
    rewrite <- Hnth.
    rewrite <- In_Zrange.
    specialize (Hdata_valid (Z.of_nat i)).
    unfold Znth in Hdata_valid.
    rewrite Nat2Z.id in Hdata_valid.
    apply Hdata_valid.
    rewrite <- Hdata_len, Zlength_correct.
    lia.
  }
  pose proof (NoDup_incl_length Hnodup Hincl) as Hlen_le.
  assert (Hlen_le_Z :
    Z.of_nat (length data_values) <=
    Z.of_nat (length (Zrange 0 data_bound))).
  { apply Nat2Z.inj_le. exact Hlen_le. }
  assert (Hrange_len :
    Z.of_nat (length (Zrange 0 data_bound)) = data_bound).
  {
    rewrite <- Zlength_correct.
    rewrite Zlength_Zrange by lia.
    lia.
  }
  rewrite <- Zlength_correct in Hlen_le_Z.
  rewrite Hdata_len, Hrange_len in Hlen_le_Z.
  lia.
Qed.

Lemma store_heap_size_le_data_bound :
  forall key_ptr data_ptr pos_ptr data_bound capacity M size,
    store_heap key_ptr data_ptr pos_ptr data_bound capacity M size |--
      “ size <= data_bound ” &&
      store_heap key_ptr data_ptr pos_ptr data_bound capacity M size.
Proof.
  intros key_ptr data_ptr pos_ptr data_bound capacity M size.
  unfold store_heap at 1.
  Intros key_values data_values pos_values.
  assert (Hsize_bound : size <= data_bound).
  { eapply heap_representation_size_le_data_bound; eauto. }
  unfold store_heap.
  Exists key_values data_values pos_values.
  entailer!.
Qed.

Lemma store_heap_present_size_positive :
  forall key_ptr data_ptr pos_ptr data_bound capacity M size data key,
    partial_map_present M data key ->
    store_heap key_ptr data_ptr pos_ptr data_bound capacity M size |--
      “ size > 0 ” &&
      store_heap key_ptr data_ptr pos_ptr data_bound capacity M size.
Proof.
  intros key_ptr data_ptr pos_ptr data_bound capacity M size data key Hpresent.
  unfold store_heap at 1.
  Intros key_values data_values pos_values.
  assert (Hsize_pos : size > 0).
  { eapply heap_representation_present_size_positive; eauto. }
  unfold store_heap.
  Exists key_values data_values pos_values.
  entailer!.
Qed.

Lemma scan_one_directed_edge_preserves_selected_edges :
  forall n m from to wt g src s_next to_new wt_new
         lowcost_in edge_parent_in de lowcost_out edge_parent_out,
    array_graph n m from to wt g ->
    0 <= Znth de to_new 0 < n ->
    selected_edges_match_state g src s_next edge_parent_in ->
    scan_one_directed_edge_update
      g s_next to_new wt_new
      lowcost_in edge_parent_in de lowcost_out edge_parent_out ->
    selected_edges_match_state g src s_next edge_parent_out.
Proof.
  intros n m from to wt g src s_next to_new wt_new
         lowcost_in edge_parent_in de lowcost_out edge_parent_out
         Hgraph Hto_range Hselected Hscan.
  unfold scan_one_directed_edge_update in Hscan.
  destruct Hscan as
    [[Hcut [_ [_ Hparent_out]]] | [_ [_ Hparent_out]]];
    subst edge_parent_out; [| exact Hselected].
  unfold selected_edges_match_state, parent_edges_match_state in *.
  destruct Hselected as [Hsrc [Hrange Hexact]].
  destruct Hcut as [Hto_not_valid _].
  unfold Znth in Hto_range.
  split; [exact Hsrc |].
  split.
  - unfold parent_edges_range_state in *.
    intros x Hx_graph Hx_src Hx_valid.
    assert (Hx_range : 0 <= x < n).
    { eapply array_graph_vertex_range; eauto. }
    pose proof (Hrange x Hx_graph Hx_src Hx_valid) as Hrange_x.
    unfold Znth, replace_Znth.
    rewrite nth_replace_nth_diff_local.
    + exact Hrange_x.
    + intro Hnat_eq.
      apply Hto_not_valid.
      unfold Znth.
      assert (Hnth_eq : nth (Z.to_nat de) to_new 0 = x).
      { eapply Z2Nat.inj; try exact Hnat_eq; lia. }
      rewrite <- Hnth_eq in Hx_valid.
      exact Hx_valid.
  - unfold parent_edges_exact_state in *.
    intros e.
    specialize (Hexact e).
    split.
    + intros Hevalid.
      apply Hexact in Hevalid.
      destruct Hevalid as [x [Hx_graph [Hx_src [Hx_valid Heq]]]].
      exists x.
      repeat split; try assumption.
      assert (Hx_range : 0 <= x < n).
      { eapply array_graph_vertex_range; eauto. }
      unfold Znth, replace_Znth.
      rewrite nth_replace_nth_diff_local.
      exact Heq.
      intro Hnat_eq.
      apply Hto_not_valid.
      unfold Znth.
      assert (Hnth_eq : nth (Z.to_nat de) to_new 0 = x).
      { eapply Z2Nat.inj; try exact Hnat_eq; lia. }
      rewrite <- Hnth_eq in Hx_valid.
      exact Hx_valid.
    + intros Hnew.
      apply Hexact.
      destruct Hnew as [x [Hx_graph [Hx_src [Hx_valid Heq]]]].
      exists x.
      repeat split; try assumption.
      assert (Hx_range : 0 <= x < n).
      { eapply array_graph_vertex_range; eauto. }
      unfold Znth, replace_Znth in Heq.
      rewrite nth_replace_nth_diff_local in Heq.
      exact Heq.
      intro Hnat_eq.
      apply Hto_not_valid.
      unfold Znth.
      assert (Hnth_eq : nth (Z.to_nat de) to_new 0 = x).
      { eapply Z2Nat.inj; try exact Hnat_eq; lia. }
      rewrite <- Hnth_eq in Hx_valid.
      exact Hx_valid.
Qed.

Lemma scan_directed_edges_partial_map_preserves_selected_edges :
  forall n m from to wt g root minIndex s_next from_new to_new wt_new scanned_edges
         lowcost_before edge_parent_before M_before
         lowcost_after edge_parent_after M_after,
    array_graph n m from to wt g ->
    directed_array_graph g from_new to_new wt_new ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    (forall de, In de scanned_edges -> In de (vertex_directed_edges g from_new minIndex)) ->
    selected_edges_match_state g root s_next edge_parent_before ->
    scan_directed_edges_partial_map_update
      g s_next to_new wt_new scanned_edges
      lowcost_before edge_parent_before M_before
      lowcost_after edge_parent_after M_after ->
    selected_edges_match_state g root s_next edge_parent_after.
Proof.
  intros n m from to wt g root minIndex s_next from_new to_new wt_new scanned_edges
         lowcost_before edge_parent_before M_before
         lowcost_after edge_parent_after M_after
         Hgraph Hdir Hfrom_range Hto_range Hin Hselected Hscan.
  induction Hscan.
  - exact Hselected.
  - assert (Hde_in : In de (vertex_directed_edges g from_new minIndex)).
    { apply Hin. simpl. auto. }
    assert (Hde_range : 0 <= de < 2 * graph_edge_count g).
    { eapply vertex_directed_edges_range; eauto. }
    assert (Hto_new_range : 0 <= Znth de to_new 0 < n).
    {
      pose proof (array_graph_edge_count n m from to wt g Hgraph) as Hcount.
      eapply directed_array_graph_to_range; eauto.
      lia.
    }
    apply IHHscan.
    + intros de0 Hin_rest.
      apply Hin. simpl. auto.
    + eapply scan_one_directed_edge_preserves_selected_edges; eauto.
Qed.

Lemma scan_minIndex_adjacency_map_prefix_preserves_selected_edges :
  forall n m from to wt g root s_next from_new first link to_new wt_new
         minIndex current_e lowcost_before edge_parent_before M_before
         lowcost_current edge_parent_current M_current,
    array_graph n m from to wt g ->
    directed_array_graph g from_new to_new wt_new ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    selected_edges_match_state g root s_next edge_parent_before ->
    scan_minIndex_adjacency_map_prefix_update
      g s_next from_new first link to_new wt_new minIndex current_e
      lowcost_before edge_parent_before M_before
      lowcost_current edge_parent_current M_current ->
    selected_edges_match_state g root s_next edge_parent_current.
Proof.
  intros n m from to wt g root s_next from_new first link to_new wt_new
         minIndex current_e lowcost_before edge_parent_before M_before
         lowcost_current edge_parent_current M_current
         Hgraph Hdir Hfrom_range Hto_range Hselected Hprefix.
  unfold scan_minIndex_adjacency_map_prefix_update in Hprefix.
  destruct Hprefix as [edge_for_base [scanned_edges [remaining_edges
    [Hchain [Hlink [Hperm [Hscan _]]]]]]].
  eapply (scan_directed_edges_partial_map_preserves_selected_edges
    n m from to wt g root minIndex s_next from_new to_new wt_new scanned_edges
    lowcost_before edge_parent_before M_before
    lowcost_current edge_parent_current M_current).
  - exact Hgraph.
  - exact Hdir.
  - exact Hfrom_range.
  - exact Hto_range.
  - intros de Hde_scanned.
    eapply Permutation_in; [exact Hperm |].
    rewrite in_app_iff.
    left.
    exact Hde_scanned.
  - exact Hselected.
  - exact Hscan.
Qed.

Lemma prim_heap_scan_state_finish_loop :
  forall n m from to wt g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current minIndex minCost
         M_before M_current X,
    array_graph n m from to wt g ->
    directed_array_graph g from_new to_new wt_new ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    prim_heap_scan_state
      g src chosen s_before s_after
      from_new first link to_new wt_new
      lowcost_before visited_after edge_parent_before
      lowcost_current edge_parent_current (-1) minIndex minCost
      M_before lowcost_current edge_parent_current M_current X ->
    prim_heap_loop_state
      g src chosen s_after lowcost_current visited_after
      edge_parent_current M_current X.
Proof.
  intros n m from to wt g src chosen s_before s_after
         from_new first link to_new wt_new
         lowcost_before visited_after edge_parent_before
         lowcost_current edge_parent_current minIndex minCost
         M_before M_current X Hgraph Hdir Hfrom_range Hto_range Hscan.
  unfold prim_heap_scan_state in Hscan.
  destruct Hscan as
    [Hchosen [Hgrow [Hvisited [Hcount [Hselected
      [Hprefix [Hlow_out [Hedge_out Hsafe]]]]]]]].
  right.
  split; [exact Hchosen |].
  split; [exact Hgrow |].
  split; [exact Hvisited |].
  split; [exact Hcount |].
  split.
  - eapply scan_minIndex_adjacency_map_prefix_preserves_selected_edges.
    + exact Hgraph.
    + exact Hdir.
    + exact Hfrom_range.
    + exact Hto_range.
    + exact Hselected.
    + exact Hprefix.
  - split.
    + eapply scan_minIndex_adjacency_map_prefix_finish_lowcost_parent.
      exact Hprefix.
    + split.
      * eapply scan_minIndex_adjacency_map_prefix_finish.
        exact Hprefix.
      * exact Hsafe.
Qed.

Lemma prim_heap_loop_state_present_if_unfinished :
  forall n m from to wt g src chosen s lowcost visited edge_parent M X,
    array_graph n m from to wt g ->
    PrimEnv g src ->
    chosen < n ->
    prim_heap_loop_state g src chosen s lowcost visited edge_parent M X ->
    exists v key, partial_map_present M v key.
Proof.
  intros n m from to wt g src chosen s lowcost visited edge_parent M X
         Hgraph Henv Hlt Hloop.
  unfold prim_heap_loop_state in Hloop.
  destruct Hloop as
    [[Hchosen [_ [_ [_ [_ [HM _]]]]]]
    | [Hchosen [Hgrow [_ [Hcount [Hselected [Hlow [Hmap _]]]]]]]].
  - subst M.
    exists src, 0.
    apply partial_map_add_present_same.
  - assert (Hnonempty :
      exists x, vvalid s.(Prim.graph_in_state) x).
    {
      unfold selected_edges_match_state, parent_edges_match_state in Hselected.
      destruct Hselected as [Hsrc_valid _].
      exists src.
      exact Hsrc_valid.
    }
    pose proof (unfinished_connected_state_has_candidate_vertex_by_count
      n m from to wt g s lowcost edge_parent 1000000000
      Hgraph (prim_connected g src Henv) Hgrow Hnonempty ltac:(lia) Hlow)
      as [v [_ Hcand]].
    exists v, (Znth v lowcost 0).
    destruct Hmap as [_ Hpresent].
    exact (Hpresent v Hcand).
Qed.

Lemma prim_heap_loop_state_done :
  forall n m from to wt g src s lowcost visited edge_parent M X,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    1 <= n ->
    Zlength lowcost = n ->
    prim_heap_loop_state g src n s lowcost visited edge_parent M X ->
    prim_heap_done_state g src s lowcost visited edge_parent M X.
Proof.
  intros n m from to wt g src s lowcost visited edge_parent M X
         Hgraph Hfrom Hto Hn_pos Hlow_len Hloop.
  unfold prim_heap_loop_state in Hloop.
  destruct Hloop as
    [[Hchosen0 _]
    | [Hchosen [Hgrow [Hvisited [Hcount [Hselected [Hlow [Hmap Hsafe]]]]]]]].
  - lia.
  - unfold prim_heap_done_state.
    split; [exact Hgrow |].
    split; [exact Hvisited |].
    split; [lia |].
    split; [exact Hselected |].
    split; [exact Hlow |].
    split; [exact Hmap |].
    eapply (Prim2_loop_finish n m from to wt g n X s).
      * eapply array_graph_gvalid; eauto.
      * exact Hgraph.
      * lia.
      * lia.
      * exact Hsafe.
Qed.

Lemma reachable_nontrivial_first_step :
  forall g x y,
    reachable g x y ->
    x <> y ->
    exists e z, graph_step g e x z.
Proof.
  intros g x y Hreach Hneq.
  unfold reachable in Hreach.
  induction_1n Hreach.
  - contradiction.
  - destruct H as [e Hstep].
    exists e, x0.
    exact Hstep.
Qed.

Lemma graph_step_vertex_in_endpoint_list :
  forall g e x y,
    graph_step g e x y ->
    In x
      (flat_map (fun e => [edge_src g e; edge_dst g e])
        (graph_edges g)).
Proof.
  intros g e x y Hstep.
  unfold graph_step in Hstep.
  destruct Hstep as [Hedge [_ [[Hx _] | [Hx _]]]].
  - rewrite Hx.
    unfold edge_valid in Hedge.
    apply in_flat_map.
    exists e.
    split; [exact Hedge | simpl; auto].
  - rewrite Hx.
    unfold edge_valid in Hedge.
    apply in_flat_map.
    exists e.
    split; [exact Hedge | simpl; auto].
Qed.

Lemma endpoint_list_length :
  forall g,
    length
      (flat_map (fun e => [edge_src g e; edge_dst g e])
        (graph_edges g)) =
    (2 * length (graph_edges g))%nat.
Proof.
  intros g.
  induction (graph_edges g) as [| e es IH]; simpl; lia.
Qed.

Lemma connected_array_graph_vertex_in_endpoint_list :
  forall n m from to wt g v,
    array_graph n m from to wt g ->
    connected g ->
    2 <= n ->
    In v (graph_vertices g) ->
    In v
      (flat_map (fun e => [edge_src g e; edge_dst g e])
        (graph_edges g)).
Proof.
  intros n m from to wt g v Hgraph Hconnected Hn Hv.
  pose proof (array_graph_vertex_range n m from to wt g v Hgraph Hv)
    as Hv_range.
  destruct (Z.eq_dec v 0) as [Hv0 | Hv_nonzero].
  - assert (Hother : In 1 (graph_vertices g)).
    { eapply array_graph_vertex_in; eauto; lia. }
    pose proof (Hconnected v 1 Hv Hother) as Hreach.
    assert (Hneq : v <> 1) by lia.
    destruct (reachable_nontrivial_first_step g v 1 Hreach Hneq)
      as [e [z Hstep]].
    eapply graph_step_vertex_in_endpoint_list; eauto.
  - assert (Hother : In 0 (graph_vertices g)).
    { eapply array_graph_vertex_in; eauto; lia. }
    pose proof (Hconnected v 0 Hv Hother) as Hreach.
    assert (Hneq : v <> 0) by lia.
    destruct (reachable_nontrivial_first_step g v 0 Hreach Hneq)
      as [e [z Hstep]].
    eapply graph_step_vertex_in_endpoint_list; eauto.
Qed.

Lemma connected_array_graph_vertex_count_le_twice_edges :
  forall n m from to wt g,
    array_graph n m from to wt g ->
    connected g ->
    2 <= n ->
    n <= 2 * m.
Proof.
  intros n m from to wt g Hgraph Hconnected Hn.
  pose proof (array_graph_vertex_count n m from to wt g Hgraph)
    as Hvertex_count.
  pose proof (array_graph_edge_count n m from to wt g Hgraph)
    as Hedge_count.
  assert (Hnodup : NoDup (graph_vertices g)).
  {
    unfold array_graph in Hgraph.
    destruct Hgraph as [Hvertices _].
    rewrite Hvertices.
    apply NoDup_Zrange.
  }
  assert (Hincl :
    incl (graph_vertices g)
      (flat_map (fun e => [edge_src g e; edge_dst g e])
        (graph_edges g))).
  {
    intros v Hv.
    eapply connected_array_graph_vertex_in_endpoint_list; eauto.
  }
  pose proof (NoDup_incl_length Hnodup Hincl) as Hlen_le.
  assert (Hlen_le_Z :
    Z.of_nat (length (graph_vertices g)) <=
    Z.of_nat (length
      (flat_map (fun e => [edge_src g e; edge_dst g e])
        (graph_edges g)))).
  { apply Nat2Z.inj_le. exact Hlen_le. }
  assert (Hendpoint_len :
    Z.of_nat (length
      (flat_map (fun e => [edge_src g e; edge_dst g e])
        (graph_edges g))) =
    2 * graph_edge_count g).
  {
    rewrite endpoint_list_length.
    unfold graph_edge_count.
    rewrite Zlength_correct.
    lia.
  }
  rewrite <- Zlength_correct in Hlen_le_Z.
  rewrite Hvertex_count, Hendpoint_len, Hedge_count in Hlen_le_Z.
  lia.
Qed.

Lemma heap_matches_prim_state_perm__prim_outer_entry_b :
  forall g s lowcost edge_parent inf entries_before entries_after,
    Permutation entries_before entries_after ->
    heap_matches_prim_state
      g s lowcost edge_parent inf entries_before ->
    heap_matches_prim_state
      g s lowcost edge_parent inf entries_after.
Proof.
  intros g s lowcost edge_parent inf entries_before entries_after
    Hperm [Hcontains [Hcurrent [Hrespect Hnodup]]].
  split; [| split; [| split]].
  - intros vertex Hcandidate.
    destruct (Hcontains vertex Hcandidate) as [cost [Hin Hcost]].
    exists cost; split; [| exact Hcost].
    eapply Permutation_in; eauto.
  - intros cost vertex Hin Hcost.
    apply (Hcurrent cost vertex); [| exact Hcost].
    eapply Permutation_in; [symmetry; exact Hperm | exact Hin].
  - intros cost vertex Hin.
    apply (Hrespect cost vertex).
    eapply Permutation_in; [symmetry; exact Hperm | exact Hin].
  - eapply Permutation_NoDup; eauto.
Qed.
Lemma selected_edges_match_state_replace_outside__prim_edge_scan_a :
  forall n m from to wt g src s edge_parent visited v de,
    array_graph n m from to wt g ->
    Zlength edge_parent = n ->
    visited_matches_state g s visited ->
    In v (graph_vertices g) ->
    Znth v visited 0 = 0 ->
    selected_edges_match_state g src s edge_parent ->
    selected_edges_match_state g src s (replace_Znth v de edge_parent).
Proof.
  intros n m from to wt g src s edge_parent visited v de
         Hgraph Hparent_len Hvisited Hv_graph Hv_zero Hselected.
  assert (Hv_range : 0 <= v < Zlength edge_parent).
  {
    rewrite Hparent_len.
    eapply array_graph_vertex_range; eauto.
  }
  assert (Hv_out : ~ vvalid s.(Prim.graph_in_state) v).
  {
    intro Hv_valid.
    apply (proj2 (Hvisited v Hv_graph)) in Hv_valid.
    congruence.
  }
  destruct Hselected as [Hsrc [Hrange Hexact]].
  split; [exact Hsrc |].
  split.
  - intros x Hx_graph Hx_src Hx_valid.
    assert (Hx_range : 0 <= x < Zlength edge_parent).
    {
      rewrite Hparent_len.
      eapply array_graph_vertex_range; eauto.
    }
    rewrite Znth_replace_Znth_diff_local;
      [eapply Hrange; eauto | exact Hv_range | exact Hx_range |].
    intro Heq.
    apply Hv_out.
    subst x.
    exact Hx_valid.
  - intros e.
    specialize (Hexact e).
    split.
    + intros Hevalid.
      apply Hexact in Hevalid.
      destruct Hevalid as [x [Hx_graph [Hx_src [Hx_valid Heq]]]].
      exists x.
      repeat split; try assumption.
      assert (Hx_range : 0 <= x < Zlength edge_parent).
      {
        rewrite Hparent_len.
        eapply array_graph_vertex_range; eauto.
      }
      rewrite Znth_replace_Znth_diff_local;
        [exact Heq | exact Hv_range | exact Hx_range |].
      intro Hxv.
      apply Hv_out.
      subst x.
      exact Hx_valid.
    + intros Hnew.
      apply Hexact.
      destruct Hnew as [x [Hx_graph [Hx_src [Hx_valid Heq]]]].
      exists x.
      repeat split; try assumption.
      assert (Hx_range : 0 <= x < Zlength edge_parent).
      {
        rewrite Hparent_len.
        eapply array_graph_vertex_range; eauto.
      }
      rewrite Znth_replace_Znth_diff_local in Heq;
        [exact Heq | exact Hv_range | exact Hx_range |].
      intro Hxv.
      apply Hv_out.
      subst x.
      exact Hx_valid.
Qed.
Lemma array_graph_vertex_in_range__prim_scan_close :
  forall n m from to wt g v,
    array_graph n m from to wt g ->
    0 <= v < n ->
    In v (graph_vertices g).
Proof.
  intros n m from to wt g v Hgraph Hv.
  unfold array_graph in Hgraph.
  destruct Hgraph as [Hvertices _].
  rewrite Hvertices, <- In_Zrange.
  exact Hv.
Qed.
Lemma in_zrange_bounds__prim_scan_close :
  forall lo hi x, In x (Zrange lo hi) -> lo <= x < hi.
Proof.
  intros lo hi x Hin.
  rewrite In_Zrange.
  exact Hin.
Qed.
Lemma prim_result_graph_matches_array_prefix_snoc__prim_loop_close :
  forall n m from to wt g src s rg rf rt rw edge_parent
         from_new to_new wt_new idx v,
    array_graph n m from to wt g ->
    (forall e, 0 <= e < m -> 0 <= Znth e from 0 < n) ->
    (forall e, 0 <= e < m -> 0 <= Znth e to 0 < n) ->
    directed_array_graph g from_new to_new wt_new ->
    growing_subgraph_state g s ->
    state_vertex_count s = n ->
    selected_edges_match_state g src s edge_parent ->
    prim_state_graph_matches rg s ->
    prim_result_graph_matches_array_prefix
      n idx rf rt rw g rg edge_parent from_new to_new wt_new ->
    src = 0 ->
    idx = v - 1 ->
    1 <= v < n ->
    prim_result_graph_matches_array_prefix
      n (idx + 1)
      (rf ++ Znth (Znth v edge_parent 0) from_new 0 :: nil)
      (rt ++ Znth (Znth v edge_parent 0) to_new 0 :: nil)
      (rw ++ Znth (Znth v edge_parent 0) wt_new 0 :: nil)
      g rg edge_parent from_new to_new wt_new.
Proof.
  intros n m from to wt g src s rg rf rt rw edge_parent
         from_new to_new wt_new idx v Hgraph Hfrom Hto Hdirected
         Hgrow Hcount Hselected Hrg Hprefix Hsrc Hidx Hv.
  pose proof (array_graph_gvalid n m from to wt g Hgraph Hfrom Hto) as Hg.
  pose proof (array_graph_edge_count _ _ _ _ _ _ Hgraph) as Hedge_count.
  assert (Hv_graph : In v (graph_vertices g)).
  { eapply array_graph_vertex_in; eauto. lia. }
  assert (Hv_state : vvalid s.(Prim.graph_in_state) v).
  { eapply completed_growing_subgraph_vvalid; eauto. }
  destruct Hselected as [_ [Hparent_range Hparent_exact]].
  unfold selected_edges_range_state in Hparent_range.
  assert (Hde_range_g :
    0 <= Znth v edge_parent 0 < 2 * graph_edge_count g).
  { apply Hparent_range; auto. subst src. lia. }
  assert (Hde_range_m : 0 <= Znth v edge_parent 0 < 2 * m).
  { rewrite <- Hedge_count. exact Hde_range_g. }
  assert (Hedge_g : In (Znth v edge_parent 0 / 2) (graph_edges g)).
  { eapply array_graph_directed_edge_valid; eauto. }
  assert (Hstep_g :
    step_aux g (Znth v edge_parent 0 / 2)
      (Znth (Znth v edge_parent 0) from_new 0)
      (Znth (Znth v edge_parent 0) to_new 0)).
  { eapply directed_array_graph_step; eauto. }
  assert (Hweight :
    weight g (Znth v edge_parent 0 / 2) =
      Some (Znth (Znth v edge_parent 0) wt_new 0)).
  { eapply directed_array_graph_weight; eauto. }
  unfold prim_state_graph_matches in Hrg.
  subst rg.
  assert (Hedge_state :
    evalid s.(Prim.graph_in_state) (Znth v edge_parent 0 / 2)).
  { apply (proj2 (Hparent_exact (Znth v edge_parent 0 / 2))).
    exists v. repeat split; auto. subst src. lia. }
  assert (Hstep_state :
    step_aux s.(Prim.graph_in_state) (Znth v edge_parent 0 / 2)
      (Znth (Znth v edge_parent 0) from_new 0)
      (Znth (Znth v edge_parent 0) to_new 0)).
  { destruct Hgrow as [Hsvalid [_ Hsub]].
    destruct Hsub as [_ Hsub_step].
    destruct (no_empty_edge s.(Prim.graph_in_state)
      (Znth v edge_parent 0 / 2) Hsvalid Hedge_state)
      as [x [y Hstep_old]].
    pose proof (Hsub_step x y (Znth v edge_parent 0 / 2) Hstep_old)
      as Hstep_g_old.
    destruct (step_aux_unique_undirected g (Znth v edge_parent 0 / 2)
      (Znth (Znth v edge_parent 0) from_new 0)
      (Znth (Znth v edge_parent 0) to_new 0) x y
      Hg Hstep_g Hstep_g_old) as [[Hx Hy] | [Hx Hy]].
    - subst x. subst y. exact Hstep_old.
    - subst y. subst x. apply step_sym. exact Hstep_old. }
  unfold prim_result_graph_matches_array_prefix in *.
  destruct Hprefix as [Hidx_range [Hrf [Hrt [Hrw Hslots]]]].
  split; [lia|].
  split; [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia|].
  split; [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia|].
  split; [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia|].
  intros k Hk.
  apply In_Zrange in Hk.
  destruct (Z_lt_ge_dec k idx) as [Hk_old | Hk_new].
  - specialize (Hslots k ltac:(apply In_Zrange; lia)).
    repeat rewrite Znth_app_l_local by lia.
    exact Hslots.
  - assert (k = idx) by lia. subst k.
    replace (idx + 1) with v by lia.
    rewrite Znth_app_r_local by lia.
    rewrite Znth_app_r_local by lia.
    rewrite Znth_app_r_local by lia.
    rewrite Hrf, Hrt, Hrw.
    replace (idx - idx) with 0 by lia.
    simpl.
    split; [exact Hedge_state|].
    split; [exact Hstep_state|].
    split; [exact Hweight|].
    repeat split; reflexivity.
Qed.
