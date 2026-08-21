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
From SimpleC.EE.LLM_bench.Algorithms.DFS Require Import DFS_adjacency_list_goal.
From SimpleC.EE.LLM_bench.Algorithms.DFS Require Import DFS_adjacency_list_proof_auto.
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
Require Import SimpleC.EE.QCP_demos_LLM.sll_lib.
Require Import Algorithms.DFS.DFS.
Require Import SimpleC.EE.LLM_bench.Algorithms.DFS.DFS_adjacency_list_lib.
Import ZSimpleGraph.
Local Open Scope sac.

Lemma proof_of_dfs_adjacency_list_entail_wit_1 : dfs_adjacency_list_entail_wit_1.
Proof.
  unfold dfs_adjacency_list_entail_wit_1.
  left; intros.
  unfold DFSAdjacencyList.visited.
  Intros values.
  subst vertex_count_pre.
  Exists values.
  unfold ZSimpleGraph.vertex_valid in PreH4.
  entailer!.
Qed.

Lemma proof_of_dfs_adjacency_list_entail_wit_2 : dfs_adjacency_list_entail_wit_2.
Proof.
  unfold dfs_adjacency_list_entail_wit_2.
  left; intros.
  set (entered_set := fun v => visited_set_low_level_spec v \/ v = vertex_pre).
  assert (Hentered_values :
    ZSimpleGraph.visited_values g_low_level_spec
      (replace_Znth vertex_pre 1 values) entered_set).
  { unfold entered_set.
    apply visited_values_after_visit__execution_representation; assumption. }
  assert (Hextension :
    DFSAdjacencyList.visited_extension visited_set_low_level_spec entered_set).
  { unfold DFSAdjacencyList.visited_extension, entered_set.
    intros v Hv. left. exact Hv. }
  assert (Hsafe_loop :
    safeExec (eq entered_set)
      (DFSAdjacencyList.dfs_loop g_low_level_spec vertex_pre)
      X_low_level_spec).
  {
    pose proof PreH7 as Hsafe.
    unfold DFSAdjacencyList.dfs_program in Hsafe.
    eapply safeExec_proequiv in Hsafe.
    2: apply DFS_unfold.
    unfold DFS_f, visit in Hsafe.
    apply safeExec_update'_bind in Hsafe.
    unfold DFSAdjacencyList.dfs_loop,
      DFSAdjacencyList.dfs_program.
    eapply safeExec_conseq; [exact Hsafe |].
    intros s (s0 & -> & <-).
    unfold entered_set.
    apply functional_extensionality; intros v.
    apply propositional_extensionality.
    sets_unfold. split; intros [Hv | Heq]; auto;
      right; symmetry; exact Heq.
  }
  (* subst vertex_count_pre. *)
  Exists (replace_Znth vertex_pre 1 values) entered_set.
  unfold entered_set.
  entailer!.
Qed.

Lemma proof_of_dfs_adjacency_list_entail_wit_3 : dfs_adjacency_list_entail_wit_3.
Proof.
  unfold dfs_adjacency_list_entail_wit_3.
  left; intros.
  Exists entered_values entered_set
    (Znth vertex_pre rows_low_level_spec nil)
    (Znth vertex_pre node_addrs_low_level_spec nil)
    (Znth vertex_pre row_ptrs_low_level_spec 0).
  sep_apply (graph_rep_split__execution_representation
    adjacency_pre g_low_level_spec row_ptrs_low_level_spec
    node_addrs_low_level_spec rows_low_level_spec vertex_pre PreH4).
  entailer!.
Qed.

Lemma proof_of_dfs_adjacency_list_entail_wit_4 : dfs_adjacency_list_entail_wit_4.
Proof.
  unfold dfs_adjacency_list_entail_wit_4.
  left; intros.
  Exists split_values split_set
    (@nil Z) row_2 (@nil Z) row_node_addrs_2
    row_2 row_node_addrs_2 row_head.
  simpl DFSAdjacencyList.addressed_sllseg.
  unfold DFSAdjacencyList.all_visited.
  entailer!.
Qed.

Lemma proof_of_dfs_adjacency_list_entail_wit_5 : dfs_adjacency_list_entail_wit_5.
Proof.
  unfold dfs_adjacency_list_entail_wit_5.
  left; intros.
  prop_apply_p (graph_except_model__execution_representation
    adjacency_pre g_low_level_spec row_ptrs_low_level_spec
    node_addrs_low_level_spec rows_low_level_spec vertex_pre).
  Intros_p Hmodel.
  destruct todo_addrs as [|node rest_addrs];
    destruct todo as [|datum rest];
    simpl DFSAdjacencyList.addressed_sll.
  - Intros_p Hnull. exfalso. apply PreH1. tauto.
  - entailer!.
  - entailer!.
  - Intros next.
    destruct H as [Hcursor Hnode_nonnull].
    subst node.
    assert (Hedge :
      ZSimpleGraph.graph_step g_low_level_spec vertex_pre datum).
    { unfold DFSAdjacencyList.adjacency_lists_model in Hmodel.
      destruct Hmodel as [_ [_ [_ Hrows]]].
      apply (proj1 (Hrows vertex_pre datum PreH5)).
      rewrite <- PreH10, PreH12.
      apply in_or_app. right. simpl. auto. }
    destruct Hedge as [_ [Hdatum_valid _]].
    Exists next loop_values loop_set done_2 rest
      done_addrs_2 rest_addrs row_2 row_node_addrs_2
      row_head_2 datum.
    unfold ZSimpleGraph.vertex_valid in *.
    entailer!.
Qed.

Lemma proof_of_dfs_adjacency_list_entail_wit_6 : dfs_adjacency_list_entail_wit_6.
Proof.
  unfold dfs_adjacency_list_entail_wit_6.
  left; intros.
  sep_apply (IntArray.full_split_to_missing_i
    visited_pre datum vertex_count_pre cursor_values 0); try lia.
  Exists next_2 cursor_values cursor_set done_2 rest_2
    done_addrs_2 rest_addrs_2 row_2 row_node_addrs_2
    row_head_2.
  entailer!.
Qed.

Lemma proof_of_dfs_adjacency_list_entail_wit_7 : dfs_adjacency_list_entail_wit_7.
Proof.
  unfold dfs_adjacency_list_entail_wit_7.
  left; intros.
  subst vertex_count_pre.
  assert (Hnot_visited : ~ read_set neighbor).
  { unfold ZSimpleGraph.visited_values in PreH22.
    destruct PreH22 as [Hvalues_len [Hvalid_values Hvalue]].
    specialize (Hvalue neighbor PreH6) as [_ Hiff].
    intro Hvisited. apply Hiff in Hvisited. lia. }
  prop_apply_p (graph_except_model__execution_representation
    adjacency_pre g_low_level_spec row_ptrs_low_level_spec
    node_addrs_low_level_spec rows_low_level_spec vertex_pre).
  Intros_p Hmodel.
  assert (Hedge :
    ZSimpleGraph.graph_step g_low_level_spec vertex_pre neighbor).
  { unfold DFSAdjacencyList.adjacency_lists_model in Hmodel.
    destruct Hmodel as [_ [_ [_ Hrows]]].
    apply (proj1 (Hrows vertex_pre neighbor PreH5)).
    rewrite <- PreH14, PreH16.
    apply in_or_app. right. simpl. auto. }
  assert (Hsafe_call :
    safeExec (eq read_set)
      (bind (DFSAdjacencyList.dfs_program g_low_level_spec neighbor)
        (DFSAdjacencyList.dfs_continue g_low_level_spec vertex_pre))
      X_low_level_spec).
  { pose proof PreH21 as Hsafe.
    unfold DFSAdjacencyList.dfs_loop in Hsafe at 1.
    unfold_loop in Hsafe.
    prog_nf in Hsafe.
    safe_choice_l Hsafe.
    2:{ intros st Hst. subst st.
        exists neighbor. split.
        - unfold DFSAdjacencyList.dfs_step.
          apply ZSimpleGraph.step_iff. exact Hedge.
        - exact Hnot_visited. }
    prog_nf in Hsafe.
    apply (safeExec_get_bind neighbor) in Hsafe.
    2:{ intros st Hst. subst st. split.
        - unfold DFSAdjacencyList.dfs_step.
          apply ZSimpleGraph.step_iff. exact Hedge.
        - exact Hnot_visited. }
    exact Hsafe. }
  sep_apply (IntArray.missing_i_merge_to_full
    visited_pre neighbor (ZSimpleGraph.vertex_count g_low_level_spec)
    (Znth neighbor read_values 0) read_values); try lia.
  rewrite replace_Znth_Znth by lia.
  assert (Hnode :
    (&(edge_value # "list" ->ₛ "data") # Int |-> neighbor) **
    (&(edge_value # "list" ->ₛ "next") # Ptr |-> next) **
    DFSAdjacencyList.addressed_sll next rest_addrs_2 rest_2 |--
    DFSAdjacencyList.addressed_sll edge_value
      (edge_value :: rest_addrs_2) (neighbor :: rest_2)).
  { simpl DFSAdjacencyList.addressed_sll.
    Exists next. entailer!. }
  sep_apply Hnode.
  sep_apply (addressed_sllseg_sll__dfs_flow
    row_head_2 edge_value done_addrs_2
    (edge_value :: rest_addrs_2) done_2 (neighbor :: rest_2)).
  assert (Haddrs : done_addrs_2 ++ edge_value :: rest_addrs_2 =
      Znth vertex_pre node_addrs_low_level_spec nil).
  { transitivity row_node_addrs_2;
      [symmetry; exact PreH15 | exact PreH13]. }
  assert (Hvalues : done_2 ++ neighbor :: rest_2 =
      Znth vertex_pre rows_low_level_spec nil).
  { transitivity row_2;
      [symmetry; exact PreH16 | exact PreH14]. }
  assert (Hmerge_current :
    ((adjacency_pre + vertex_pre * sizeof (PTR)) # Ptr |-> row_head_2) **
    DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec
      row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec
      vertex_pre **
    DFSAdjacencyList.addressed_sll row_head_2
      (done_addrs_2 ++ edge_value :: rest_addrs_2)
      (done_2 ++ neighbor :: rest_2) |--
    DFSAdjacencyList.graph_rep adjacency_pre g_low_level_spec
      row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec).
  { rewrite PreH12, Haddrs, Hvalues.
    apply (graph_rep_merge__execution_representation
      adjacency_pre g_low_level_spec row_ptrs_low_level_spec
      node_addrs_low_level_spec rows_low_level_spec vertex_pre PreH5). }
  sep_apply Hmerge_current.
  Exists read_set done_2 rest_2 done_addrs_2 rest_addrs_2
    row_2 row_node_addrs_2 row_head_2.
  unfold DFSAdjacencyList.visited.
  Exists read_values.
  entailer!.
Qed.

Lemma proof_of_dfs_adjacency_list_entail_wit_8 : dfs_adjacency_list_entail_wit_8.
Proof.
  unfold dfs_adjacency_list_entail_wit_8.
  left; intros.
  unfold DFSAdjacencyList.visited.
  Intros after_values.
  assert (Hall_after :
    DFSAdjacencyList.all_visited
      (done_2 ++ (neighbor :: nil)%list) bind_visited_set).
  { unfold DFSAdjacencyList.all_visited in *.
    intros v Hv.
    apply in_app_or in Hv.
    destruct Hv as [Hdone | Hneighbor].
    - apply PreH1. apply PreH22. exact Hdone.
    - simpl in Hneighbor. destruct Hneighbor as [-> | []]. exact PreH2. }
  assert (Hsafe_after :
    safeExec (eq bind_visited_set)
      (DFSAdjacencyList.dfs_loop g_low_level_spec vertex_pre)
      X_low_level_spec).
  { unfold applyf, DFSAdjacencyList.dfs_continue in PreH3.
    exact PreH3. }
  assert (Hextension_after :
    DFSAdjacencyList.visited_extension
      visited_set_low_level_spec bind_visited_set).
  { intros v Hv. apply PreH1. apply PreH20. exact Hv. }
  assert (Hvertex_after : bind_visited_set vertex_pre).
  { apply PreH1. exact PreH21. }
  sep_apply (graph_rep_split__execution_representation
    adjacency_pre g_low_level_spec row_ptrs_low_level_spec
    node_addrs_low_level_spec rows_low_level_spec vertex_pre PreH7).
  assert (Hsplit :
    DFSAdjacencyList.addressed_sll
      (Znth vertex_pre row_ptrs_low_level_spec 0)
      (Znth vertex_pre node_addrs_low_level_spec nil)
      (Znth vertex_pre rows_low_level_spec nil) |--
    EX next,
      DFSAdjacencyList.addressed_sllseg row_head_2 edge_value
        done_addrs_2 done_2 **
      (&(edge_value # "list" ->ₛ "data") # Int |-> neighbor) **
      (&(edge_value # "list" ->ₛ "next") # Ptr |-> next) **
      DFSAdjacencyList.addressed_sll next rest_addrs_2 rest_2).
  { rewrite <- PreH14, <- PreH15, <- PreH16.
    rewrite PreH17, PreH18.
    apply (addressed_sll_reverse_split__dfs_flow
      row_head_2 edge_value done_addrs_2 rest_addrs_2
      done_2 neighbor rest_2 PreH19). }
  sep_apply Hsplit.
  Intros next.
  Exists next after_values bind_visited_set done_2 rest_2
    done_addrs_2 rest_addrs_2 row_2 row_node_addrs_2
    row_head_2.
  entailer!.
  rewrite PreH4, PreH14.
  entailer!.
Qed.

Lemma proof_of_dfs_adjacency_list_entail_wit_9_1 : dfs_adjacency_list_entail_wit_9_1.
Proof.
  unfold dfs_adjacency_list_entail_wit_9_1.
  left; intros.
  Exists next_2 after_values after_set done_2 rest_2
    done_addrs_2 rest_addrs_2 row_2 row_node_addrs_2
    row_head_2.
  entailer!.
Qed.

Lemma proof_of_dfs_adjacency_list_entail_wit_9_2 : dfs_adjacency_list_entail_wit_9_2.
Proof.
  unfold dfs_adjacency_list_entail_wit_9_2.
  left; intros.
  assert (Hneighbor_visited : read_set neighbor).
  { unfold ZSimpleGraph.visited_values in PreH22.
    destruct PreH22 as [Hvalues_len [Hvalid_values Hvalue]].
    specialize (Hvalue neighbor PreH6) as [H01 Hiff].
    apply Hiff. destruct H01 as [Hzero | Hone]; [contradiction | exact Hone]. }
  assert (Hall_next :
    DFSAdjacencyList.all_visited
      (done_2 ++ (neighbor :: nil)%list) read_set).
  { unfold DFSAdjacencyList.all_visited in *.
    intros v Hv. apply in_app_or in Hv. destruct Hv as [Hv | Hv].
    - apply PreH20. exact Hv.
    - simpl in Hv. destruct Hv as [-> | []]. exact Hneighbor_visited. }
  sep_apply (IntArray.missing_i_merge_to_full
    visited_pre neighbor vertex_count_pre
    (Znth neighbor read_values 0) read_values); try lia.
  rewrite replace_Znth_Znth by lia.
  Exists next_2 read_values read_set done_2 rest_2
    done_addrs_2 rest_addrs_2 row_2 row_node_addrs_2
    row_head_2.
  entailer!.
Qed.

Lemma proof_of_dfs_adjacency_list_entail_wit_10 : dfs_adjacency_list_entail_wit_10.
Proof.
  unfold dfs_adjacency_list_entail_wit_10.
  left; intros.
  assert (Hsingle :
    (&(edge_value # "list" ->ₛ "data") # Int |-> neighbor) **
    (&(edge_value # "list" ->ₛ "next") # Ptr |-> next) |--
    DFSAdjacencyList.addressed_sllseg edge_value next
      (edge_value :: nil) (neighbor :: nil)).
  { simpl DFSAdjacencyList.addressed_sllseg.
    Exists next. entailer!. }
  sep_apply Hsingle.
  sep_apply (addressed_sllseg_append__dfs_flow
    row_head_2 edge_value next done_addrs_2
    (edge_value :: nil) done_2 (neighbor :: nil)).
  assert (Hrow : row_2 =
      (done_2 ++ (neighbor :: nil)%list) ++ rest).
  { rewrite <- app_assoc. simpl. exact PreH15. }
  assert (Haddrs : row_node_addrs_2 =
      (done_addrs_2 ++ (edge_value :: nil)%list) ++ rest_addrs).
  { rewrite <- app_assoc. simpl. exact PreH14. }
  Exists next_values next_set
    (done_2 ++ (neighbor :: nil)%list) rest
    (done_addrs_2 ++ (edge_value :: nil)%list) rest_addrs
    row_2 row_node_addrs_2 row_head_2.
  unfold DFSAdjacencyList.all_visited in *.
  entailer!.
  rewrite !Zlength_correct in *.
  rewrite !length_app. simpl. lia.
Qed.

Lemma proof_of_dfs_adjacency_list_entail_wit_11 : dfs_adjacency_list_entail_wit_11.
Proof.
  unfold dfs_adjacency_list_entail_wit_11.
  left; intros.
  subst vertex_count_pre.
  subst edge_value.
  prop_apply_p (graph_except_model__execution_representation
    adjacency_pre g_low_level_spec row_ptrs_low_level_spec
    node_addrs_low_level_spec rows_low_level_spec vertex_pre).
  Intros_p Hmodel.
  destruct todo_addrs as [|a todo_addrs];
    destruct todo as [|v todo];
    simpl DFSAdjacencyList.addressed_sll.
  - Intros_p Hnull.
    assert (Hsafe_return :
      safeExec (eq loop_set) (return tt) X_low_level_spec).
    { pose proof PreH17 as Hsafe.
      unfold DFSAdjacencyList.dfs_loop in Hsafe at 1.
      unfold_loop in Hsafe.
      prog_nf in Hsafe.
      safe_choice_r Hsafe.
      - exact Hsafe.
      - intros st Hst. subst st.
        intros (w & Hstep & Hnot).
        apply Hnot.
        apply PreH16.
        assert (Hedge :
          ZSimpleGraph.graph_step g_low_level_spec vertex_pre w).
        { unfold DFSAdjacencyList.dfs_step in Hstep.
          apply ZSimpleGraph.step_iff. exact Hstep. }
        unfold DFSAdjacencyList.adjacency_lists_model in Hmodel.
        destruct Hmodel as [_ [_ [_ Hrows]]].
        apply (proj2 (Hrows vertex_pre w PreH5)) in Hedge.
        rewrite <- PreH10, PreH12 in Hedge.
        rewrite app_nil_r in Hedge. exact Hedge. }
    sep_apply (addressed_sllseg_null_sll__dfs_flow
      row_head done_addrs done).
    rewrite app_nil_r in PreH11, PreH12.
    assert (Haddrs : done_addrs =
        Znth vertex_pre node_addrs_low_level_spec nil).
    { transitivity row_node_addrs;
        [symmetry; exact PreH11 | exact PreH9]. }
    assert (Hvalues : done = Znth vertex_pre rows_low_level_spec nil).
    { transitivity row;
        [symmetry; exact PreH12 | exact PreH10]. }
    assert (Hmerge_current :
      ((adjacency_pre + vertex_pre * sizeof (PTR)) # Ptr |-> row_head) **
      DFSAdjacencyList.graph_except adjacency_pre g_low_level_spec
        row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec
        vertex_pre **
      DFSAdjacencyList.addressed_sll row_head done_addrs done |--
      DFSAdjacencyList.graph_rep adjacency_pre g_low_level_spec
        row_ptrs_low_level_spec node_addrs_low_level_spec rows_low_level_spec).
    { rewrite PreH8, Haddrs, Hvalues.
      apply (graph_rep_merge__execution_representation
        adjacency_pre g_low_level_spec row_ptrs_low_level_spec
        node_addrs_low_level_spec rows_low_level_spec vertex_pre PreH5). }
    sep_apply Hmerge_current.
    Exists loop_set.
    unfold DFSAdjacencyList.visited.
    Exists loop_values.
    entailer!.
  - Intros_p Hfalse. contradiction.
  - Intros_p Hfalse. contradiction.
  - Intros next0. destruct H as [Hzero Hnonnull].
    exfalso. apply Hnonnull. unfold NULL in *. lia.
Qed.

Lemma proof_of_dfs_adjacency_list_return_wit_1 : dfs_adjacency_list_return_wit_1.
Proof.
  left.
  intros.
  Exists visited_set_out.
  entailer!.
Qed.

Lemma proof_of_dfs_adjacency_list_derive_bind_spec_by_low_level_spec : dfs_adjacency_list_derive_bind_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | Hsafe : safeExec _ (bind _ _) _ |- _ =>
      apply safeExec_bind in Hsafe as
        (X_low_level_spec & Hsafe_first & Hsafe_cont)
  end.
  Exists g_bind_spec row_ptrs_bind_spec node_addrs_bind_spec rows_bind_spec
    visited_set_bind_spec X_low_level_spec.
  split_pure_spatial.
  - cancel (DFSAdjacencyList.graph_rep adjacency_pre g_bind_spec
      row_ptrs_bind_spec node_addrs_bind_spec rows_bind_spec).
    cancel (DFSAdjacencyList.visited visited_pre g_bind_spec
      visited_set_bind_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros low_visited_set.
    Exists low_visited_set.
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; try assumption.
      match goal with
      | Hret : safeExec _ (return tt) X_low_level_spec |- _ =>
          exact (Hsafe_cont _ tt Hret)
      end.
  - split_pures; dump_pre_spatial; try assumption.
Qed.

Lemma proof_of_dfs_adjacency_list_derive_high_level_spec_by_low_level_spec : dfs_adjacency_list_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold DFSAdjacencyList.graph at 1.
  unfold DFSAdjacencyList.graph_with_rows at 1.
  Intros rows_high_level_spec row_ptrs_high_level_spec
    node_addrs_high_level_spec.
  assert (Hinitial_empty : initial_visited_set_high_level_spec == ∅).
  {
    sets_unfold.
    intro v.
    split; intro Hv.
    - exfalso.
      match goal with
      | Hempty : DFSAdjacencyList.empty_visited _ |- _ =>
          exact (Hempty v Hv)
      end.
    - contradiction.
  }
  Exists g_high_level_spec row_ptrs_high_level_spec
    node_addrs_high_level_spec rows_high_level_spec
    initial_visited_set_high_level_spec
    ((DFSAdjacencyList.dfs_program g_high_level_spec vertex_pre)
      initial_visited_set_high_level_spec).
  split_pure_spatial.
  - cancel (DFSAdjacencyList.graph_rep adjacency_pre g_high_level_spec
      row_ptrs_high_level_spec node_addrs_high_level_spec
      rows_high_level_spec).
    cancel (DFSAdjacencyList.visited visited_pre g_high_level_spec
      initial_visited_set_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros low_visited_set.
    Exists low_visited_set.
    split_pure_spatial.
    + unfold DFSAdjacencyList.graph.
      Exists rows_high_level_spec.
      unfold DFSAdjacencyList.graph_with_rows.
      Exists row_ptrs_high_level_spec node_addrs_high_level_spec.
      cancel (DFSAdjacencyList.graph_rep adjacency_pre g_high_level_spec
        row_ptrs_high_level_spec node_addrs_high_level_spec
        rows_high_level_spec).
      cancel (DFSAdjacencyList.visited visited_pre g_high_level_spec
        low_visited_set).
    + split_pures.
      * dump_pre_spatial.
        intros v Hvisited.
        pose proof
          (@DFS_visited_reachable
            ZSimpleGraph.G Z ZSimpleGraph.E ZSimpleGraph.graph_instance
            g_high_level_spec vertex_pre v) as Hdfs.
        match goal with
        | Hret : safeExec (eq low_visited_set) (return tt)
            ((DFSAdjacencyList.dfs_program g_high_level_spec vertex_pre)
              initial_visited_set_high_level_spec) |- _ =>
            destruct
              (@Hoare_safeexec_compose
                (Z -> Prop) unit
                (fun s => s == ∅)
                (DFSAdjacencyList.dfs_program g_high_level_spec vertex_pre)
                (fun _ s =>
                  s v <->
                  DFSAdjacencyList.is_reachable
                    g_high_level_spec vertex_pre v)
                Hdfs (eq low_visited_set) tt
                initial_visited_set_high_level_spec Hret Hinitial_empty)
              as [result [Hresult Heq]]
        end.
        subst result.
        exact (proj1 Hresult Hvisited).
      * dump_pre_spatial.
        intros v Hreachable.
        pose proof
          (@DFS_visited_reachable
            ZSimpleGraph.G Z ZSimpleGraph.E ZSimpleGraph.graph_instance
            g_high_level_spec vertex_pre v) as Hdfs.
        match goal with
        | Hret : safeExec (eq low_visited_set) (return tt)
            ((DFSAdjacencyList.dfs_program g_high_level_spec vertex_pre)
              initial_visited_set_high_level_spec) |- _ =>
            destruct
              (@Hoare_safeexec_compose
                (Z -> Prop) unit
                (fun s => s == ∅)
                (DFSAdjacencyList.dfs_program g_high_level_spec vertex_pre)
                (fun _ s =>
                  s v <->
                  DFSAdjacencyList.is_reachable
                    g_high_level_spec vertex_pre v)
                Hdfs (eq low_visited_set) tt
                initial_visited_set_high_level_spec Hret Hinitial_empty)
              as [result [Hresult Heq]]
        end.
        subst result.
        exact (proj2 Hresult Hreachable).
  - split_pures; dump_pre_spatial; try assumption.
    unfold safeExec, safe.
    exists initial_visited_set_high_level_spec.
    split.
    + reflexivity.
    + apply wp_self.
Qed.
