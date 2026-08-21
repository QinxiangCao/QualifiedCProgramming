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
Require Import SimpleC.EE.QCP_demos_LLM.graph_matrix_lib.
From SimpleC.EE.LLM_bench.Algorithms.DFS Require Import DFS_adjacency_matrix_goal.
From SimpleC.EE.LLM_bench.Algorithms.DFS Require Import DFS_adjacency_matrix_proof_auto.
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
Require Import Algorithms.DFS.DFS.
Require Import SimpleC.EE.LLM_bench.Algorithms.DFS.DFS_adjacency_matrix_lib.
Import ZSimpleGraph.
Local Open Scope sac.

Lemma proof_of_dfs_adjacency_matrix_safety_wit_3 : dfs_adjacency_matrix_safety_wit_3.
Proof.
  unfold dfs_adjacency_matrix_safety_wit_3.
  left; intros.
  entailer!; nia.
Qed.

Lemma proof_of_dfs_adjacency_matrix_safety_wit_4 : dfs_adjacency_matrix_safety_wit_4.
Proof.
  unfold dfs_adjacency_matrix_safety_wit_4.
  left; intros.
  entailer!; nia.
Qed.

Lemma proof_of_dfs_adjacency_matrix_entail_wit_1 : dfs_adjacency_matrix_entail_wit_1.
Proof.
  unfold dfs_adjacency_matrix_entail_wit_1.
  left; intros.
  unfold DFSAdjacencyMatrix.visited.
  Intros values.
  subst vertex_count_pre.
  Exists values.
  unfold ZSimpleGraph.vertex_valid in PreH4.
  entailer!.
Qed.

Lemma proof_of_dfs_adjacency_matrix_entail_wit_2 : dfs_adjacency_matrix_entail_wit_2.
Proof.
  unfold dfs_adjacency_matrix_entail_wit_2.
  left; intros.
  set (entered_set := fun v => visited_set_low_level_spec v \/ v = vertex_pre).
  assert (Hentered_values:
    ZSimpleGraph.visited_values g_low_level_spec
      (replace_Znth vertex_pre 1 values) entered_set).
  { unfold entered_set.
    apply visited_values_after_visit__dfs_core; assumption. }
  assert (Hprocessed:
    DFSAdjacencyMatrix.processed_neighbors
      g_low_level_spec vertex_pre 0 entered_set).
  { unfold DFSAdjacencyMatrix.processed_neighbors, entered_set.
    split.
    - right. reflexivity.
    - intros v Hv. lia. }
  assert (Hextension:
    DFSAdjacencyMatrix.visited_extension
      visited_set_low_level_spec entered_set).
  { unfold DFSAdjacencyMatrix.visited_extension, entered_set.
    intros v Hv. left. exact Hv. }
  assert (Hsafe_loop:
    safeExec (eq entered_set)
      (DFSAdjacencyMatrix.dfs_loop g_low_level_spec vertex_pre)
      X_low_level_spec).
  {
    pose proof PreH7 as Hsafe.
    unfold DFSAdjacencyMatrix.dfs_program in Hsafe.
    eapply safeExec_proequiv in Hsafe.
    2: apply DFS_unfold.
    unfold DFS_f, visit in Hsafe.
    apply safeExec_update'_bind in Hsafe.
    assert (Hstep_eq:
      reachable_basic.step g_low_level_spec =
      ZSimpleGraph.graph_step g_low_level_spec).
    { apply functional_extensionality; intros x.
      apply functional_extensionality; intros y.
      apply propositional_extensionality.
      apply ZSimpleGraph.step_iff. }
    unfold DFSAdjacencyMatrix.dfs_loop,
      DFSAdjacencyMatrix.dfs_program.
    rewrite <- Hstep_eq.
    eapply safeExec_conseq; [exact Hsafe |].
    intros s (s0 & -> & <-).
    unfold entered_set.
    apply functional_extensionality; intros v.
    apply propositional_extensionality.
    sets_unfold. split; intros [Hv | Heq]; auto;
      right; symmetry; exact Heq.
  }
  Exists (replace_Znth vertex_pre 1 values) entered_set.
  entailer!.
Qed.

Lemma proof_of_dfs_adjacency_matrix_entail_wit_3 : dfs_adjacency_matrix_entail_wit_3.
Proof.
  unfold dfs_adjacency_matrix_entail_wit_3.
  left; intros.
  assert (Hneighbor_valid:
    ZSimpleGraph.vertex_valid g_low_level_spec neighbor).
  { unfold ZSimpleGraph.vertex_valid. rewrite <- PreH5. lia. }
  assert (Hedge:
    ZSimpleGraph.graph_step g_low_level_spec vertex_pre neighbor).
  { eapply DFSAdjacencyMatrix.adjacency_matrix_model_nonzero_step; eauto. }
  assert (Hnot_visited: ~ visited_set1 neighbor).
  { unfold ZSimpleGraph.visited_values in PreH16.
    destruct PreH16 as [_ [_ Hvalue]].
    specialize (Hvalue neighbor Hneighbor_valid) as [_ Hiff].
    intros Hvisited. apply Hiff in Hvisited. lia. }
  assert (Hsafe_call:
    safeExec (eq visited_set1)
      (bind (DFSAdjacencyMatrix.dfs_program g_low_level_spec neighbor)
        (DFSAdjacencyMatrix.dfs_continue g_low_level_spec vertex_pre))
      X_low_level_spec).
  {
    pose proof PreH15 as Hsafe.
    unfold DFSAdjacencyMatrix.dfs_loop in Hsafe at 1.
    unfold_loop in Hsafe.
    prog_nf in Hsafe.
    safe_choice_l Hsafe.
    2:{ intros st Hst. subst st.
        exists neighbor. split; assumption. }
    prog_nf in Hsafe.
    apply (safeExec_get_bind neighbor) in Hsafe.
    2:{ intros st Hst. subst st. split; assumption. }
    exact Hsafe.
  }
  Exists visited_set1.
  subst vertex_count_pre.
  sep_apply (matrix_split_merge__dfs_core
    matrix_pre (ZSimpleGraph.vertex_count g_low_level_spec)
    rows_low_level_spec vertex_pre neighbor __default__List_Z);
    try lia.
  sep_apply (@GraphMatrixFlat.graph_rep_intro
    (ZSimpleGraph.vertex_count g_low_level_spec)
    (DFSAdjacencyMatrix.adjacency_matrix_model g_low_level_spec)
    matrix_pre rows_low_level_spec PreH3).
  unfold DFSAdjacencyMatrix.visited.
  Exists values1.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; eauto; lia).
  cancel.
Qed.

Lemma proof_of_dfs_adjacency_matrix_entail_wit_4_1 : dfs_adjacency_matrix_entail_wit_4_1.
Proof.
  unfold dfs_adjacency_matrix_entail_wit_4_1.
  left; intros.
  assert (Hprocessed_next:
    DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre
      (neighbor + 1) bind_visited_set).
  { unfold DFSAdjacencyMatrix.processed_neighbors in *.
    destruct PreH15 as [Hsource Hprocessed].
    split.
    - apply PreH1. exact Hsource.
    - intros v Hv Hedge.
      destruct (Z.eq_dec v neighbor) as [-> | Hne].
      + exact PreH2.
      + apply PreH1. apply Hprocessed; [lia | exact Hedge]. }
  assert (Hextension:
    DFSAdjacencyMatrix.visited_extension
      visited_set_low_level_spec bind_visited_set).
  { unfold DFSAdjacencyMatrix.visited_extension in *.
    intros v Hv. apply PreH1, PreH16, Hv. }
  unfold DFSAdjacencyMatrix.visited.
  Intros values2.
  Exists values2 bind_visited_set.
  subst vertex_count_pre.
  unfold DFSAdjacencyMatrix.dfs_continue, applyf in PreH3.
  entailer!.
Qed.

Lemma proof_of_dfs_adjacency_matrix_entail_wit_4_2 : dfs_adjacency_matrix_entail_wit_4_2.
Proof.
  unfold dfs_adjacency_matrix_entail_wit_4_2.
  left; intros.
  assert (Hneighbor_valid:
    ZSimpleGraph.vertex_valid g_low_level_spec neighbor).
  { unfold ZSimpleGraph.vertex_valid. rewrite <- PreH4. lia. }
  assert (Hnot_edge:
    ~ ZSimpleGraph.graph_step g_low_level_spec vertex_pre neighbor).
  { eapply DFSAdjacencyMatrix.adjacency_matrix_model_zero_not_step; eauto. }
  assert (Hprocessed_next:
    DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre
      (neighbor + 1) visited_set1).
  { unfold DFSAdjacencyMatrix.processed_neighbors in *.
    destruct PreH12 as [Hsource Hprocessed].
    split; [exact Hsource |].
    intros v Hv Hedge.
    destruct (Z.eq_dec v neighbor) as [-> | Hne].
    - contradiction.
    - apply Hprocessed; [lia | exact Hedge]. }
  Exists values1 visited_set1.
  subst vertex_count_pre.
  sep_apply (matrix_split_merge__dfs_core
    matrix_pre (ZSimpleGraph.vertex_count g_low_level_spec)
    rows_low_level_spec vertex_pre neighbor __default__List_Z);
    try lia.
  sep_apply (@GraphMatrixFlat.graph_rep_intro
    (ZSimpleGraph.vertex_count g_low_level_spec)
    (DFSAdjacencyMatrix.adjacency_matrix_model g_low_level_spec)
    matrix_pre rows_low_level_spec PreH2).
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; eauto; lia).
  cancel.
Qed.

Lemma proof_of_dfs_adjacency_matrix_entail_wit_4_3 : dfs_adjacency_matrix_entail_wit_4_3.
Proof.
  unfold dfs_adjacency_matrix_entail_wit_4_3.
  left; intros.
  assert (Hneighbor_valid:
    ZSimpleGraph.vertex_valid g_low_level_spec neighbor).
  { unfold ZSimpleGraph.vertex_valid. rewrite <- PreH5. lia. }
  assert (Hneighbor_visited: visited_set1 neighbor).
  { unfold ZSimpleGraph.visited_values in PreH16.
    destruct PreH16 as [_ [_ Hvalue]].
    specialize (Hvalue neighbor Hneighbor_valid) as [H01 Hiff].
    apply Hiff. destruct H01 as [Hzero | Hone]; [contradiction | exact Hone]. }
  assert (Hprocessed_next:
    DFSAdjacencyMatrix.processed_neighbors g_low_level_spec vertex_pre
      (neighbor + 1) visited_set1).
  { unfold DFSAdjacencyMatrix.processed_neighbors in *.
    destruct PreH13 as [Hsource Hprocessed].
    split; [exact Hsource |].
    intros v Hv Hedge.
    destruct (Z.eq_dec v neighbor) as [-> | Hne].
    - exact Hneighbor_visited.
    - apply Hprocessed; [lia | exact Hedge]. }
  Exists values1 visited_set1.
  subst vertex_count_pre.
  sep_apply (matrix_split_merge__dfs_core
    matrix_pre (ZSimpleGraph.vertex_count g_low_level_spec)
    rows_low_level_spec vertex_pre neighbor __default__List_Z);
    try lia.
  sep_apply (@GraphMatrixFlat.graph_rep_intro
    (ZSimpleGraph.vertex_count g_low_level_spec)
    (DFSAdjacencyMatrix.adjacency_matrix_model g_low_level_spec)
    matrix_pre rows_low_level_spec PreH3).
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; eauto; lia).
  cancel.
Qed.

Lemma proof_of_dfs_adjacency_matrix_entail_wit_5 : dfs_adjacency_matrix_entail_wit_5.
Proof.
  unfold dfs_adjacency_matrix_entail_wit_5.
  left; intros.
  Exists values2 visited_set2.
  entailer!.
Qed.

Lemma proof_of_dfs_adjacency_matrix_entail_wit_6 : dfs_adjacency_matrix_entail_wit_6.
Proof.
  unfold dfs_adjacency_matrix_entail_wit_6.
  left; intros.
  assert (Hneighbor_eq: neighbor = vertex_count_pre) by lia.
  destruct PreH10 as [Hsource Hprocessed].
  assert (Hsafe_return:
    safeExec (eq visited_set1) (return tt) X_low_level_spec).
  {
    pose proof PreH12 as Hsafe.
    unfold DFSAdjacencyMatrix.dfs_loop in Hsafe at 1.
    unfold_loop in Hsafe.
    prog_nf in Hsafe.
    safe_choice_r Hsafe.
    - exact Hsafe.
    - intros st Hst. subst st.
      intros (v & Hedge & Hnot).
      apply Hnot.
      apply Hprocessed.
      + subst neighbor.
        unfold ZSimpleGraph.graph_step,
          ZSimpleGraph.vertex_valid in Hedge.
        lia.
      + exact Hedge.
  }
  Exists visited_set1.
  unfold DFSAdjacencyMatrix.visited.
  Exists values1.
  subst vertex_count_pre.
  entailer!.
Qed.

Lemma proof_of_dfs_adjacency_matrix_return_wit_1 : dfs_adjacency_matrix_return_wit_1.
Proof.
  unfold dfs_adjacency_matrix_return_wit_1.
  left; intros.
  Exists visited_set_out.
  entailer!.
Qed.

Lemma proof_of_dfs_adjacency_matrix_derive_bind_spec_by_low_level_spec : dfs_adjacency_matrix_derive_bind_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | Hsafe: safeExec _ (bind _ _) _ |- _ =>
      apply safeExec_bind in Hsafe as
        (X_low_level_spec & Hsafe_first & Hsafe_cont)
  end.
  Exists g_bind_spec rows_bind_spec visited_set_bind_spec X_low_level_spec.
  split_pure_spatial.
  - cancel (GraphMatrixFlat.graph_rep vertex_count_pre
      (DFSAdjacencyMatrix.adjacency_matrix_model g_bind_spec)
      matrix_pre rows_bind_spec).
    cancel (DFSAdjacencyMatrix.visited visited_pre
      g_bind_spec visited_set_bind_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros low_visited_set.
    Exists low_visited_set.
    repeat (split_pure_spatial || split_pures).
    + cancel (GraphMatrixFlat.graph_rep vertex_count_pre
        (DFSAdjacencyMatrix.adjacency_matrix_model g_bind_spec)
        matrix_pre rows_bind_spec).
      cancel (DFSAdjacencyMatrix.visited visited_pre
        g_bind_spec low_visited_set).
    + dump_pre_spatial. exact H3.
    + dump_pre_spatial. exact H4.
    + dump_pre_spatial.
      unfold applyf.
      apply (Hsafe_cont (eq low_visited_set) tt).
      exact H5.
  - repeat (split_pure_spatial || split_pures);
      dump_pre_spatial; assumption.
Qed.

Lemma proof_of_dfs_adjacency_matrix_derive_high_level_spec_by_low_level_spec : dfs_adjacency_matrix_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Intros rows_low_level_spec.
  assert (Hinitial_empty:
    initial_visited_set_high_level_spec == Sets.empty).
  { sets_unfold. intros v. split.
    - intros Hv. exfalso.
      apply (H3 v). exact Hv.
    - tauto. }
  set (X_low_level_spec :=
    result_state (eq initial_visited_set_high_level_spec)
      (DFSAdjacencyMatrix.dfs_program g_high_level_spec vertex_pre)).
  assert (Hsafe_first:
    safeExec (eq initial_visited_set_high_level_spec)
      (DFSAdjacencyMatrix.dfs_program g_high_level_spec vertex_pre)
      X_low_level_spec).
  { unfold X_low_level_spec.
    apply safeExec_result_state.
    exists initial_visited_set_high_level_spec. reflexivity. }
  Exists g_high_level_spec rows_low_level_spec
    initial_visited_set_high_level_spec X_low_level_spec.
  split_pure_spatial.
  - cancel (GraphMatrixFlat.graph_rep vertex_count_pre
      (DFSAdjacencyMatrix.adjacency_matrix_model g_high_level_spec)
      matrix_pre rows_low_level_spec).
    cancel (DFSAdjacencyMatrix.visited visited_pre
      g_high_level_spec initial_visited_set_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros low_visited_set.
    Exists rows_low_level_spec low_visited_set.
    repeat (split_pure_spatial || split_pures).
    + cancel (GraphMatrixFlat.graph_rep vertex_count_pre
        (DFSAdjacencyMatrix.adjacency_matrix_model g_high_level_spec)
        matrix_pre rows_low_level_spec).
      cancel (DFSAdjacencyMatrix.visited visited_pre
        g_high_level_spec low_visited_set).
    + dump_pre_spatial.
      apply safeExec_ret in H6 as (s & Hs & Hresult).
      subst s.
      unfold X_low_level_spec, result_state in Hresult.
      sets_unfold in Hresult.
      destruct Hresult as (s0 & Hs0 & Hrun).
      subst s0.
      intros v Hv.
      pose proof (DFS_visited_reachable
        g_high_level_spec vertex_pre v) as Hdfs.
      unfold Hoare in Hdfs.
      specialize (Hdfs initial_visited_set_high_level_spec tt
        low_visited_set Hinitial_empty Hrun).
      unfold DFSAdjacencyMatrix.graph_reachable.
      apply Hdfs. exact Hv.
    + dump_pre_spatial.
      apply safeExec_ret in H6 as (s & Hs & Hresult).
      subst s.
      unfold X_low_level_spec, result_state in Hresult.
      sets_unfold in Hresult.
      destruct Hresult as (s0 & Hs0 & Hrun).
      subst s0.
      intros v Hv.
      pose proof (DFS_visited_reachable
        g_high_level_spec vertex_pre v) as Hdfs.
      unfold Hoare in Hdfs.
      specialize (Hdfs initial_visited_set_high_level_spec tt
        low_visited_set Hinitial_empty Hrun).
      unfold DFSAdjacencyMatrix.graph_reachable in Hv.
      apply Hdfs. exact Hv.
  - repeat (split_pure_spatial || split_pures);
      dump_pre_spatial; assumption.
Qed.
