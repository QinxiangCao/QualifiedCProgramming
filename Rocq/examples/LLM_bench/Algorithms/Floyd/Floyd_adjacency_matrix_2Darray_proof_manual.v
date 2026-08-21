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
From SimpleC.EE.LLM_bench.Algorithms.Floyd Require Import Floyd_adjacency_matrix_2Darray_goal.
From SimpleC.EE.LLM_bench.Algorithms.Floyd Require Import Floyd_adjacency_matrix_2Darray_proof_auto.
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
Require Import Algorithms.Floyd.Floyd.
Require Import SimpleC.EE.LLM_bench.Algorithms.Floyd.Floyd_adjacency_matrix_lib.
Import FloydGraph.
Import FloydAdjacencyMatrix2Darray.
Local Open Scope sac.

Lemma proof_of_floyd_adjacency_matrix_2Darray_safety_wit_6_split_goal_1 :
  floyd_adjacency_matrix_2Darray_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_safety_wit_6_split_goal_2 :
  floyd_adjacency_matrix_2Darray_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof PreH14 i k ltac:(split; lia);
  pose proof PreH14 k j ltac:(split; lia);
  lia.
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_safety_wit_6 :
  floyd_adjacency_matrix_2Darray_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_floyd_adjacency_matrix_2Darray_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_floyd_adjacency_matrix_2Darray_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_safety_wit_7_split_goal_1 :
  floyd_adjacency_matrix_2Darray_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_safety_wit_7_split_goal_2 :
  floyd_adjacency_matrix_2Darray_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof PreH15 i k ltac:(split; lia);
  pose proof PreH15 k j ltac:(split; lia);
  lia.
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_safety_wit_7 :
  floyd_adjacency_matrix_2Darray_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_floyd_adjacency_matrix_2Darray_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_floyd_adjacency_matrix_2Darray_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_entail_wit_1 : floyd_adjacency_matrix_2Darray_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply (@GraphMatrixFlat.graph_rep_elim
    10 (FloydAdjacencyMatrix2Darray.graph_matrix_model g_low_level_spec)
    dist_pre dist0_low_level_spec).
  Intros_p H.
  unfold FloydAdjacencyMatrix2Darray.graph_matrix_model in H.
  pre_process_pure.
  Exists dist0_low_level_spec.
  destruct H as [_ [Hmatrix_shape Hmatrix_values_safe]].
  assert (Hvalues_with_zero_default:
    forall r c,
      (0 <= r < 10 /\ 0 <= c) /\ c < 10 ->
      0 <= Znth c (Znth r dist0_low_level_spec __default__List_Z) 0 <= 1000000000).
  {
    intros r c Hrc.
    change 1000000000 with FloydGraph.infinity.
    eapply FloydAdjacencyMatrix2Darray.matrix_values_safe_Znth_default;
      [exact Hmatrix_shape | exact Hmatrix_values_safe |].
    unfold FloydGraph.max_vertices.
    lia.
  }
  pose proof PreH1 as Hsize_bounds.
  unfold FloydAdjacencyMatrix2Darray.graph_has_size,
    FloydAdjacencyMatrix2Darray.valid_size,
    FloydGraph.max_vertices in Hsize_bounds.
  destruct Hsize_bounds as [_ Hsize_bounds].
  unfold FloydAdjacencyMatrix2Darray.floyd_indexed_program in PreH2.
  split_pure_spatial.
  - apply (@GraphMatrixFlat.graph_rep_intro
      10 FloydAdjacencyMatrix2Darray.matrix_rows_model
      dist_pre dist0_low_level_spec).
    unfold FloydAdjacencyMatrix2Darray.matrix_rows_model.
    split; [exact Hmatrix_shape | exact Hmatrix_values_safe].
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_entail_wit_2_split_goal_1 :
  floyd_adjacency_matrix_2Darray_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold floyd_k_from in PreH8 at 1.
  rewrite range_iter_unfold in PreH8.
  safe_choice_l PreH8; try lia.
  safe_equiv.
  apply bind_equiv; [reflexivity | intros []; reflexivity].
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_entail_wit_2 :
  floyd_adjacency_matrix_2Darray_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_floyd_adjacency_matrix_2Darray_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_entail_wit_3_split_goal_1 :
  floyd_adjacency_matrix_2Darray_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold floyd_i_k_from in PreH10 at 1.
  unfold floyd_i_from in PreH10 at 1.
  rewrite range_iter_unfold in PreH10.
  safe_choice_l PreH10; try lia.
  safe_equiv.
  apply bind_equiv; [reflexivity | intros []; reflexivity].
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_entail_wit_3 :
  floyd_adjacency_matrix_2Darray_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_floyd_adjacency_matrix_2Darray_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_entail_wit_4_1 :
  floyd_adjacency_matrix_2Darray_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  unfold floyd_j_i_k_from in PreH16 at 1.
  unfold floyd_j_from in PreH16 at 1.
  rewrite range_iter_unfold in PreH16.
  safe_choice_l PreH16; try lia.
  set (dist_j :=
    replace_Znth i
      (replace_Znth j
        (Znth k (Znth i dist_j_2 __default__List_Z) 0 +
         Znth j (Znth k dist_j_2 __default__List_Z) 0)
        (Znth i dist_j_2 __default__List_Z))
      dist_j_2).
  edestruct (floyd_update_matrix_bridge
    dist_j_2 i j k n_pre __default__List_Z g_low_level_spec
    X_low_level_spec)
    as [Hupdated_values [Hupdated_shape Hupdated_safe]].
  all: try eassumption; try lia.
  Exists dist_j.
  subst dist_j.
  assert (Hupdated_model:
    FloydAdjacencyMatrix2Darray.matrix_rows_model
      (replace_Znth i
        (replace_Znth j
          (Znth k (Znth i dist_j_2 __default__List_Z) 0 +
           Znth j (Znth k dist_j_2 __default__List_Z) 0)
          (Znth i dist_j_2 __default__List_Z))
        dist_j_2)).
  {
    unfold FloydAdjacencyMatrix2Darray.matrix_rows_model.
    split; [exact Hupdated_shape | exact Hupdated_values].
  }
  sep_apply (@GraphMatrixFlat.graph_rep_intro
    10 FloydAdjacencyMatrix2Darray.matrix_rows_model
    dist_pre
    (replace_Znth i
      (replace_Znth j
        (Znth k (Znth i dist_j_2 __default__List_Z) 0 +
         Znth j (Znth k dist_j_2 __default__List_Z) 0)
        (Znth i dist_j_2 __default__List_Z))
      dist_j_2) Hupdated_model).
  assert (Hupdated_values_with_zero_default:
    forall r c,
      (0 <= r < 10 /\ 0 <= c) /\ c < 10 ->
      0 <=
        Znth c
          (Znth r
            (replace_Znth i
              (replace_Znth j
                (Znth k (Znth i dist_j_2 __default__List_Z) 0 +
                 Znth j (Znth k dist_j_2 __default__List_Z) 0)
                (Znth i dist_j_2 __default__List_Z))
              dist_j_2)
            __default__List_Z) 0 <= 1000000000).
  {
    intros r c Hrc.
    change 1000000000 with FloydGraph.infinity.
    eapply FloydAdjacencyMatrix2Darray.matrix_values_safe_Znth_default;
      [exact Hupdated_shape | exact Hupdated_values |].
    unfold FloydGraph.max_vertices.
    lia.
  }
  destruct PreH6 as [Hvertex_count Hvalid_size].
  apply split_pure_and_spatial_goals.
  - entailer!.
  - dump_pre_spatial.
    split; [exact Hvertex_count | exact Hvalid_size].
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_entail_wit_4_2 :
  floyd_adjacency_matrix_2Darray_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  unfold floyd_j_i_k_from in PreH15 at 1.
  unfold floyd_j_from in PreH15 at 1.
  rewrite range_iter_unfold in PreH15.
  safe_choice_l PreH15; try lia.
  assert (Hnext_safe:
    safeExec (FloydAdjacencyMatrix2Darray.state_model dist_j_2)
      (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from
        g_low_level_spec n_pre k i (j + 1))
      X_low_level_spec).
  {
    eapply floyd_no_update_matrix_bridge; try eassumption; try lia.
    left.
    change 1000000000 with FloydGraph.infinity in PreH1.
    exact PreH1.
  }
  Exists dist_j_2.
  sep_apply (@GraphMatrixFlat.graph_rep_intro
    10 FloydAdjacencyMatrix2Darray.matrix_rows_model
    dist_pre dist_j_2 PreH3).
  destruct PreH5 as [Hvertex_count Hvalid_size].
  apply split_pure_and_spatial_goals.
  - entailer!.
  - dump_pre_spatial.
    split; [exact Hvertex_count | exact Hvalid_size].
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_entail_wit_4_3 :
  floyd_adjacency_matrix_2Darray_entail_wit_4_3.
Proof.
  aggressive_pre_process.
  unfold floyd_j_i_k_from in PreH14 at 1.
  unfold floyd_j_from in PreH14 at 1.
  rewrite range_iter_unfold in PreH14.
  safe_choice_l PreH14; try lia.
  assert (Hnext_safe:
    safeExec (FloydAdjacencyMatrix2Darray.state_model dist_j_2)
      (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from
        g_low_level_spec n_pre k i (j + 1))
      X_low_level_spec).
  {
    eapply floyd_no_update_matrix_bridge; try eassumption; try lia.
    right; left.
    change 1000000000 with FloydGraph.infinity in PreH1.
    exact PreH1.
  }
  Exists dist_j_2.
  sep_apply (@GraphMatrixFlat.graph_rep_intro
    10 FloydAdjacencyMatrix2Darray.matrix_rows_model
    dist_pre dist_j_2 PreH2).
  destruct PreH4 as [Hvertex_count Hvalid_size].
  apply split_pure_and_spatial_goals.
  - entailer!.
  - dump_pre_spatial.
    split; [exact Hvertex_count | exact Hvalid_size].
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_entail_wit_4_4 :
  floyd_adjacency_matrix_2Darray_entail_wit_4_4.
Proof.
  aggressive_pre_process.
  unfold floyd_j_i_k_from in PreH16 at 1.
  unfold floyd_j_from in PreH16 at 1.
  rewrite range_iter_unfold in PreH16.
  safe_choice_l PreH16; try lia.
  assert (Hnext_safe:
    safeExec (FloydAdjacencyMatrix2Darray.state_model dist_j_2)
      (FloydAdjacencyMatrix2Darray.floyd_j_i_k_from
        g_low_level_spec n_pre k i (j + 1))
      X_low_level_spec).
  {
    eapply floyd_no_update_matrix_bridge; try eassumption; try lia.
    right; right.
    exact PreH1.
  }
  Exists dist_j_2.
  sep_apply (@GraphMatrixFlat.graph_rep_intro
    10 FloydAdjacencyMatrix2Darray.matrix_rows_model
    dist_pre dist_j_2 PreH4).
  destruct PreH6 as [Hvertex_count Hvalid_size].
  apply split_pure_and_spatial_goals.
  - entailer!.
  - dump_pre_spatial.
    split; [exact Hvertex_count | exact Hvalid_size].
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_entail_wit_5_split_goal_1 :
  floyd_adjacency_matrix_2Darray_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold floyd_j_i_k_from in PreH12 at 1.
  unfold floyd_j_from in PreH12 at 1.
  rewrite range_iter_unfold in PreH12.
  safe_choice_r PreH12.
  unfold floyd_i_k_after in PreH12.
  exact PreH12.
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_entail_wit_5 :
  floyd_adjacency_matrix_2Darray_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_floyd_adjacency_matrix_2Darray_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_entail_wit_6_split_goal_1 :
  floyd_adjacency_matrix_2Darray_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold floyd_i_k_from in PreH10 at 1.
  unfold floyd_i_from in PreH10 at 1.
  rewrite range_iter_unfold in PreH10.
  safe_choice_r PreH10.
  unfold floyd_k_after in PreH10.
  exact PreH10.
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_entail_wit_6 :
  floyd_adjacency_matrix_2Darray_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_floyd_adjacency_matrix_2Darray_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_return_wit_1 : floyd_adjacency_matrix_2Darray_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold floyd_k_from in PreH8 at 1.
  rewrite range_iter_unfold in PreH8.
  safe_choice_r PreH8.
  Exists dist_k.
  apply split_pure_and_spatial_goals.
  - entailer!.
  - dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_floyd_adjacency_matrix_2Darray_derive_high_level_spec_by_low_level_spec :
  floyd_adjacency_matrix_2Darray_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rename H into Hsize.
  rename H0 into Hinitial_state.
  unfold FloydAdjacencyMatrix2Darray.floyd_init_matrix in Hinitial_state.
  sep_apply (@GraphMatrixFlat.graph_rep_elim
    10 (FloydAdjacencyMatrix2Darray.graph_matrix_model g_high_level_spec)
    dist_pre dist0_high_level_spec).
  Intros_p Hgraph_model.
  unfold FloydAdjacencyMatrix2Darray.graph_matrix_model in Hgraph_model.
  destruct Hgraph_model as
    [Hmatrix_model [Hmatrix_shape Hmatrix_values_safe]].
  pose proof
    (FloydAdjacencyMatrix2Darray.matrix_model_nonnegative_edges
      g_high_level_spec dist0_high_level_spec
      Hmatrix_model Hmatrix_values_safe)
    as Hnonnegative_edges.
  pose proof
    (FloydAdjacencyMatrix2Darray.floyd_nonnegative_edges_no_negative_cycle
      g_high_level_spec Hnonnegative_edges)
    as Hno_negative_cycle.
  set (X_low_level_spec :=
    result_state (FloydAdjacencyMatrix2Darray.floyd_initial_state
      g_high_level_spec)
      (FloydAdjacencyMatrix2Darray.floyd_indexed_program
        g_high_level_spec n_pre)).
  assert (Hstate_model_initial:
    FloydAdjacencyMatrix2Darray.state_model dist0_high_level_spec
      (FloydAdjacencyMatrix2Darray.state_of_matrix dist0_high_level_spec)).
  {
    intros u v Hu Hv.
    pose proof Hmatrix_values_safe u v Hu Hv as Hsafe.
    unfold FloydAdjacencyMatrix2Darray.state_model.
    change (@dist Z
      (FloydAdjacencyMatrix2Darray.state_of_matrix dist0_high_level_spec)
      (u, v)) with
      (FloydAdjacencyMatrix2Darray.matrix_distance
        dist0_high_level_spec u v).
    unfold FloydAdjacencyMatrix2Darray.matrix_distance,
      FloydGraph.matrix_distance, FloydGraph.cell_as_distance,
      FloydAdjacencyMatrix2Darray.abstract_distance_nonnegative,
      FloydAdjacencyMatrix2Darray.distance_as_observed_cell.
    unfold FloydAdjacencyMatrix2Darray.physical_cell in Hsafe |- *.
    set (cell := Znth v (Znth u dist0_high_level_spec nil)
      FloydGraph.infinity).
    destruct (Z.eq_dec cell FloydGraph.infinity) as [Heq | Hneq].
    - split; [exact I | exact Heq].
    - split.
      + lia.
      + destruct (Z_lt_dec cell FloydGraph.infinity) as [_ | Hge].
        * reflexivity.
        * lia.
  }
  assert (Hsafe_first:
    safeExec (FloydAdjacencyMatrix2Darray.state_model
      dist0_high_level_spec)
      (FloydAdjacencyMatrix2Darray.floyd_indexed_program
        g_high_level_spec n_pre)
      X_low_level_spec).
  {
    unfold X_low_level_spec, safeExec, safe, result_state.
    eexists; split; [exact Hstate_model_initial |].
    sets_unfold; intros ? ? ?; eauto.
  }
  Exists g_high_level_spec dist0_high_level_spec X_low_level_spec.
  split_pure_spatial.
  - assert (Hgraph_rows_model:
      FloydAdjacencyMatrix2Darray.graph_matrix_model
        g_high_level_spec dist0_high_level_spec).
    {
      unfold FloydAdjacencyMatrix2Darray.graph_matrix_model.
      split; [exact Hmatrix_model |].
      split; [exact Hmatrix_shape | exact Hmatrix_values_safe].
    }
    sep_apply (@GraphMatrixFlat.graph_rep_intro
      10 (FloydAdjacencyMatrix2Darray.graph_matrix_model g_high_level_spec)
      dist_pre dist0_high_level_spec Hgraph_rows_model).
    entailer!.
    apply derivable1_wand_sepcon_adjoint.
    Intros dist1_2.
    Exists dist1_2.
    prop_apply (@GraphMatrixFlat.graph_rep_model
      10
      FloydAdjacencyMatrix2Darray.matrix_rows_model
      dist_pre dist1_2).
    Intros.
    rename H0 into Hmatrix_rows.
    unfold FloydAdjacencyMatrix2Darray.matrix_rows_model in Hmatrix_rows.
    destruct Hmatrix_rows as [Hshape_final Hvalues_final].
    assert (Hshortest:
      FloydAdjacencyMatrix2Darray.floyd_shortest_matrix
        g_high_level_spec dist1_2).
    {
      split; [exact Hshape_final | split; [exact Hvalues_final |]].
      apply safeExec_ret in H as
        (s_final & Hmodel_final & Hresult).
      unfold X_low_level_spec, result_state in Hresult.
      sets_unfold in Hresult.
      destruct Hresult as (s_initial & Hinitial & Hrun).
      exists s_final.
      split; [exact Hmodel_final |].
      assert (Hgraph_wf: FloydGraph.graph_wf g_high_level_spec) by
        (unfold FloydAdjacencyMatrix2Darray.graph_has_size,
          FloydAdjacencyMatrix2Darray.valid_size,
          FloydGraph.graph_wf in Hsize |- *; lia).
      pose proof
        (floyd_indexed_program_Hoare_correct
          g_high_level_spec n_pre Hgraph_wf Hno_negative_cycle Hsize)
        as Hcorrect.
      unfold Hoare in Hcorrect.
      exact (Hcorrect s_initial tt s_final Hinitial Hrun).
    }
    apply split_pure_and_spatial_goals.
    + cancel (GraphMatrixFlat.graph_rep
        10
        FloydAdjacencyMatrix2Darray.matrix_rows_model
        dist_pre dist1_2).
    + dump_pre_spatial.
      exact Hshortest.
  - repeat (split_pure_spatial || split_pures);
      dump_pre_spatial; auto; lia.
Qed.
