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
From SimpleC.EE.LLM_bench.Algorithms.Prim Require Import prim_adjacency_matrix_return_matrix_goal.
From SimpleC.EE.LLM_bench.Algorithms.Prim Require Import prim_adjacency_matrix_return_matrix_proof_auto.
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
Require Import SimpleC.EE.LLM_bench.Algorithms.Prim.prim_adjacency_matrix_lib.
Require Import ListLib.Base.Positional.
Local Open Scope sac.

Ltac qcp_light_sep :=
  repeat (split_pure_spatial || split_pures);
  try solve [
    sepcon_assoc_change; cancel
  | normalize; cancel
  | dump_pre_spatial; int_auto
  | dump_pre_spatial; lia
  | dump_pre_spatial; assumption
  | dump_pre_spatial; reflexivity
  | apply derivable1s_coq_prop_r; int_auto
  | apply derivable1s_coq_prop_r; lia
  | apply derivable1s_coq_prop_r; assumption
  | apply derivable1s_coq_prop_r; reflexivity
  ].

Lemma int_ptr_array2_missing_i_Zlength : forall x n i row_ptr rows,
  IntPtrArray2.missing_i x n i row_ptr rows |-- “ Zlength rows = n ”.
Proof.
  intros.
  unfold IntPtrArray2.missing_i.
  Intros row_ptrs.
  entailer!.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_1_split_goal_1 : prim_adjacency_matrix_return_matrix_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_1 : prim_adjacency_matrix_return_matrix_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_2_split_goal_1 : prim_adjacency_matrix_return_matrix_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  symmetry; apply repeat_Z_tail; lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_2 : prim_adjacency_matrix_return_matrix_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_3_split_goal_1 : prim_adjacency_matrix_return_matrix_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_3_split_goal_2 : prim_adjacency_matrix_return_matrix_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace i with n_pre by lia.
  reflexivity.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_3 : prim_adjacency_matrix_return_matrix_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_4_split_goal_1 : prim_adjacency_matrix_return_matrix_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  symmetry; apply repeat_Z_tail; lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_4 : prim_adjacency_matrix_return_matrix_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_5_split_goal_1 : prim_adjacency_matrix_return_matrix_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_5_split_goal_2 : prim_adjacency_matrix_return_matrix_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace i with n_pre by lia.
  reflexivity.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_5 : prim_adjacency_matrix_return_matrix_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_5_split_goal_2.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_6_split_goal_1 : prim_adjacency_matrix_return_matrix_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  symmetry; apply repeat_Z_tail; lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_6 : prim_adjacency_matrix_return_matrix_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_7_split_goal_1 : prim_adjacency_matrix_return_matrix_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace i with n_pre by lia.
  reflexivity.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_7 : prim_adjacency_matrix_return_matrix_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_7_split_goal_1.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_9_boot_split_goal_1 : prim_adjacency_matrix_return_matrix_entail_wit_9_boot_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply init_lowcost_values_in_range; lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_9_boot : prim_adjacency_matrix_return_matrix_entail_wit_9_boot.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_9_boot_split_goal_1.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_10_1_boot_split_goal_1 : prim_adjacency_matrix_return_matrix_entail_wit_10_1_boot_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (j = 0).
  {
    destruct (Z.eq_dec j 0); [lia |].
    assert (1 <= j) by lia.
    destruct (PreH19 H0) as [Hmin _].
    specialize (PreH22 j ltac:(subst l_lowcost_2;
      rewrite Zlength_replace_Znth_local;
      unfold repeat_Z; rewrite Zlength_correct, repeat_length; lia)).
    lia.
  }
  subst j.
  split.
  - subst l_lowcost_2.
    rewrite Znth_replace_Znth_same_local.
    + reflexivity.
    + unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
  - reflexivity.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_10_1_boot_split_goal_2 : prim_adjacency_matrix_return_matrix_entail_wit_10_1_boot_split_goal_2.
Proof.
  intros n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    l_visited_2 l_vertex_parent_2 l_edge_parent_2
    l_lowcost_2 minIndex min i j
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    PreH20 PreH21 PreH22 PreH23 PreH24 PreH25.
  destruct (Z.eq_dec j 0) as [Hj | Hj].
  - subst j.
    assert (Hrange_arg : 0 <= 0 < Zlength l_lowcost_2).
    {
      rewrite PreH21.
      rewrite Zlength_replace_Znth_local by
        (unfold repeat_Z; rewrite Zlength_correct, repeat_length; lia).
      unfold repeat_Z; rewrite Zlength_correct, repeat_length; lia.
    }
    specialize (PreH22 0 Hrange_arg).
    lia.
  - assert (Hrange_arg : 0 <= j < Zlength l_lowcost_2).
    {
      rewrite PreH21.
      rewrite Zlength_replace_Znth_local by
        (unfold repeat_Z; rewrite Zlength_correct, repeat_length; lia).
      unfold repeat_Z; rewrite Zlength_correct, repeat_length; lia.
    }
    specialize (PreH22 j Hrange_arg).
    lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_10_1_boot : prim_adjacency_matrix_return_matrix_entail_wit_10_1_boot.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_10_1_boot_split_goal_1.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_10_1_boot_split_goal_2.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_10_2_boot : prim_adjacency_matrix_return_matrix_entail_wit_10_2_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  unfold prim_adjacency_matrix_graph_model in Hgraph_model.
  Exists l_lowcost_2 l_vertex_parent_2 l_edge_parent_2 l_visited_2 s_2.
  prop_apply (IntArray.full_Zlength lowcost n_pre l_lowcost_2).
  Intros_p Hlow_len.
  split_pure_spatial.
  - cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (IntArray.full visited n_pre l_visited_2).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
  - split_pures; dump_pre_spatial; subst; try lia; try int_auto;
	      try match goal with
	      | |- INT_MIN <= Znth ?j ?lowcost 0 =>
	          unfold lowcost_values_in_range in PreH26;
	          specialize (PreH26 j ltac:(rewrite Hlow_len; lia));
	          lia
	      | |- min_vertex_in_range _ _ (?j + 1) _ ?j _ _ =>
	          eapply min_vertex_in_range_take_current_from_arrays; eauto; lia
	      end.
  pose proof (PreH26 j ltac:(lia)) as Hlow_j.
  lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_10_3_boot : prim_adjacency_matrix_return_matrix_entail_wit_10_3_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists l_lowcost_2 l_vertex_parent_2 l_edge_parent_2 l_visited_2 s_2.
  split_pure_spatial.
  - cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (IntArray.full visited n_pre l_visited_2).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
  - split_pures; dump_pre_spatial; subst; try lia; try int_auto;
      match goal with
      | |- min_vertex_in_range _ _ (?j + 1) _ _ _ _ =>
          eapply min_vertex_in_range_skip_not_candidate;
	          [ lia
	          | intros Hcand;
	            unfold candidate_vertex in Hcand;
	            destruct Hcand as [Hgraph [Hnot_valid _]];
	            destruct (PreH19 j Hgraph) as [Hvisited_to_valid _];
            apply Hnot_valid;
            apply Hvisited_to_valid;
            exact PreH1
          | exact PreH27 ]
      end.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_10_4_boot_split_goal_1 : prim_adjacency_matrix_return_matrix_entail_wit_10_4_boot_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hj_pos : 1 <= j).
  {
    destruct (Z.eq_dec j 0); [| lia].
    subst j l_visited_2.
    unfold repeat_Z in PreH1.
    rewrite Znth_repeat_lt in PreH1 by lia.
    lia.
  }
  apply PreH18.
  exact Hj_pos.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_10_4_boot : prim_adjacency_matrix_return_matrix_entail_wit_10_4_boot.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_10_4_boot_split_goal_1.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_10_5_boot_split_goal_1 : prim_adjacency_matrix_return_matrix_entail_wit_10_5_boot_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hj_pos : 1 <= j).
  {
    destruct (Z.eq_dec j 0); [| lia].
    subst j l_lowcost_2.
    rewrite Znth_replace_Znth_same_local in PreH1.
    - destruct (PreH19 ltac:(lia)) as [Hmin _].
      lia.
    - unfold repeat_Z. rewrite Zlength_correct, repeat_length. lia.
  }
  apply PreH19.
  exact Hj_pos.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_10_5_boot : prim_adjacency_matrix_return_matrix_entail_wit_10_5_boot.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_10_5_boot_split_goal_1.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_10_6_boot : prim_adjacency_matrix_return_matrix_entail_wit_10_6_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists l_lowcost_2 l_vertex_parent_2 l_edge_parent_2 l_visited_2 s_2.
  split_pure_spatial.
  - cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (IntArray.full visited n_pre l_visited_2).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
  - split_pures; dump_pre_spatial; subst; try lia; try int_auto;
      match goal with
      | |- min_vertex_in_range _ _ (?j + 1) _ _ _ _ =>
          eapply min_vertex_in_range_skip_not_better_from_value; eauto; lia
      end.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_11_2_boot : prim_adjacency_matrix_return_matrix_entail_wit_11_2_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  unfold prim_adjacency_matrix_graph_model in Hgraph_model.
  assert (Hj_done : j = n_pre) by lia.
  subst j.
  assert (Hcand_exists :
    candidate_vertex_exists_in_range n_pre
      g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000).
  {
    apply PreH25. lia.
  }
  assert (HminIndex_not_minus : minIndex <> -1).
  {
    eapply min_vertex_in_range_not_minus_one; eauto.
  }
  destruct (min_vertex_parent_pair_exists
    n_pre g_low_level_spec s_2
    l_lowcost_2 l_edge_parent_2 1000000000 minIndex
    PreH26 HminIndex_not_minus) as [u Hparent_pair].
  Exists u minIndex l_lowcost_2 l_vertex_parent_2 l_edge_parent_2 l_visited_2 s_2.
  split_pure_spatial.
  - cancel ((( &( "j" ) )) # Int  |-> n_pre).
    cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (IntArray.full visited n_pre l_visited_2).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
  - split_pures; dump_pre_spatial; subst; try lia; try int_auto;
      match goal with
      | |- candidate_vertex_exists_in_range _ _ _ _ _ _ =>
          exact Hcand_exists
      | |- minIndex <> -1 =>
          exact HminIndex_not_minus
      | |- min = Znth minIndex l_lowcost_2 0 =>
          apply PreH28; exact HminIndex_not_minus
      | |- selected_parent_edge_is_min_cut_edge _ _ _ _ =>
          eapply min_vertex_parent_is_min_cut_edge;
            [exact Hgraph_model | exact PreH22 | exact PreH26 | exact HminIndex_not_minus]
      | |- selected_parent_pair _ _ _ _ _ _ =>
          exact Hparent_pair
      | |- min_vertex_in_range _ _ n_pre _ _ _ _ =>
          exact PreH26
      end.
Qed.

Ltac intros_prim_adj_ret_wit_12_1_boot :=
  intros n_pre X_low_level_spec src_low_level_spec g_low_level_spec
	  matrix_low_level_spec l_visited_2 l_lowcost l_vertex_parent_2
	  l_edge_parent i minIndex min row_ptr_2 __default__List_Z
	  PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
	  PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
	  PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_1 : prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_1.
Proof.
  intros_prim_adj_ret_wit_12_1_boot.
  apply derivable1s_coq_prop_r.
  rewrite PreH22, PreH23.
  apply vertex_parent_matches_default_edge_parent with (matrix := matrix_low_level_spec) (inf := 1000000000) (src := 0).
  exact PreH1.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_2 : prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_2.
Proof.
  intros_prim_adj_ret_wit_12_1_boot.
  apply derivable1s_coq_prop_r.
  rewrite PreH20.
  apply initSt_lowcost_sum_matches_state; [reflexivity | lia | exact PreH12].
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_3 : prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_3.
Proof.
  intros_prim_adj_ret_wit_12_1_boot.
  apply derivable1s_coq_prop_r.
  apply initSt_state_vertex_count.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_4 : prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_4.
Proof.
  intros_prim_adj_ret_wit_12_1_boot.
  apply derivable1s_coq_prop_r.
  rewrite PreH24.
  eapply initSt_visited_matches_state_zero_repeat;
    [exact PreH1 | reflexivity].
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_5 : prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_5.
Proof.
  intros_prim_adj_ret_wit_12_1_boot.
  apply derivable1s_coq_prop_r.
  apply initSt_growing_subgraph_state.
  rewrite <- PreH8.
  exact PreH13.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_6 : prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_6.
Proof.
  intros_prim_adj_ret_wit_12_1_boot.
  apply derivable1s_coq_prop_r.
  apply initStPred_Prim2_to_loop0.
  rewrite <- PreH8.
  exact PreH17.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_7 : prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_7.
Proof.
  intros_prim_adj_ret_wit_12_1_boot.
  apply derivable1s_coq_prop_r.
  pose proof PreH1 as Hmodel.
  unfold prim_adjacency_matrix_graph_model, adjacency_matrix_model in Hmodel.
  destruct Hmodel as [[_ Hrow_len] _].
  rewrite Hrow_len; lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_spatial : prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_spatial.
Proof.
  intros_prim_adj_ret_wit_12_1_boot.
  pose proof PreH1 as Hmodel.
  unfold prim_adjacency_matrix_graph_model, adjacency_matrix_model in Hmodel.
  destruct Hmodel as [[Hmatrix_len _] _].
  rewrite <- (Znth_indep matrix_low_level_spec minIndex __default__List_Z nil)
    by (rewrite Hmatrix_len; lia).
  cancel (IntArray.full row_ptr_2
    (Zlength (Znth minIndex matrix_low_level_spec __default__List_Z))
    (Znth minIndex matrix_low_level_spec __default__List_Z)).
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot : prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_spatial.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_1.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_2.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_3.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_4.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_5.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_6.
  - Goal_apply proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_1_boot_split_goal_7.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_12_2_boot : prim_adjacency_matrix_return_matrix_entail_wit_12_2_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_Zlength.
  Intros_p Hvisited_replace_len.
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  unfold prim_adjacency_matrix_graph_model in Hgraph_model.
  assert (Henv0 : PrimEnv g_low_level_spec 0).
  {
    rewrite <- PreH7.
    exact PreH12.
  }
  destruct (selected_parent_add_to_mst_exists
    g_low_level_spec 0 s_2 l_edge_parent minIndex u_2 v_2
    Henv0 PreH18 PreH30) as [s_after Hadd].
  assert (Hsafe_after :
    safeExec (prim_state_is s_after)
      (Prim2_loop g_low_level_spec i) X_low_level_spec).
	  {
	    eapply (selected_parent_prim2_loop_step
	      n_pre matrix_low_level_spec g_low_level_spec 1000000000
	      i X_low_level_spec s_2 s_after l_edge_parent minIndex);
	      [exact (prim_graph_valid g_low_level_spec src_low_level_spec PreH12)
	      | exact Hgraph_model | lia | lia | exact PreH17 | exact PreH29 | exact Hadd].
	  }
  assert (Hgrow_after :
    growing_subgraph_state g_low_level_spec s_after).
  {
    eapply selected_parent_add_to_mst_growing; eauto.
  }
  assert (Hvisited_after :
    visited_matches_state g_low_level_spec s_after
      (replace_Znth minIndex 1 l_visited_2)).
  {
    eapply selected_parent_add_to_mst_visited_matches_replaced_len; eauto.
  }
	  assert (Hcount_after : state_vertex_count s_after = i + 1).
	  {
	    rewrite <- PreH20.
	    eapply selected_parent_add_to_mst_state_vertex_count; eauto.
	  }
  assert (Hselected_after :
    selected_edges_match_state
      g_low_level_spec src_low_level_spec s_after l_edge_parent).
  {
    eapply (selected_parent_add_to_mst_parent_edges_match
      g_low_level_spec src_low_level_spec s_2 s_after
      l_edge_parent minIndex); eauto.
  }
  sep_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_elim n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model_rows.
  prop_apply (IntPtrArray2.full_Zlength graph_pre n_pre matrix_low_level_spec).
  Intros_p Hmatrix_len.
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    graph_pre minIndex n_pre matrix_low_level_spec).
  - dump_pre_spatial. lia.
	  - Intros row_ptr.
	    Exists row_ptr l_vertex_parent_2 u_2 v_2 l_edge_parent
	      l_visited_2 s_2 s_after l_lowcost.
	    unfold StorePtrAsElement.storeA.
	    change (IntPtrArray2.ElemArray.full row_ptr
	      (Zlength (Znth minIndex matrix_low_level_spec nil))
	      (Znth minIndex matrix_low_level_spec nil))
	      with (IntArray.full row_ptr
	        (Zlength (Znth minIndex matrix_low_level_spec nil))
	        (Znth minIndex matrix_low_level_spec nil)).
    repeat (split_pure_spatial || split_pures);
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; lia);
      try solve [
        apply derivable1s_coq_prop_r;
	        pose proof (selected_parent_lowcost_bounds
	          n_pre matrix_low_level_spec g_low_level_spec s_2
	          l_lowcost l_edge_parent 1000000000 minIndex u_2 v_2
	          Hgraph_model PreH23 PreH30 ltac:(lia)) as [Hmin_low Hmin_high];
	        rewrite PreH28;
	        lia
	      ];
      try solve [
        apply derivable1s_coq_prop_r;
	        eapply (selected_parent_add_to_mst_lowcost_sum_matches_state
	          g_low_level_spec s_2 s_after l_lowcost l_edge_parent
	          1000000000 minIndex);
	        [exact Henv0 | exact PreH18 | exact PreH23 | exact PreH24 | exact Hadd]
	      ];
      try solve [
        sepcon_assoc_change; cancel
      | normalize; cancel
      | dump_pre_spatial; int_auto
      | dump_pre_spatial; lia
      | dump_pre_spatial; assumption
	      | dump_pre_spatial; reflexivity
	      | apply derivable1s_coq_prop_r; int_auto
	      | apply derivable1s_coq_prop_r; lia
	      ].
	    all: try solve [change (sizeof(PTR)) with ptr_size_Z; sepcon_assoc_change; cancel].
	  Unshelve.
  all: try solve [
    sepcon_assoc_change; cancel
  | normalize; cancel
  | dump_pre_spatial; int_auto
  | dump_pre_spatial; lia
  | dump_pre_spatial; assumption
  | dump_pre_spatial; reflexivity
  | apply derivable1s_coq_prop_r; int_auto
  | apply derivable1s_coq_prop_r; lia
  | apply derivable1s_coq_prop_r;
    let Hmodel_shape := fresh "Hmodel_shape" in
    pose proof Hgraph_model as Hmodel_shape;
    unfold adjacency_matrix_model in Hmodel_shape;
    destruct Hmodel_shape as [[_ Hrow_len] _];
    rewrite (Hrow_len minIndex); lia
  | change (sizeof(PTR)) with ptr_size_Z; sepcon_assoc_change; cancel
  | lia | assumption | reflexivity].
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_13_1_boot : prim_adjacency_matrix_return_matrix_entail_wit_13_1_boot.
Proof.
  left.
  LLM_pre_process ltac:(int_auto).
  Exists l_vertex_parent_2 l_lowcost0_2 l_edge_parent0_2 u_2 v_2
    l_edge_parent0_2 l_visited_2 s_2 s_after_2 l_lowcost0_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [
      sepcon_assoc_change; cancel
    | normalize; cancel
    | dump_pre_spatial; int_auto
    | dump_pre_spatial; lia
    | dump_pre_spatial; assumption
    | dump_pre_spatial; reflexivity
	    | apply derivable1s_coq_prop_r; int_auto
	    | apply derivable1s_coq_prop_r; lia
	    ].
  all: try solve [apply derivable1s_coq_prop_r; apply scan_matrix_row_prefix_update_zero].
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_13_2_boot : prim_adjacency_matrix_return_matrix_entail_wit_13_2_boot.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists l_vertex_parent_2 l_lowcost0_2 l_edge_parent0_2
    l_edge_parent0_2 l_lowcost0_2 l_visited_2 s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [
      sepcon_assoc_change; cancel
    | normalize; cancel
    | dump_pre_spatial; int_auto
    | dump_pre_spatial; lia
    | dump_pre_spatial; assumption
    | dump_pre_spatial; reflexivity
    | apply derivable1s_coq_prop_r; int_auto
    | apply derivable1s_coq_prop_r; lia
    ].
  - apply derivable1s_coq_prop_r.
    apply scan_matrix_row_prefix_update_zero.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_14_1_boot : prim_adjacency_matrix_return_matrix_entail_wit_14_1_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hj_row :
    0 <= j < Zlength (Znth minIndex matrix_low_level_spec nil)) by lia.
  sep_apply (IntArray.full_split_to_missing_i
    row_ptr j (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth minIndex matrix_low_level_spec nil) 0 Hj_row).
	  Exists l_vertex_parent_2 l_lowcost_2 l_edge_parent_2 u_2 v_2
	    l_edge_parent0_2 l_visited_2 s_2 s_after_2 l_lowcost0_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [
      sepcon_assoc_change; cancel
    | normalize; cancel
    | dump_pre_spatial; int_auto
    | dump_pre_spatial; lia
    | dump_pre_spatial; assumption
    | dump_pre_spatial; reflexivity
    | apply derivable1s_coq_prop_r; int_auto
    | apply derivable1s_coq_prop_r; lia
    ].
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_14_2_boot : prim_adjacency_matrix_return_matrix_entail_wit_14_2_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hj_row :
    0 <= j < Zlength (Znth minIndex matrix_low_level_spec nil)) by lia.
  sep_apply_l_atomic (IntArray.full_split_to_missing_i
    row_ptr j (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth minIndex matrix_low_level_spec nil) 0).
  - apply derivable1s_coq_prop_r.
    exact Hj_row.
  - Exists l_vertex_parent_2 l_lowcost_2 l_edge_parent_2
      l_edge_parent0_2 l_lowcost0_2 l_visited_2 s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [
      sepcon_assoc_change; cancel
    | normalize; cancel
    | dump_pre_spatial; int_auto
    | dump_pre_spatial; lia
    | dump_pre_spatial; assumption
    | dump_pre_spatial; reflexivity
    | apply derivable1s_coq_prop_r; int_auto
    | apply derivable1s_coq_prop_r; lia
    ].
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_15_1_boot : prim_adjacency_matrix_return_matrix_entail_wit_15_1_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hj_range : 0 <= j < n_pre) by lia.
  sep_apply (IntArray.full_split_to_missing_i
    visited j n_pre (replace_Znth minIndex 1 l_visited_2) 0 Hj_range).
  sep_apply (IntArray.full_split_to_missing_i
    lowcost j n_pre l_lowcost_2 0 Hj_range).
  sep_apply (IntArray.full_split_to_missing_i
    vertex_parent j n_pre l_vertex_parent_2 (-1) Hj_range).
  Exists l_vertex_parent_2 l_lowcost_2 l_edge_parent_2
    u_2 v_2 l_edge_parent0_2 l_visited_2 s_2 s_after_2 l_lowcost0_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try cancel.
  cancel (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr
    matrix_low_level_spec).
  cancel ((graph_pre + minIndex * sizeof(PTR)) # Ptr |-> row_ptr).
  cancel (IntArray.missing_i row_ptr j 0
    (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth minIndex matrix_low_level_spec nil)).
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_15_2_boot : prim_adjacency_matrix_return_matrix_entail_wit_15_2_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hj_range : 0 <= j < n_pre) by lia.
  sep_apply (IntArray.full_split_to_missing_i
    visited j n_pre (replace_Znth minIndex 1 l_visited_2) 0 Hj_range).
  sep_apply (IntArray.full_split_to_missing_i
    lowcost j n_pre l_lowcost_2 0 Hj_range).
  sep_apply (IntArray.full_split_to_missing_i
    vertex_parent j n_pre l_vertex_parent_2 (-1) Hj_range).
  Exists l_vertex_parent_2 l_lowcost_2 l_edge_parent_2
    l_edge_parent0_2 l_lowcost0_2 l_visited_2 s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try cancel.
  cancel (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr
    matrix_low_level_spec).
  cancel ((graph_pre + minIndex * sizeof(PTR)) # Ptr |-> row_ptr).
  cancel (IntArray.missing_i row_ptr j 0
    (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth minIndex matrix_low_level_spec nil)).
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_16_1_boot : prim_adjacency_matrix_return_matrix_entail_wit_16_1_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrow_len :
    Zlength (Znth minIndex matrix_low_level_spec nil) = n_pre).
  {
    pose proof PreH11 as Hmodel.
    unfold prim_adjacency_matrix_graph_model in Hmodel.
    unfold adjacency_matrix_model in Hmodel.
    destruct Hmodel as [[_ Hrow_len_all] _].
    apply Hrow_len_all; lia.
  }
  assert (Hj_row :
    0 <= j < Zlength (Znth minIndex matrix_low_level_spec nil)) by
    (rewrite Hrow_len; lia).
  subst w.
  sep_apply (int_array_missing_store_merge_to_full
    selected_row j
    (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
    (Znth minIndex matrix_low_level_spec nil)); try exact Hj_row.
  rewrite replace_Znth_Znth by exact Hj_row.
  sep_apply (IntArray.missing_i_merge_to_full
    visited j n_pre
    (Znth j (replace_Znth minIndex 1 l_visited_2) 0)
    (replace_Znth minIndex 1 l_visited_2)); try lia.
  rewrite replace_Znth_Znth by lia.
  prop_apply (IntArray.missing_i_Zlength lowcost j 0 n_pre l_lowcost_2).
  Intros.
  assert (Hlowcost2_len : Zlength l_lowcost_2 = n_pre) by lia.
  sep_apply (IntArray.missing_i_merge_to_full
    lowcost j n_pre (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
    l_lowcost_2); try lia.
  prop_apply (IntArray.missing_i_Zlength vertex_parent j 0 n_pre l_vertex_parent_2).
  Intros.
  assert (Hvertex_parent_len : Zlength l_vertex_parent_2 = n_pre) by lia.
  sep_apply (IntArray.missing_i_merge_to_full
    vertex_parent j n_pre minIndex l_vertex_parent_2); try lia.
  assert (Hmin_bounds : INT_MIN <= min /\ min <= INT_MAX).
  {
    rewrite PreH20.
    split; int_auto.
  }
  assert (Hj_graph : In j (graph_vertices g_low_level_spec)).
  {
    pose proof PreH11 as Hmodel.
    unfold prim_adjacency_matrix_graph_model in Hmodel.
    eapply adjacency_matrix_vertex_in_graph; eauto; lia.
  }
  assert (Hj_not_state : ~ graph_basic.vvalid s_after_2.(Prim.graph_in_state) j).
  {
    intro Hv_valid.
    destruct (PreH24 j Hj_graph) as [_ Hvalid_to_visited].
    apply Hvalid_to_visited in Hv_valid.
    apply Hv_valid. exact PreH2.
  }
  assert (HminIndex_neq_j : minIndex <> j).
  {
    intro Heq.
    subst j.
    rewrite Znth_replace_Znth_Same in PreH2.
    - lia.
    - rewrite PreH30.
      unfold repeat_Z.
      rewrite Zlength_correct, repeat_length.
      rewrite Z2Nat.id by lia.
      lia.
  }
  assert (Hvalue_bound :
    0 <= Znth j (Znth minIndex matrix_low_level_spec nil) 0 <= 1000000000).
  {
    pose proof PreH11 as Hmodel_entry.
    unfold prim_adjacency_matrix_graph_model in Hmodel_entry.
    unfold adjacency_matrix_model in Hmodel_entry.
    destruct Hmodel_entry as [_ [_ [Hentry _]]].
    specialize (Hentry minIndex j ltac:(lia) ltac:(lia)).
    unfold matrix_entry in Hentry.
    destruct Hentry as [Heq | Hrange].
    - exfalso. apply PreH4. exact Heq.
    - lia.
  }
  assert (Hlowcost2_bound :
    forall k, 0 <= k < n_pre -> 0 <= Znth k l_lowcost_2 0 <= 1000000000).
  {
    intros k Hk. apply PreH34. rewrite Hlowcost2_len. exact Hk.
  }
  assert (Hgraph_vertices_range :
    forall v, In v (graph_vertices g_low_level_spec) -> 0 <= v < Zlength l_lowcost_2).
  {
    intros v Hv.
    rewrite Hlowcost2_len.
    pose proof PreH11 as Hmodel_vertices.
    unfold prim_adjacency_matrix_graph_model in Hmodel_vertices.
    unfold adjacency_matrix_model in Hmodel_vertices.
    destruct Hmodel_vertices as [_ [Hvertices _]].
    rewrite Hvertices in Hv.
    rewrite <- SumLib.ZRange.In_Zrange in Hv.
    lia.
  }
  Exists (replace_Znth j minIndex l_vertex_parent_2)
    (replace_Znth j (Znth j (Znth minIndex matrix_low_level_spec nil) 0) l_lowcost_2)
    (replace_Znth j (undirected_edge minIndex j) l_edge_parent_2)
    l_edge_parent0_2 l_lowcost0_2 l_visited_2 s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (apply derivable1s_coq_prop_r; destruct Hmin_bounds; lia);
    try (apply derivable1s_coq_prop_r;
      unfold lowcost_values_in_range; intros k Hk;
      destruct (Z.eq_dec k j) as [-> | Hneq];
      [ rewrite Znth_replace_Znth_same_local;
        [ exact Hvalue_bound | rewrite Hlowcost2_len; lia ]
      | rewrite Znth_replace_Znth_diff_local;
        [ apply Hlowcost2_bound; exact Hk
        | rewrite Hlowcost2_len; lia
        | rewrite Hlowcost2_len; lia
        | lia ] ]);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [cancel].
  - apply derivable1s_coq_prop_r.
	    eapply scan_matrix_row_prefix_update_snoc.
	    + lia.
	    + exact PreH31.
	    + apply scan_one_matrix_neighbor_update_take with (n := n_pre).
	      * pose proof PreH11 as Hmodel.
          unfold prim_adjacency_matrix_graph_model in Hmodel.
          exact Hmodel.
	      * lia.
	      * lia.
      * exact Hj_not_state.
      * unfold matrix_entry. exact PreH4.
      * unfold matrix_entry. exact PreH1.
  - apply derivable1s_coq_prop_r.
	    eapply (vertex_parent_matches_edge_parent_update_matrix
	      n_pre matrix_low_level_spec g_low_level_spec 1000000000
	      src_low_level_spec l_vertex_parent_2 l_edge_parent_2 minIndex j).
	    + pose proof PreH11 as Hmodel.
        unfold prim_adjacency_matrix_graph_model in Hmodel.
        exact Hmodel.
	    + exact PreH32.
    + lia.
    + lia.
    + exact HminIndex_neq_j.
    + intro Hjsrc.
      apply HminIndex_neq_j.
      lia.
    + unfold matrix_entry. exact PreH4.
  - apply derivable1s_coq_prop_r.
	    eapply lowcost_sum_matches_state_replace_outside
	      with (g := g_low_level_spec) (bound := 1000000000).
	    + exact PreH23.
    + exact Hj_not_state.
    + rewrite Hlowcost2_len; lia.
    + exact Hvalue_bound.
	    + rewrite Hlowcost2_len; exact PreH16.
    + exact Hgraph_vertices_range.
    + intros v Hv. apply Hlowcost2_bound. rewrite Hlowcost2_len in Hv. exact Hv.
	    + exact PreH33.
  - apply derivable1s_coq_prop_r.
    unfold lowcost_values_in_range; intros k Hk.
    rewrite Zlength_replace_Znth_local in Hk.
    destruct (Z.eq_dec k j) as [-> | Hneq].
    + rewrite Znth_replace_Znth_same_local by lia.
      exact Hvalue_bound.
    + rewrite Znth_replace_Znth_diff_local by
        (try lia; intro Heq; apply Hneq; symmetry; exact Heq).
	      apply PreH34. lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_16_2_boot : prim_adjacency_matrix_return_matrix_entail_wit_16_2_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrow_len :
    Zlength (Znth minIndex matrix_low_level_spec nil) = n_pre).
  {
    pose proof PreH11 as Hmodel.
    unfold prim_adjacency_matrix_graph_model in Hmodel.
    unfold adjacency_matrix_model in Hmodel.
    destruct Hmodel as [[_ Hrow_len_all] _].
    apply Hrow_len_all; lia.
  }
  assert (Hj_row :
    0 <= j < Zlength (Znth minIndex matrix_low_level_spec nil)) by
    (rewrite Hrow_len; lia).
  subst w.
  prop_apply (IntArray.missing_i_Zlength visited j 0 n_pre
    (replace_Znth minIndex 1 l_visited_2)).
  Intros.
  assert (Hvisited2_len : Zlength l_visited_2 = n_pre).
  { rewrite <- (@Zlength_replace_Znth Z l_visited_2 minIndex 1). lia. }
  sep_apply (int_array_missing_store_merge_to_full
    selected_row j
    (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
    (Znth minIndex matrix_low_level_spec nil)); try exact Hj_row.
  rewrite replace_Znth_Znth by exact Hj_row.
  sep_apply (IntArray.missing_i_merge_to_full
    visited j n_pre
    (Znth j (replace_Znth minIndex 1 l_visited_2) 0)
    (replace_Znth minIndex 1 l_visited_2)); try lia.
  rewrite replace_Znth_Znth by lia.
  prop_apply (IntArray.missing_i_Zlength lowcost j 0 n_pre l_lowcost_2).
  Intros.
  assert (Hlowcost2_len : Zlength l_lowcost_2 = n_pre) by lia.
  sep_apply (IntArray.missing_i_merge_to_full
    lowcost j n_pre (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
    l_lowcost_2); try lia.
  prop_apply (IntArray.missing_i_Zlength vertex_parent j 0 n_pre l_vertex_parent_2).
  Intros.
  assert (Hvertex_parent_len : Zlength l_vertex_parent_2 = n_pre) by lia.
  sep_apply (IntArray.missing_i_merge_to_full
    vertex_parent j n_pre minIndex l_vertex_parent_2); try lia.
  assert (Hmin_bounds : INT_MIN <= min /\ min <= INT_MAX).
  {
    rewrite PreH20.
    pose proof (selected_parent_lowcost_bounds
      n_pre matrix_low_level_spec g_low_level_spec s_2
      l_lowcost0_2 l_edge_parent0_2 1000000000
      minIndex u_2 v_2
      ltac:(pose proof PreH11 as Hmodel;
            unfold prim_adjacency_matrix_graph_model in Hmodel;
            exact Hmodel)
      PreH26 PreH28 ltac:(lia)) as Hbounds.
    split; lia.
  }
  assert (Hj_graph : In j (graph_vertices g_low_level_spec)).
  {
    pose proof PreH11 as Hmodel.
    unfold prim_adjacency_matrix_graph_model in Hmodel.
    eapply adjacency_matrix_vertex_in_graph; eauto; lia.
  }
  assert (Hj_not_state : ~ graph_basic.vvalid s_after_2.(Prim.graph_in_state) j).
  {
    intro Hv_valid.
    destruct (PreH31 j Hj_graph) as [_ Hvalid_to_visited].
    apply Hvalid_to_visited in Hv_valid.
    apply Hv_valid. exact PreH2.
  }
  assert (HminIndex_neq_j : minIndex <> j).
  {
    intro Heq.
    subst j.
    rewrite Znth_replace_Znth_Same in PreH2 by (rewrite Hvisited2_len; lia).
    lia.
  }
  assert (Hvalue_bound :
    0 <= Znth j (Znth minIndex matrix_low_level_spec nil) 0 <= 1000000000).
  {
    pose proof PreH11 as Hmodel_entry.
    unfold prim_adjacency_matrix_graph_model in Hmodel_entry.
    unfold adjacency_matrix_model in Hmodel_entry.
    destruct Hmodel_entry as [_ [_ [Hentry _]]].
    specialize (Hentry minIndex j ltac:(lia) ltac:(lia)).
    unfold matrix_entry in Hentry.
    destruct Hentry as [Heq | Hrange].
    - exfalso. apply PreH4. exact Heq.
    - lia.
  }
  assert (Hlowcost2_bound :
    forall k, 0 <= k < n_pre -> 0 <= Znth k l_lowcost_2 0 <= 1000000000).
  {
    intros k Hk. apply PreH39. rewrite Hlowcost2_len. exact Hk.
  }
  assert (Hgraph_vertices_range :
    forall v, In v (graph_vertices g_low_level_spec) -> 0 <= v < Zlength l_lowcost_2).
  {
    intros v Hv.
    rewrite Hlowcost2_len.
    pose proof PreH11 as Hmodel_vertices.
    unfold prim_adjacency_matrix_graph_model in Hmodel_vertices.
    unfold adjacency_matrix_model in Hmodel_vertices.
    destruct Hmodel_vertices as [_ [Hvertices _]].
    rewrite Hvertices in Hv.
    rewrite <- SumLib.ZRange.In_Zrange in Hv.
    lia.
  }
  Exists (replace_Znth j minIndex l_vertex_parent_2)
    (replace_Znth j (Znth j (Znth minIndex matrix_low_level_spec nil) 0) l_lowcost_2)
    (replace_Znth j (undirected_edge minIndex j) l_edge_parent_2)
    u_2 v_2 l_edge_parent0_2 l_visited_2 s_2 s_after_2 l_lowcost0_2.
  repeat (split_pure_spatial || split_pures);
    try (apply derivable1s_coq_prop_r; destruct Hmin_bounds; lia);
    try (apply derivable1s_coq_prop_r;
      unfold lowcost_values_in_range; intros k Hk;
      destruct (Z.eq_dec k j) as [-> | Hneq];
      [ rewrite Znth_replace_Znth_same_local;
        [ exact Hvalue_bound | rewrite Hlowcost2_len; lia ]
      | rewrite Znth_replace_Znth_diff_local;
        [ apply Hlowcost2_bound; exact Hk
        | rewrite Hlowcost2_len; lia
        | rewrite Hlowcost2_len; lia
        | lia ] ]);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [cancel].
  - apply derivable1s_coq_prop_r.
	    eapply scan_matrix_row_prefix_update_snoc.
	    + lia.
	    + exact PreH36.
	    + apply scan_one_matrix_neighbor_update_take with (n := n_pre).
	      * pose proof PreH11 as Hmodel.
          unfold prim_adjacency_matrix_graph_model in Hmodel.
          exact Hmodel.
      * lia.
      * lia.
      * exact Hj_not_state.
      * unfold matrix_entry. exact PreH4.
      * unfold matrix_entry. exact PreH1.
  - apply derivable1s_coq_prop_r.
	    eapply (vertex_parent_matches_edge_parent_update_matrix
	      n_pre matrix_low_level_spec g_low_level_spec 1000000000
	      src_low_level_spec l_vertex_parent_2 l_edge_parent_2 minIndex j).
	    + pose proof PreH11 as Hmodel.
        unfold prim_adjacency_matrix_graph_model in Hmodel.
        exact Hmodel.
	    + exact PreH37.
    + lia.
    + lia.
    + exact HminIndex_neq_j.
    + intro Hjsrc.
      apply Hj_not_state.
	      destruct PreH33 as [Hsrc_valid _].
	      rewrite Hjsrc.
	      exact Hsrc_valid.
    + unfold matrix_entry. exact PreH4.
  - apply derivable1s_coq_prop_r.
	    eapply lowcost_sum_matches_state_replace_outside
	      with (g := g_low_level_spec) (bound := 1000000000).
	    + exact PreH30.
    + exact Hj_not_state.
    + rewrite Hlowcost2_len; lia.
    + exact Hvalue_bound.
	    + rewrite Hlowcost2_len. exact PreH16.
    + exact Hgraph_vertices_range.
    + intros v Hv. apply Hlowcost2_bound. rewrite Hlowcost2_len in Hv. exact Hv.
	    + exact PreH38.
  - apply derivable1s_coq_prop_r.
    unfold lowcost_values_in_range; intros k Hk.
    rewrite Zlength_replace_Znth_local in Hk.
    destruct (Z.eq_dec k j) as [-> | Hneq].
    + rewrite Znth_replace_Znth_same_local by lia.
      exact Hvalue_bound.
    + rewrite Znth_replace_Znth_diff_local by
        (try lia; intro Heq; apply Hneq; symmetry; exact Heq).
	      apply PreH39. lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_16_3_boot : prim_adjacency_matrix_return_matrix_entail_wit_16_3_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrow_len :
    Zlength (Znth minIndex matrix_low_level_spec nil) = n_pre).
  {
    pose proof PreH11 as Hmodel.
    unfold prim_adjacency_matrix_graph_model in Hmodel.
    unfold adjacency_matrix_model in Hmodel.
    destruct Hmodel as [[_ Hrow_len_all] _].
    apply Hrow_len_all; lia.
  }
  assert (Hj_row :
    0 <= j < Zlength (Znth minIndex matrix_low_level_spec nil)) by
    (rewrite Hrow_len; lia).
  subst w.
  sep_apply (int_array_missing_store_merge_to_full
    selected_row j
    (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
    (Znth minIndex matrix_low_level_spec nil)); try exact Hj_row.
  rewrite replace_Znth_Znth by exact Hj_row.
  sep_apply (IntArray.missing_i_merge_to_full
    visited j n_pre
    (Znth j (replace_Znth minIndex 1 l_visited_2) 0)
    (replace_Znth minIndex 1 l_visited_2)); try lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply (IntArray.missing_i_merge_to_full
    lowcost j n_pre (Znth j l_lowcost_2 0) l_lowcost_2); try lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply (IntArray.missing_i_merge_to_full
    vertex_parent j n_pre (Znth j l_vertex_parent_2 (-1)) l_vertex_parent_2); try lia.
  rewrite replace_Znth_Znth by lia.
  Exists l_vertex_parent_2 l_lowcost_2 l_edge_parent_2
    l_edge_parent0_2 l_lowcost0_2 l_visited_2 s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [cancel].
  - apply derivable1s_coq_prop_r.
	    eapply scan_matrix_row_prefix_update_snoc.
	    + lia.
	    + exact PreH31.
    + apply scan_one_matrix_neighbor_update_skip.
      right; right.
      unfold matrix_entry.
      lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_16_4_boot : prim_adjacency_matrix_return_matrix_entail_wit_16_4_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hadj_model :
    adjacency_matrix_model n_pre matrix_low_level_spec g_low_level_spec 1000000000).
  {
    match goal with
    | H : prim_adjacency_matrix_graph_model n_pre g_low_level_spec
          1000000000 matrix_low_level_spec |- _ =>
        pose proof H as Hmodel;
        unfold prim_adjacency_matrix_graph_model in Hmodel;
        exact Hmodel
    end.
  }
  assert (Hrow_len :
    Zlength (Znth minIndex matrix_low_level_spec nil) = n_pre).
  {
    pose proof Hadj_model as Hmodel.
    unfold adjacency_matrix_model in Hmodel.
    destruct Hmodel as [[_ Hrow_len_all] _].
    apply Hrow_len_all; lia.
  }
  assert (Hj_row :
    0 <= j < Zlength (Znth minIndex matrix_low_level_spec nil)) by
    (rewrite Hrow_len; lia).
  subst w.
  sep_apply (int_array_missing_store_merge_to_full
    selected_row j
    (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
    (Znth minIndex matrix_low_level_spec nil)); try exact Hj_row.
  rewrite replace_Znth_Znth by exact Hj_row.
  sep_apply (IntArray.missing_i_merge_to_full
    visited j n_pre
    (Znth j (replace_Znth minIndex 1 l_visited_2) 0)
    (replace_Znth minIndex 1 l_visited_2)); try lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply (IntArray.missing_i_merge_to_full
    lowcost j n_pre (Znth j l_lowcost_2 0) l_lowcost_2); try lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply (IntArray.missing_i_merge_to_full
    vertex_parent j n_pre (Znth j l_vertex_parent_2 (-1)) l_vertex_parent_2); try lia.
  rewrite replace_Znth_Znth by lia.
  assert (Hmin_bounds : INT_MIN <= min /\ min <= INT_MAX).
  {
    match goal with
    | Hmin : min = Znth minIndex l_lowcost0_2 0,
      Hmatch : lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2
                 l_edge_parent0_2 1000000000,
      Hpair : selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2
                minIndex u_2 v_2 |- _ =>
        rewrite Hmin;
        pose proof (selected_parent_lowcost_bounds
          n_pre matrix_low_level_spec g_low_level_spec s_2
          l_lowcost0_2 l_edge_parent0_2 1000000000
          minIndex u_2 v_2 Hadj_model Hmatch Hpair ltac:(lia)) as Hbounds;
        split; lia
    end.
  }
  Exists l_vertex_parent_2 l_lowcost_2 l_edge_parent_2
    u_2 v_2 l_edge_parent0_2 l_visited_2 s_2 s_after_2 l_lowcost0_2.
  repeat (split_pure_spatial || split_pures);
    try (apply derivable1s_coq_prop_r; destruct Hmin_bounds; lia);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [cancel].
  - apply derivable1s_coq_prop_r.
    eapply scan_matrix_row_prefix_update_snoc.
    + lia.
    + match goal with
      | Hscan : scan_matrix_row_prefix_update g_low_level_spec
          matrix_low_level_spec 1000000000 s_after_2 minIndex j
          l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 |- _ =>
          exact Hscan
      end.
    + apply scan_one_matrix_neighbor_update_skip.
      right; right.
      unfold matrix_entry.
      lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_16_5_boot : prim_adjacency_matrix_return_matrix_entail_wit_16_5_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hadj_model :
    adjacency_matrix_model n_pre matrix_low_level_spec g_low_level_spec 1000000000).
  {
    match goal with
    | H : prim_adjacency_matrix_graph_model n_pre g_low_level_spec
          1000000000 matrix_low_level_spec |- _ =>
        pose proof H as Hmodel;
        unfold prim_adjacency_matrix_graph_model in Hmodel;
        exact Hmodel
    end.
  }
  assert (Hrow_len :
    Zlength (Znth minIndex matrix_low_level_spec nil) = n_pre).
  {
    pose proof Hadj_model as Hmodel.
    unfold adjacency_matrix_model in Hmodel.
    destruct Hmodel as [[_ Hrow_len_all] _].
    apply Hrow_len_all; lia.
  }
  assert (Hj_row :
    0 <= j < Zlength (Znth minIndex matrix_low_level_spec nil)) by
    (rewrite Hrow_len; lia).
  subst w.
  sep_apply (int_array_missing_store_merge_to_full
    selected_row j
    (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
    (Znth minIndex matrix_low_level_spec nil)); try exact Hj_row.
  rewrite replace_Znth_Znth by exact Hj_row.
  sep_apply (IntArray.missing_i_merge_to_full
    visited j n_pre
    (Znth j (replace_Znth minIndex 1 l_visited_2) 0)
    (replace_Znth minIndex 1 l_visited_2)); try lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply (IntArray.missing_i_merge_to_full
    lowcost j n_pre (Znth j l_lowcost_2 0) l_lowcost_2); try lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply (IntArray.missing_i_merge_to_full
    vertex_parent j n_pre (Znth j l_vertex_parent_2 (-1)) l_vertex_parent_2); try lia.
  rewrite replace_Znth_Znth by lia.
  assert (Hmin_bounds : INT_MIN <= min /\ min <= INT_MAX).
  {
    match goal with
    | Hmin : min = Znth minIndex l_lowcost0_2 0,
      Hmatch : lowcost_parent_match g_low_level_spec s_2 l_lowcost0_2
                 l_edge_parent0_2 1000000000,
      Hpair : selected_parent_pair g_low_level_spec s_2 l_edge_parent0_2
                minIndex u_2 v_2 |- _ =>
        rewrite Hmin;
        pose proof (selected_parent_lowcost_bounds
          n_pre matrix_low_level_spec g_low_level_spec s_2
          l_lowcost0_2 l_edge_parent0_2 1000000000
          minIndex u_2 v_2 Hadj_model Hmatch Hpair ltac:(lia)) as Hbounds;
        split; lia
    end.
  }
  Exists l_vertex_parent_2 l_lowcost_2 l_edge_parent_2
    u_2 v_2 l_edge_parent0_2 l_visited_2 s_2 s_after_2 l_lowcost0_2.
  repeat (split_pure_spatial || split_pures);
    try (apply derivable1s_coq_prop_r; destruct Hmin_bounds; lia);
    try (apply derivable1s_coq_prop_r; subst; assumption);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [cancel].
  - apply derivable1s_coq_prop_r.
    eapply scan_matrix_row_prefix_update_snoc.
    + lia.
    + match goal with
      | Hscan : scan_matrix_row_prefix_update g_low_level_spec
          matrix_low_level_spec 1000000000 s_after_2 minIndex j
          l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 |- _ =>
          exact Hscan
      end.
    + apply scan_one_matrix_neighbor_update_skip.
      left.
      assert (Hj_graph : In j (graph_vertices g_low_level_spec)).
      {
        eapply adjacency_matrix_vertex_in_graph; eauto; lia.
      }
      match goal with
      | Hvisited : visited_matches_state g_low_level_spec s_after_2
          (replace_Znth minIndex 1 l_visited_2) |- _ =>
          destruct (Hvisited j Hj_graph) as [Hvisited_to_valid _];
          apply Hvisited_to_valid;
          exact PreH1
      end.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_16_6_boot : prim_adjacency_matrix_return_matrix_entail_wit_16_6_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hadj_model :
    adjacency_matrix_model n_pre matrix_low_level_spec g_low_level_spec 1000000000).
  {
    match goal with
    | H : prim_adjacency_matrix_graph_model n_pre g_low_level_spec
          1000000000 matrix_low_level_spec |- _ =>
        pose proof H as Hmodel;
        unfold prim_adjacency_matrix_graph_model in Hmodel;
        exact Hmodel
    end.
  }
  assert (Hrow_len :
    Zlength (Znth minIndex matrix_low_level_spec nil) = n_pre).
  {
    pose proof Hadj_model as Hmodel.
    unfold adjacency_matrix_model in Hmodel.
    destruct Hmodel as [[_ Hrow_len_all] _].
    apply Hrow_len_all; lia.
  }
  assert (Hj_row :
    0 <= j < Zlength (Znth minIndex matrix_low_level_spec nil)) by
    (rewrite Hrow_len; lia).
  subst w.
  sep_apply (int_array_missing_store_merge_to_full
    selected_row j
    (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
    (Znth minIndex matrix_low_level_spec nil)); try exact Hj_row.
  rewrite replace_Znth_Znth by exact Hj_row.
  sep_apply (IntArray.missing_i_merge_to_full
    visited j n_pre
    (Znth j (replace_Znth minIndex 1 l_visited_2) 0)
    (replace_Znth minIndex 1 l_visited_2)); try lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply (IntArray.missing_i_merge_to_full
    lowcost j n_pre (Znth j l_lowcost_2 0) l_lowcost_2); try lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply (IntArray.missing_i_merge_to_full
    vertex_parent j n_pre (Znth j l_vertex_parent_2 (-1)) l_vertex_parent_2); try lia.
  rewrite replace_Znth_Znth by lia.
  Exists l_vertex_parent_2 l_lowcost_2 l_edge_parent_2
    l_edge_parent0_2 l_lowcost0_2 l_visited_2 s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (apply derivable1s_coq_prop_r; subst; assumption);
    try (dump_pre_spatial; subst; assumption);
    try (dump_pre_spatial; subst; lia);
    try solve [cancel].
  - apply derivable1s_coq_prop_r.
    exact PreH20.
  - apply derivable1s_coq_prop_r.
    exact PreH27.
  - apply derivable1s_coq_prop_r.
    exact PreH28.
  - apply derivable1s_coq_prop_r.
    exact PreH29.
  - apply derivable1s_coq_prop_r.
    eapply scan_matrix_row_prefix_update_snoc.
    + lia.
    + match goal with
      | Hscan : scan_matrix_row_prefix_update g_low_level_spec
          matrix_low_level_spec 1000000000 s_after_2 minIndex j
          l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 |- _ =>
          exact Hscan
      end.
    + apply scan_one_matrix_neighbor_update_skip.
      left.
      assert (Hj_graph : In j (graph_vertices g_low_level_spec)).
      {
        eapply adjacency_matrix_vertex_in_graph; eauto; lia.
      }
      match goal with
      | Hvisited : visited_matches_state g_low_level_spec s_after_2
          (replace_Znth minIndex 1 l_visited_2) |- _ =>
          destruct (Hvisited j Hj_graph) as [Hvisited_to_valid _];
          apply Hvisited_to_valid;
          exact PreH1
      end.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_16_7_boot : prim_adjacency_matrix_return_matrix_entail_wit_16_7_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply (int_array_missing_store_merge_to_full
    row_ptr j
    (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
    (Znth minIndex matrix_low_level_spec nil)); try lia.
  rewrite replace_Znth_Znth by lia.
  Exists l_vertex_parent_2 l_lowcost_2 l_edge_parent_2
    u_2 v_2 l_edge_parent0_2 l_visited_2 s_2 s_after_2 l_lowcost0_2.
  repeat (split_pure_spatial || split_pures);
    try (apply derivable1s_coq_prop_r; subst; assumption);
    try (dump_pre_spatial; subst; assumption);
    try (dump_pre_spatial; subst; lia);
    try solve [cancel].
  - cancel (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr
      matrix_low_level_spec).
    cancel ((graph_pre + minIndex * sizeof(PTR)) # Ptr |-> row_ptr).
    cancel (IntArray.full row_ptr
      (Zlength (Znth minIndex matrix_low_level_spec nil))
      (Znth minIndex matrix_low_level_spec nil)).
    try cancel (IntArray.full visited n_pre (replace_Znth minIndex 1 l_visited_2)).
    try cancel (IntArray.full lowcost n_pre l_lowcost_2).
    try cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
  - apply derivable1s_coq_prop_r.
    eapply scan_matrix_row_prefix_update_snoc.
    + lia.
    + match goal with
      | Hscan : scan_matrix_row_prefix_update g_low_level_spec
          matrix_low_level_spec 1000000000 s_after_2 minIndex j
          l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 |- _ =>
          exact Hscan
      end.
    + apply scan_one_matrix_neighbor_update_skip.
      right; left.
      unfold matrix_entry.
      lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_16_8_boot : prim_adjacency_matrix_return_matrix_entail_wit_16_8_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply (int_array_missing_store_merge_to_full
    row_ptr j
    (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
    (Znth minIndex matrix_low_level_spec nil)); try lia.
  rewrite replace_Znth_Znth by lia.
  Exists l_vertex_parent_2 l_lowcost_2 l_edge_parent_2
    l_edge_parent0_2 l_lowcost0_2 l_visited_2 s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (apply derivable1s_coq_prop_r; subst; assumption);
    try (dump_pre_spatial; subst; assumption);
    try (dump_pre_spatial; subst; lia);
    try solve [cancel].
  - cancel (IntPtrArray2.missing_i graph_pre n_pre minIndex row_ptr
      matrix_low_level_spec).
    cancel ((graph_pre + minIndex * sizeof(PTR)) # Ptr |-> row_ptr).
    cancel (IntArray.full row_ptr
      (Zlength (Znth minIndex matrix_low_level_spec nil))
      (Znth minIndex matrix_low_level_spec nil)).
    cancel (IntArray.full visited n_pre (replace_Znth minIndex 1 l_visited_2)).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
  - apply derivable1s_coq_prop_r.
    exact PreH29.
  - apply derivable1s_coq_prop_r.
    exact PreH36.
  - apply derivable1s_coq_prop_r.
    exact PreH37.
  - apply derivable1s_coq_prop_r.
    exact PreH38.
  - apply derivable1s_coq_prop_r.
    eapply scan_matrix_row_prefix_update_snoc.
    + lia.
    + match goal with
      | Hscan : scan_matrix_row_prefix_update g_low_level_spec
          matrix_low_level_spec 1000000000 s_after_2 minIndex j
          l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2 |- _ =>
          exact Hscan
      end.
    + apply scan_one_matrix_neighbor_update_skip.
      right; left.
      unfold matrix_entry.
      lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_17_1_boot : prim_adjacency_matrix_return_matrix_entail_wit_17_1_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hj_eq : j = n_pre) by lia.
  subst j.
  assert (Hadj_model :
    adjacency_matrix_model n_pre matrix_low_level_spec g_low_level_spec 1000000000).
  {
    pose proof PreH9 as Hmodel.
    unfold prim_adjacency_matrix_graph_model in Hmodel.
    exact Hmodel.
  }
  assert (Hscan_full :
    scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec
      1000000000 s_after_2 minIndex l_lowcost0_2 l_edge_parent0_2
      l_lowcost_2 l_edge_parent_2).
  {
    unfold scan_matrix_row_full_update, scan_matrix_row_prefix_update.
    exact PreH36.
  }
  sep_apply_l_atomic (int_ptr_array2_missing_store_row_merge_to_full
    graph_pre minIndex n_pre row_ptr matrix_low_level_spec
    (Znth minIndex matrix_low_level_spec nil)).
  - apply derivable1s_coq_prop_r; lia.
  -
  rewrite replace_Znth_Znth by lia.
  Exists l_edge_parent0_2 l_lowcost_2 l_vertex_parent_2 l_edge_parent_2
    l_visited_2 s_after_2 l_lowcost0_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [cancel].
  + sep_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_intro n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel ((&( "j" )) # Int |-> n_pre).
    cancel (IntArray.full visited n_pre (replace_Znth minIndex 1 l_visited_2)).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
    qcp_light_sep.
    unfold prim_adjacency_matrix_graph_model; exact Hadj_model.
  + apply derivable1s_coq_prop_r.
    pose proof Hscan_full as Hscan_update.
    unfold scan_matrix_row_full_update, scan_matrix_row_prefix_update in Hscan_update.
    eapply scan_matrix_row_update_selected_edges_match_state.
    * exact PreH33.
    * intros cur Hcur.
      pose proof PreH26 as Hmatch_before.
      destruct Hmatch_before as [Hrange _].
      exact (Hrange cur Hcur).
    * intros cur Hcur.
      rewrite <- SumLib.ZRange.In_Zrange in Hcur.
      eapply adjacency_matrix_vertex_in_graph; eauto.
    * exact Hscan_update.
  + apply derivable1s_coq_prop_r.
    eapply scan_matrix_row_full_update_lowcost_parent_match_after_add.
    * exact Hadj_model.
    * exact PreH26.
    * exact PreH29.
    * exact Hscan_full.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_17_2_boot : prim_adjacency_matrix_return_matrix_entail_wit_17_2_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hj_eq : j = n_pre) by lia.
  subst j.
  assert (Hadj_model :
    adjacency_matrix_model n_pre matrix_low_level_spec g_low_level_spec 1000000000).
  {
    pose proof PreH9 as Hmodel.
    unfold prim_adjacency_matrix_graph_model in Hmodel.
    exact Hmodel.
  }
  assert (Hscan_full_init :
    scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec
      1000000000 (initSt g_low_level_spec src_low_level_spec) src_low_level_spec
      (replace_Znth src_low_level_spec 0 (repeat_Z 1000000000 n_pre))
      (default_edge_list n_pre) l_lowcost_2 l_edge_parent_2).
  {
    pose proof PreH31 as Hscan.
    unfold scan_matrix_row_full_update, scan_matrix_row_prefix_update in Hscan.
    rewrite PreH19 in Hscan.
    rewrite PreH28 in Hscan.
    rewrite PreH29 in Hscan.
    unfold scan_matrix_row_full_update, scan_matrix_row_prefix_update.
    rewrite <- PreH21.
    rewrite PreH10.
    exact Hscan.
  }
  sep_apply_l_atomic (int_ptr_array2_missing_store_row_merge_to_full
    graph_pre minIndex n_pre row_ptr matrix_low_level_spec
    (Znth minIndex matrix_low_level_spec nil)).
  - apply derivable1s_coq_prop_r; lia.
  -
  rewrite replace_Znth_Znth by lia.
  Exists l_edge_parent0_2 l_lowcost_2 l_vertex_parent_2 l_edge_parent_2
    l_visited_2 s_after_2 l_lowcost0_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [cancel].
  + sep_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_intro n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel ((&( "j" )) # Int |-> n_pre).
    cancel (IntArray.full visited n_pre (replace_Znth minIndex 1 l_visited_2)).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
    qcp_light_sep.
    match goal with
    | H : prim_adjacency_matrix_graph_model n_pre g_low_level_spec
          1000000000 matrix_low_level_spec |- _ =>
        pose proof H as Hmodel;
        unfold prim_adjacency_matrix_graph_model in Hmodel;
        exact Hmodel
    end.
  Unshelve.
  + apply derivable1s_coq_prop_r.
    rewrite PreH21.
    pose proof Hscan_full_init as Hscan_update.
    unfold scan_matrix_row_full_update, scan_matrix_row_prefix_update in Hscan_update.
    eapply scan_matrix_row_update_selected_edges_match_state.
    * apply initSt_selected_edges_match_state.
    * intros cur Hcur.
      assert (Hcur_range : 0 <= cur < n_pre).
      {
        pose proof Hadj_model as Hmodel.
        unfold adjacency_matrix_model in Hmodel.
        destruct Hmodel as [_ [Hvertices _]].
        apply Hvertices in Hcur.
        rewrite <- SumLib.ZRange.In_Zrange in Hcur.
        exact Hcur.
      }
      assert (Hn_nonneg : 0 <= n_pre) by lia.
      split.
      -- rewrite Zlength_replace_Znth_local.
        unfold repeat_Z.
        rewrite Zlength_correct, repeat_length.
        rewrite Z2Nat.id by exact Hn_nonneg.
        lia.
      -- unfold default_edge_list.
        rewrite Zlength_correct, repeat_length.
        rewrite Z2Nat.id by exact Hn_nonneg.
        lia.
    * intros cur Hcur.
      rewrite <- SumLib.ZRange.In_Zrange in Hcur.
      eapply adjacency_matrix_vertex_in_graph; eauto.
    * exact Hscan_update.
  + apply derivable1s_coq_prop_r.
    rewrite PreH21.
    eapply scan_matrix_row_full_update_lowcost_parent_match_init.
    * exact Hadj_model.
    * exact PreH10.
    * exact PreH11.
    * exact Hscan_full_init.
  + apply derivable1s_coq_prop_r.
    replace i with 0 by lia.
    exact PreH22.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_18_1_boot : prim_adjacency_matrix_return_matrix_entail_wit_18_1_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists l_lowcost_2 l_vertex_parent_2 l_edge_parent_2
    (replace_Znth minIndex 1 l_visited_2) s_after_2.
  split_pure_spatial.
  - cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (IntArray.full visited n_pre
      (replace_Znth minIndex 1 l_visited_2)).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
  - split_pures; dump_pre_spatial; eauto; lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_18_2_boot : prim_adjacency_matrix_return_matrix_entail_wit_18_2_boot.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists l_lowcost_2 l_vertex_parent_2 l_edge_parent_2
    (replace_Znth minIndex 1 l_visited_2) s_after_2.
  split_pure_spatial.
  - cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (IntArray.full visited n_pre
      (replace_Znth minIndex 1 l_visited_2)).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
  - split_pures; dump_pre_spatial; eauto; lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_19_1_running : prim_adjacency_matrix_return_matrix_entail_wit_19_1_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists l_lowcost_3 l_vertex_parent_3 l_edge_parent_3 l_visited_3 s_2.
  split_pure_spatial.
  - cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (IntArray.full visited n_pre l_visited_3).
    cancel (IntArray.full lowcost n_pre l_lowcost_3).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_3).
  - split_pures; dump_pre_spatial; eauto using min_vertex_in_range_empty; lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_19_2_running : prim_adjacency_matrix_return_matrix_entail_wit_19_2_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists l_lowcost_3 l_vertex_parent_3 l_edge_parent_3 l_visited_3 s_2.
  split_pure_spatial.
  - cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (IntArray.full visited n_pre l_visited_3).
    cancel (IntArray.full lowcost n_pre l_lowcost_3).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_3).
  - split_pures; dump_pre_spatial; eauto using min_vertex_in_range_empty; lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_20_1_running : prim_adjacency_matrix_return_matrix_entail_wit_20_1_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  unfold prim_adjacency_matrix_graph_model in Hgraph_model.
  Exists l_lowcost l_vertex_parent l_edge_parent l_visited s_after.
  pose proof (prim_connected _ _ PreH12) as Hconnected.
  pose proof (state_vertex_count_positive_exists
    s_after (proj1 PreH15) ltac:(rewrite PreH17; lia)) as Hnonempty.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [
      apply derivable1s_coq_prop_r;
      intros Hlt;
      eapply unfinished_connected_state_has_candidate_vertex_by_count;
      eauto;
      rewrite PreH17; exact Hlt
    ];
    try solve [
      apply derivable1s_coq_prop_r;
      replace ((i + 1) - 1) with i by lia;
      exact PreH23
    ];
    try solve [
      sepcon_assoc_change; cancel
    | normalize; cancel
    | dump_pre_spatial; int_auto
    | dump_pre_spatial; lia
    | dump_pre_spatial; assumption
    | dump_pre_spatial; reflexivity
    | apply derivable1s_coq_prop_r; int_auto
    | apply derivable1s_coq_prop_r; lia
    | apply derivable1s_coq_prop_r; assumption
    | apply derivable1s_coq_prop_r; reflexivity
    ].
  Unshelve.
  all: try solve [lia | nia | int_auto | eauto | reflexivity | constructor].
  all: try solve [
    sepcon_assoc_change; cancel
  | normalize; cancel
  | dump_pre_spatial; int_auto
  | dump_pre_spatial; lia
  | dump_pre_spatial; assumption
  | dump_pre_spatial; reflexivity
  | apply derivable1s_coq_prop_r; int_auto
  | apply derivable1s_coq_prop_r; lia
  | apply derivable1s_coq_prop_r; assumption
  | apply derivable1s_coq_prop_r; reflexivity
  ].
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_20_2_running : prim_adjacency_matrix_return_matrix_entail_wit_20_2_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  unfold prim_adjacency_matrix_graph_model in Hgraph_model.
  Exists l_lowcost l_vertex_parent l_edge_parent l_visited s_after.
  pose proof (prim_connected _ _ PreH12) as Hconnected.
  pose proof (state_vertex_count_positive_exists
    s_after (proj1 PreH15) ltac:(rewrite PreH17; lia)) as Hnonempty.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [
      apply derivable1s_coq_prop_r;
      intros Hlt;
      eapply unfinished_connected_state_has_candidate_vertex_by_count;
      eauto;
      rewrite PreH17; exact Hlt
    ];
    try solve [
      apply derivable1s_coq_prop_r;
      replace ((i_2 + 1) - 1) with i_2 by lia;
      exact PreH23
    ];
    try solve [sepcon_assoc_change; cancel | normalize; cancel | cancel].
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_21_1_running : prim_adjacency_matrix_return_matrix_entail_wit_21_1_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  unfold prim_adjacency_matrix_graph_model in Hgraph_model.
  Exists l_lowcost_3 l_visited_3 nil
         l_vertex_parent_3 l_edge_parent_3 (Prim.graph_in_state s) s.
  assert (Hret_empty:
    emp |-- IntPtrArray2.full retval 0 (inf_matrix 0 n_pre 1000000000)).
  {
    unfold IntPtrArray2.full, inf_matrix.
    simpl.
    Exists (@nil Z).
    split_pure_spatial.
    - simpl.
      rewrite (PtrArray.full_empty retval 0).
      unfold IntPtrArray2.row_blocks, iter_sepcon.
      simpl.
      split_pure_spatial.
      + cancel.
      + apply derivable1s_coq_prop_r.
        reflexivity.
    - apply derivable1s_coq_prop_r.
      split; reflexivity.
  }
  assert (Hsafe_graph:
    safeExec (prim_state_graph_matches (Prim.graph_in_state s)) (return tt)
      X_low_level_spec).
  {
    assert (Hsafe_ret : safeExec (prim_state_is s) (return tt) X_low_level_spec).
    {
      eapply Prim2_loop_finish with
        (n := n_pre) (matrix := matrix_low_level_spec)
        (inf := 1000000000) (i := i_2).
      - exact (prim_graph_valid _ _ PreH10).
      - exact Hgraph_model.
      - lia.
      - lia.
      - exact PreH20.
    }
    eapply safeExec_conseq; [exact Hsafe_ret |].
    intros st Hst.
    unfold prim_state_is in Hst.
    subst st.
    unfold prim_state_graph_matches.
    reflexivity.
  }
  split_pure_spatial.
  - change nil with (inf_matrix 0 n_pre 1000000000).
    sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg retval n_pre).
    sep_apply_r_atomic Hret_empty.
    cancel (PtrArray.undef_seg retval 0 n_pre).
    cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (IntArray.full visited n_pre l_visited_3).
    cancel (IntArray.full lowcost n_pre l_lowcost_3).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_3).
    cancel.
  - split_pures;
      try solve [dump_pre_spatial; unfold prim_state_graph_matches, inf_matrix; simpl; eauto; lia
                 | dump_pre_spatial; exact Hsafe_graph].
Qed. 

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_21_2_running : prim_adjacency_matrix_return_matrix_entail_wit_21_2_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  unfold prim_adjacency_matrix_graph_model in Hgraph_model.
  Exists l_lowcost_3 l_visited_3 nil
         l_vertex_parent_3 l_edge_parent_3 (Prim.graph_in_state s) s.
  assert (Hret_empty:
    emp |-- IntPtrArray2.full retval 0 (inf_matrix 0 n_pre 1000000000)).
  {
    unfold IntPtrArray2.full, inf_matrix.
    simpl.
    Exists (@nil Z).
    split_pure_spatial.
    - simpl.
      rewrite (PtrArray.full_empty retval 0).
      unfold IntPtrArray2.row_blocks, iter_sepcon.
      simpl.
      split_pure_spatial.
      + cancel.
      + apply derivable1s_coq_prop_r.
        reflexivity.
    - apply derivable1s_coq_prop_r.
      split; reflexivity.
  }
  assert (Hsafe_graph:
    safeExec (prim_state_graph_matches (Prim.graph_in_state s)) (return tt)
      X_low_level_spec).
  {
    assert (Hsafe_ret : safeExec (prim_state_is s) (return tt) X_low_level_spec).
    {
      eapply Prim2_loop_finish with
        (n := n_pre) (matrix := matrix_low_level_spec)
        (inf := 1000000000) (i := i_2).
      - exact (prim_graph_valid _ _ PreH10).
      - exact Hgraph_model.
      - lia.
      - lia.
      - exact PreH20.
    }
    eapply safeExec_conseq; [exact Hsafe_ret |].
    intros st Hst.
    unfold prim_state_is in Hst.
    subst st.
    unfold prim_state_graph_matches.
    reflexivity.
  }
  split_pure_spatial.
  - change nil with (inf_matrix 0 n_pre 1000000000).
    sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg retval n_pre).
    sep_apply_r_atomic Hret_empty.
    cancel (PtrArray.undef_seg retval 0 n_pre).
    cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (IntArray.full visited n_pre l_visited_3).
    cancel (IntArray.full lowcost n_pre l_lowcost_3).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_3).
    cancel.
  - split_pures;
      try solve [dump_pre_spatial; unfold prim_state_graph_matches, inf_matrix; simpl; eauto; lia
                 | dump_pre_spatial; exact Hsafe_graph].
Qed. 

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_22_running : prim_adjacency_matrix_return_matrix_entail_wit_22_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists l_lowcost_2 l_visited_2 retval (repeat_Z 1000000000 0)
    result_matrix_2 l_vertex_parent_2 l_edge_parent_2 rg_2 s_after_2.
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval n_pre).
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; unfold repeat_Z; reflexivity);
    try (dump_pre_spatial; lia);
    try solve [cancel].
  - change (repeat_Z 1000000000 0) with (@nil Z).
    rewrite (IntArray.seg_empty retval 0 0).
    cancel.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial; lia.
Qed. 

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_23_running : prim_adjacency_matrix_return_matrix_entail_wit_23_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hrow_next :
    row_prefix_2 +:: 1000000000 = repeat_Z 1000000000 (j + 1)).
  {
    rewrite PreH18.
    symmetry.
    apply repeat_Z_tail.
    lia.
  }
  rewrite Hrow_next.
  Exists l_lowcost_2 l_visited_2 row_ptr_2
    (repeat_Z 1000000000 (j + 1)) result_matrix_2
    l_vertex_parent_2 l_edge_parent_2 rg_2 s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [
      apply derivable1s_coq_prop_r;
      rewrite <- PreH18;
      apply repeat_Z_tail;
      lia
    ];
    try solve [cancel].
  - cancel (IntArray.seg row_ptr_2 0 (j + 1) (repeat_Z 1000000000 (j + 1))).
    cancel (IntArray.undef_seg row_ptr_2 (j + 1) n_pre).
    cancel (IntPtrArray2.full mst i result_matrix_2).
    cancel (PtrArray.undef_seg mst (i + 1) n_pre).
    cancel (((mst + i * sizeof(PTR)) # Ptr |-> row_ptr_2)).
    cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (IntArray.full visited n_pre l_visited_2).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
  - apply derivable1s_coq_prop_r.
    reflexivity.
Qed. 

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_24_running : prim_adjacency_matrix_return_matrix_entail_wit_24_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hj_eq : j = n_pre) by lia.
  subst j.
  assert (Hmatrix_next :
    result_matrix_2 ++ row_prefix :: nil =
      inf_matrix (i + 1) n_pre 1000000000).
  {
    rewrite PreH17, PreH18.
    unfold inf_matrix.
    symmetry.
    apply repeat_Z_tail.
    lia.
  }
  assert (Hpublish :
    IntPtrArray2.full mst i result_matrix_2 **
    StorePtrAsElement.storeA mst i row_ptr **
    IntArray.full row_ptr (Zlength row_prefix) row_prefix **
    PtrArray.undef_seg mst (i + 1) n_pre |--
      IntPtrArray2.full mst (i + 1) (result_matrix_2 ++ row_prefix :: nil) **
      PtrArray.undef_seg mst (i + 1) n_pre).
  {
    unfold IntPtrArray2.full.
    Intros row_ptrs.
    destruct H as [Hptrs Hrows].
    Exists (row_ptrs ++ row_ptr :: nil).
    split_pure_spatial.
    - sep_apply (PtrArray.full_to_seg mst i row_ptrs).
      sep_apply (PtrArray.seg_single mst i row_ptr).
      sep_apply (PtrArray.seg_merge_to_full mst 0 i (i + 1)); try lia.
      rewrite Z.mul_0_l, Z.add_0_r.
      replace (i + 1 - 0) with (i + 1) by lia.
      cancel.
      assert (Hlen : List.length row_ptrs = List.length result_matrix_2).
      { apply Nat2Z.inj. rewrite <- !Zlength_correct. lia. }
      unfold IntPtrArray2.row_blocks.
      rewrite (combine_app row_ptrs (row_ptr :: nil) result_matrix_2 (row_prefix :: nil) Hlen).
      rewrite map_app.
      rewrite <- derivable1_sepcon_iter_sepcon1.
      unfold IntPtrArray2.row_block.
      change (IntArray.full row_ptr (Zlength row_prefix) row_prefix)
        with (IntPtrArray2.ElemArray.full row_ptr (Zlength row_prefix) row_prefix).
      sep_apply (IntPtrArray2.single_to_iter_sepcon
        (IntPtrArray2.ElemArray.full row_ptr (Zlength row_prefix) row_prefix)).
      simpl map.
      simpl combine.
      apply __derivable1_provable.
      apply provable_sepcon_comm_impp.
    - apply derivable1s_coq_prop_r.
      split.
      + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
      + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  }
  sep_apply_l_atomic (IntArray.undef_seg_empty row_ptr n_pre).
  sep_apply_l_atomic
    (IntArray.seg_to_full row_ptr 0 n_pre row_prefix).
  replace (row_ptr + 0 * sizeof(INT)) with row_ptr by lia.
  assert (Hrow_len : Zlength row_prefix = n_pre).
  {
    rewrite PreH18.
    unfold repeat_Z.
    rewrite Zlength_correct, repeat_length.
    rewrite Z2Nat.id by lia.
    reflexivity.
  }
  replace (n_pre - 0) with (Zlength row_prefix) by lia.
  change (((mst + i * sizeof(PTR)) # Ptr |-> row_ptr))
    with (StorePtrAsElement.storeA mst i row_ptr).
  sep_apply_l_atomic Hpublish.
  rewrite Hmatrix_next.
  Exists l_lowcost_2 l_visited_2 (inf_matrix (i + 1) n_pre 1000000000)
    l_vertex_parent_2 l_edge_parent_2 rg_2 s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [cancel].
  - cancel (((&( "j" )) # Int |-> n_pre)).
    cancel (PtrArray.undef_seg mst (i + 1) n_pre).
    cancel (IntPtrArray2.full mst (i + 1) (inf_matrix (i + 1) n_pre 1000000000)).
    cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (IntArray.full visited n_pre l_visited_2).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
  - apply derivable1s_coq_prop_r.
    reflexivity.
Qed. 

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_25_running : prim_adjacency_matrix_return_matrix_entail_wit_25_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH14.
  Exists l_lowcost_2 l_visited_2 (inf_matrix (i + 1) n_pre 1000000000)
    l_vertex_parent_2 l_edge_parent_2 rg_2 s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [cancel].
  - cancel (PtrArray.undef_seg mst (i + 1) n_pre).
    cancel (IntPtrArray2.full mst (i + 1) (inf_matrix (i + 1) n_pre 1000000000)).
    cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (IntArray.full visited n_pre l_visited_2).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
  - apply derivable1s_coq_prop_r.
    reflexivity.
Qed. 

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_26_running : prim_adjacency_matrix_return_matrix_entail_wit_26_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  unfold prim_adjacency_matrix_graph_model in Hgraph_model.
  assert (i = n_pre) by lia.
  subst i.
  subst result_matrix_2.
  Exists l_lowcost_2 l_visited_2 (inf_matrix n_pre n_pre 1000000000)
    l_vertex_parent_2 l_edge_parent_2 rg_2 s_after_2.
  split_pure_spatial.
  - sep_apply_l_atomic (PtrArray.undef_seg_empty mst n_pre).
    cancel.
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
    cancel.
  - split_pures; dump_pre_spatial; eauto; try reflexivity; try lia.
    eapply result_matrix_parent_prefix_zero_inf_matrix; eauto; lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_27_running : prim_adjacency_matrix_return_matrix_entail_wit_27_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst result_matrix_2.
  Exists l_lowcost_2 l_visited_2 (inf_matrix n_pre n_pre 1000000000)
    l_vertex_parent_2 l_edge_parent_2 rg_2 s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [repeat cancel].
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_28_running : prim_adjacency_matrix_return_matrix_entail_wit_28_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_elim n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  pose proof Hgraph_model as Hmodel_shape.
  unfold prim_adjacency_matrix_graph_model, adjacency_matrix_model,
    adjacency_matrix_shape in Hmodel_shape.
  destruct Hmodel_shape as [[Hmatrix_len Hmatrix_row_len] _].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    graph_pre (Znth i l_vertex_parent 0) n_pre matrix_low_level_spec).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists l_lowcost_2 l_visited_2 row_ptr result_matrix_2
      l_edge_parent_2 rg_2 s_after_2 l_vertex_parent.
    rewrite (Znth_indep matrix_low_level_spec
      (Znth i l_vertex_parent 0) nil __default__List_Z)
      by (rewrite Hmatrix_len; lia).
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth (Znth i l_vertex_parent 0)
        matrix_low_level_spec __default__List_Z))
      (Znth (Znth i l_vertex_parent 0)
        matrix_low_level_spec __default__List_Z))
      with (IntArray.full row_ptr
        (Zlength (Znth (Znth i l_vertex_parent 0)
          matrix_low_level_spec __default__List_Z))
        (Znth (Znth i l_vertex_parent 0)
          matrix_low_level_spec __default__List_Z)).
    replace (Zlength (Znth (Znth i l_vertex_parent 0)
      matrix_low_level_spec __default__List_Z)) with n_pre
      by (rewrite <- (Znth_indep matrix_low_level_spec
            (Znth i l_vertex_parent 0) nil __default__List_Z)
            by (rewrite Hmatrix_len; lia);
          symmetry; apply Hmatrix_row_len; lia).
    change (sizeof(PTR)) with ptr_size_Z.
    repeat (split_pure_spatial || split_pures);
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; lia);
      try solve [repeat cancel].
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_29_running : prim_adjacency_matrix_return_matrix_entail_wit_29_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (int_ptr_array2_missing_i_Zlength
    graph_pre n_pre p row_ptr matrix_low_level_spec).
  Intros_p Hgraph_matrix_len.
  assert (Hres_row_len :
    Zlength (Znth p result_matrix_2 __default__List_Z) = n_pre).
  {
    destruct PreH17 as [[Houter Hrows] _].
    rewrite (Znth_indep result_matrix_2 p __default__List_Z nil)
      by (rewrite Houter, Hgraph_matrix_len; lia).
    rewrite <- Hgraph_matrix_len.
    apply Hrows.
    rewrite Hgraph_matrix_len; lia.
  }
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    mst p n_pre result_matrix_2).
  - dump_pre_spatial. lia.
  - Intros mst_row.
    Exists l_lowcost_2 l_visited_2 mst_row row_ptr result_matrix_2
      l_edge_parent_2 rg_2 s_after_2 l_vertex_parent_2.
    rewrite (Znth_indep result_matrix_2 p nil __default__List_Z)
      by (destruct PreH17 as [[Houter _] _];
          rewrite Houter, Hgraph_matrix_len; lia).
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full mst_row
      (Zlength (Znth p result_matrix_2 __default__List_Z))
      (Znth p result_matrix_2 __default__List_Z))
      with (IntArray.full mst_row
        (Zlength (Znth p result_matrix_2 __default__List_Z))
        (Znth p result_matrix_2 __default__List_Z)).
    rewrite Hres_row_len.
    change (sizeof(PTR)) with ptr_size_Z.
    repeat (split_pure_spatial || split_pures);
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; lia);
      try solve [repeat cancel].
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_30_running : prim_adjacency_matrix_return_matrix_entail_wit_30_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength graph_row n_pre
    (Znth p matrix_low_level_spec __default__List_Z)).
  Intros_p Hgraph_row_len.
  replace (IntArray.full graph_row n_pre
    (Znth p matrix_low_level_spec __default__List_Z))
    with (IntArray.full graph_row
      (Zlength (Znth p matrix_low_level_spec __default__List_Z))
      (Znth p matrix_low_level_spec __default__List_Z))
    by (rewrite Hgraph_row_len; reflexivity).
  sep_apply_l_atomic (int_ptr_array2_missing_store_row_merge_to_full
    graph_pre p n_pre graph_row matrix_low_level_spec
    (Znth p matrix_low_level_spec __default__List_Z)).
  - dump_pre_spatial. lia.
  - rewrite replace_Znth_Znth by lia.
    Exists l_lowcost_2 l_visited_2 mst_row_2 result_matrix_2
      l_edge_parent_2 rg_2 s_after_2 l_vertex_parent_2.
    repeat (split_pure_spatial || split_pures);
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; lia);
      try solve [repeat cancel].
    + sep_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_intro n_pre
        (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
        graph_pre matrix_low_level_spec).
      cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
        (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
        graph_pre matrix_low_level_spec).
      qcp_light_sep.
      unfold prim_adjacency_matrix_graph_model in PreH19; exact PreH19.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_31_running : prim_adjacency_matrix_return_matrix_entail_wit_31_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  assert (Hmatrix_len : Zlength matrix_low_level_spec = n_pre).
  {
    pose proof Hgraph_model as Hmodel.
    unfold prim_adjacency_matrix_graph_model, adjacency_matrix_model,
      adjacency_matrix_shape in Hmodel.
    destruct Hmodel as [[Hmatrix_len _] _].
    exact Hmatrix_len.
  }
  assert (Hres_row_len :
    Zlength (Znth p result_matrix_2 __default__List_Z) = n_pre).
  {
    pose proof PreH18 as Hprefix.
    unfold result_matrix_parent_prefix in Hprefix.
    destruct Hprefix as [[Houter Hrows] _].
    rewrite (Znth_indep result_matrix_2 p __default__List_Z nil)
      by (rewrite Houter, Hmatrix_len; lia).
    rewrite <- Hmatrix_len.
    apply Hrows.
    rewrite Hmatrix_len; lia.
  }
  replace (IntArray.full mst_row n_pre
    (replace_Znth i w (Znth p result_matrix_2 __default__List_Z)))
    with (IntArray.full mst_row
      (Zlength (replace_Znth i w
        (Znth p result_matrix_2 __default__List_Z)))
      (replace_Znth i w (Znth p result_matrix_2 __default__List_Z)))
    by (rewrite Zlength_replace_Znth, Hres_row_len; reflexivity).
  sep_apply_l_atomic (int_ptr_array2_missing_store_row_merge_to_full
    mst p n_pre mst_row result_matrix_2
    (replace_Znth i w (Znth p result_matrix_2 __default__List_Z))).
  - dump_pre_spatial. lia.
  - rewrite (Znth_indep result_matrix_2 p __default__List_Z nil)
      by (destruct PreH18 as [[Houter _] _];
          rewrite Houter, Hmatrix_len; lia).
    unfold set_matrix_entry.
    Exists l_lowcost_2 l_visited_2 result_matrix_2
      l_edge_parent_2 rg_2 s_after_2 l_vertex_parent_2.
    repeat (split_pure_spatial || split_pures);
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; lia);
      try solve [repeat cancel].
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_32_running : prim_adjacency_matrix_return_matrix_entail_wit_32_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  assert (Hmatrix_len : Zlength matrix_low_level_spec = n_pre).
  {
    pose proof Hgraph_model as Hmodel.
    unfold prim_adjacency_matrix_graph_model, adjacency_matrix_model,
      adjacency_matrix_shape in Hmodel.
    destruct Hmodel as [[Hmatrix_len _] _].
    exact Hmatrix_len.
  }
  assert (Hshape_result_2 : adjacency_matrix_shape n_pre result_matrix_2).
  {
    pose proof PreH18 as Hprefix.
    unfold result_matrix_parent_prefix in Hprefix.
    destruct Hprefix as [Hshape_result_2 _].
    rewrite Hmatrix_len in Hshape_result_2.
    exact Hshape_result_2.
  }
  assert (Hshape_set :
    adjacency_matrix_shape n_pre (set_matrix_entry result_matrix_2 p i w)).
  {
    eapply set_matrix_entry_shape; eauto; lia.
  }
  assert (Hrow_default :
    Znth i (set_matrix_entry result_matrix_2 p i w) nil =
    Znth i (set_matrix_entry result_matrix_2 p i w) __default__List_Z).
  {
    apply Znth_indep.
    destruct Hshape_set as [Hlen _].
    rewrite Hlen; lia.
  }
  assert (Hrow_len :
    Zlength (Znth i (set_matrix_entry result_matrix_2 p i w) __default__List_Z) = n_pre).
  {
    rewrite <- Hrow_default.
    destruct Hshape_set as [_ Hrows].
    apply Hrows; lia.
  }
  Exists l_lowcost_2 l_visited_2.
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i mst i n_pre (set_matrix_entry result_matrix_2 p i w)).
  - dump_pre_spatial. lia.
  - Intros mst_row.
    Exists mst_row result_matrix_2 l_edge_parent_2 rg_2 s_after_2 l_vertex_parent_2.
    rewrite Hrow_default.
    rewrite Hrow_len.
    repeat (split_pure_spatial || split_pures);
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; lia);
      try solve [cancel].
    unfold StorePtrAsElement.storeA.
    simpl.
    change ptr_size_Z with Arch32.ptr_size_Z.
    change (IntPtrArray2.ElemArray.full mst_row n_pre
      (Znth i (set_matrix_entry result_matrix_2 p i w) __default__List_Z))
      with (IntArray.full mst_row n_pre
      (Znth i (set_matrix_entry result_matrix_2 p i w) __default__List_Z)).
    cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (IntPtrArray2.missing_i mst n_pre i mst_row
      (set_matrix_entry result_matrix_2 p i w)).
    cancel (((mst + i * Arch32.ptr_size_Z)) # Ptr |-> mst_row).
    cancel (IntArray.full mst_row n_pre
      (Znth i (set_matrix_entry result_matrix_2 p i w) __default__List_Z)).
    cancel (IntArray.full visited n_pre l_visited_2).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_33_running : prim_adjacency_matrix_return_matrix_entail_wit_33_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  assert (Hmatrix_len : Zlength matrix_low_level_spec = n_pre).
  {
    pose proof Hgraph_model as Hmodel.
    unfold prim_adjacency_matrix_graph_model, adjacency_matrix_model,
      adjacency_matrix_shape in Hmodel.
    destruct Hmodel as [[Hmatrix_len _] _].
    exact Hmatrix_len.
  }
  assert (Hshape_result_2 : adjacency_matrix_shape n_pre result_matrix_2).
  {
    pose proof PreH18 as Hprefix.
    unfold result_matrix_parent_prefix in Hprefix.
    destruct Hprefix as [Hshape_result_2 _].
    rewrite Hmatrix_len in Hshape_result_2.
    exact Hshape_result_2.
  }
  assert (Hshape_set :
    adjacency_matrix_shape n_pre (set_matrix_entry result_matrix_2 p i w)).
  {
    eapply set_matrix_entry_shape; eauto; lia.
  }
  assert (Hrow_default :
    Znth i (set_matrix_entry result_matrix_2 p i w) nil =
    Znth i (set_matrix_entry result_matrix_2 p i w) __default__List_Z).
  {
    apply Znth_indep.
    destruct Hshape_set as [Hlen _].
    rewrite Hlen; lia.
  }
  assert (Hrow_len :
    Zlength (replace_Znth p w
      (Znth i (set_matrix_entry result_matrix_2 p i w) __default__List_Z)) = n_pre).
  {
    rewrite Zlength_replace_Znth.
    rewrite <- Hrow_default.
    destruct Hshape_set as [_ Hrows].
    apply Hrows; lia.
  }
  assert (Hrow_len_nil :
    Zlength (replace_Znth p w
      (Znth i (set_matrix_entry result_matrix_2 p i w) nil)) = n_pre).
  {
    rewrite Hrow_default.
    exact Hrow_len.
  }
  Exists l_lowcost_2 l_visited_2 result_matrix_2 l_edge_parent_2 rg_2 s_after_2 l_vertex_parent_2.
  rewrite <- Hrow_default.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve
      [ apply derivable1s_coq_prop_r;
        eapply result_matrix_parent_prefix_step; eauto; try lia;
        [ exact PreH13
        | exact PreH18
        | lia
        | lia
        | rewrite (Znth_indep l_vertex_parent_2 i (-1) 0); eauto; lia
        | unfold matrix_entry;
          rewrite (Znth_indep matrix_low_level_spec p nil __default__List_Z) by lia;
          exact PreH5 ] ].
  cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  cancel (IntArray.full visited n_pre l_visited_2).
  cancel (IntArray.full lowcost n_pre l_lowcost_2).
  cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
  unfold set_undirected_matrix_entry, set_matrix_entry.
  change ((mst + i * sizeof(PTR)) # Ptr |-> mst_row)
    with (StorePtrAsElement.storeA mst i mst_row).
  replace (IntArray.full mst_row n_pre
    (replace_Znth p w (Znth i
      (replace_Znth p
        (replace_Znth i w (Znth p result_matrix_2 nil))
        result_matrix_2) nil)))
    with (IntPtrArray2.ElemArray.full mst_row
      (Zlength (replace_Znth p w (Znth i
        (replace_Znth p
          (replace_Znth i w (Znth p result_matrix_2 nil))
          result_matrix_2) nil)))
      (replace_Znth p w (Znth i
        (replace_Znth p
          (replace_Znth i w (Znth p result_matrix_2 nil))
          result_matrix_2) nil))).
  2: { unfold set_matrix_entry in Hrow_len_nil; rewrite Hrow_len_nil. reflexivity. }
  sep_apply_l_atomic (IntPtrArray2.missing_i_merge_to_full
    mst i n_pre mst_row
    (replace_Znth p (replace_Znth i w (Znth p result_matrix_2 nil)) result_matrix_2)
    (replace_Znth p w (Znth i
      (replace_Znth p
        (replace_Znth i w (Znth p result_matrix_2 nil))
        result_matrix_2) nil))).
  - dump_pre_spatial. lia.
  - cancel.
  - apply derivable1s_coq_prop_r.
    eapply result_matrix_parent_prefix_step; eauto; try lia.
    + assert (Hi_graph : In i (graph_vertices g_low_level_spec)).
      {
        eapply adjacency_matrix_vertex_in_graph; eauto; lia.
      }
      pose proof (PreH17 i Hi_graph) as [Hi_parent_range _].
      rewrite (Znth_indep l_vertex_parent_2 i (-1) 0) by lia.
      exact PreH6.
    + unfold matrix_entry.
      rewrite (Znth_indep matrix_low_level_spec p nil __default__List_Z) by (rewrite Hmatrix_len; lia).
      exact PreH5.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_34_1_running : prim_adjacency_matrix_return_matrix_entail_wit_34_1_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists l_lowcost_2 l_visited_2 (set_undirected_matrix_entry result_matrix_2 p i w)
    l_vertex_parent_2 l_edge_parent_2 rg_2 s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia).
  cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  cancel (IntPtrArray2.full mst n_pre
    (set_undirected_matrix_entry result_matrix_2 p i w)).
  cancel (IntArray.full visited n_pre l_visited_2).
  cancel (IntArray.full lowcost n_pre l_lowcost_2).
  cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_34_2_running : prim_adjacency_matrix_return_matrix_entail_wit_34_2_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  assert (Hadj_model :
    adjacency_matrix_model n_pre matrix_low_level_spec g_low_level_spec 1000000000).
  {
    unfold prim_adjacency_matrix_graph_model in Hgraph_model.
    exact Hgraph_model.
  }
  Exists l_lowcost_2 l_visited_2 result_matrix_2 l_vertex_parent_2
    l_edge_parent_2 rg_2 s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia).
  - cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (IntPtrArray2.full mst n_pre result_matrix_2).
    cancel (IntArray.full visited n_pre l_visited_2).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
  - apply derivable1s_coq_prop_r.
    eapply result_matrix_parent_prefix_skip_negative_parent; eauto; try lia.
    assert (Hi_graph : In i (graph_vertices g_low_level_spec)).
    {
      eapply adjacency_matrix_vertex_in_graph; eauto; lia.
    }
    pose proof (PreH15 i Hi_graph) as [Hi_parent_range _].
    rewrite (Znth_indep l_vertex_parent_2 i (-1) 0) by lia.
    lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_34_3_running : prim_adjacency_matrix_return_matrix_entail_wit_34_3_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  assert (Hadj_model :
    adjacency_matrix_model n_pre matrix_low_level_spec g_low_level_spec 1000000000).
  {
    unfold prim_adjacency_matrix_graph_model in Hgraph_model.
    exact Hgraph_model.
  }
  Exists l_lowcost_2 l_visited_2 result_matrix_2 l_vertex_parent_2
    l_edge_parent_2 rg_2 s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia).
  - cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (IntPtrArray2.full mst n_pre result_matrix_2).
    cancel (IntArray.full visited n_pre l_visited_2).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
  - apply derivable1s_coq_prop_r.
    eapply result_matrix_parent_prefix_skip_large_parent; eauto; try lia.
    assert (Hi_graph : In i (graph_vertices g_low_level_spec)).
    {
      eapply adjacency_matrix_vertex_in_graph; eauto; lia.
    }
    pose proof (PreH16 i Hi_graph) as [Hi_parent_range _].
    rewrite (Znth_indep l_vertex_parent_2 i (-1) 0) by lia.
    lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_entail_wit_35_running : prim_adjacency_matrix_return_matrix_entail_wit_35_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  assert (Hadj_model :
    adjacency_matrix_model n_pre matrix_low_level_spec g_low_level_spec 1000000000).
  {
    unfold prim_adjacency_matrix_graph_model in Hgraph_model.
    exact Hgraph_model.
  }
  assert (Hi_eq : i = n_pre) by lia.
  subst i.
  Exists l_lowcost_2 l_visited_2 result_matrix_2 l_vertex_parent_2
    l_edge_parent_2 rg_2 s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia).
  - cancel (((&("i"))) # Int |-> n_pre).
    cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
      (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
      graph_pre matrix_low_level_spec).
    cancel (IntPtrArray2.full mst n_pre result_matrix_2).
    cancel (IntArray.full visited n_pre l_visited_2).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full vertex_parent n_pre l_vertex_parent_2).
  - apply derivable1s_coq_prop_r.
    eapply prim_result_matrix_matches_from_parent_prefix; eauto.
Qed.

Lemma proof_of_prim_adjacency_matrix_return_matrix_return_wit_1_running : prim_adjacency_matrix_return_matrix_return_wit_1_running.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  - Exists result_matrix_2 rg_2.
    split_pure_spatial.
    + cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
        (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
        graph_pre matrix_low_level_spec).
      cancel (IntPtrArray2.full mst n_pre result_matrix_2).
    + split_pures; dump_pre_spatial; auto.
Qed. 

Lemma proof_of_prim_adjacency_matrix_return_matrix_derive_high_level_spec_by_low_level_spec : prim_adjacency_matrix_return_matrix_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists matrix_high_level_spec g_high_level_spec src_high_level_spec
    (result_state (initStPred g_high_level_spec src_high_level_spec)
       (Prim2 g_high_level_spec)).
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try (dump_pre_spatial; apply safeExec_result_state; exists (initSt g_high_level_spec src_high_level_spec); reflexivity).
  cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
    (prim_adjacency_matrix_graph_model n_pre g_high_level_spec 1000000000)
    graph_pre matrix_high_level_spec).
  apply derivable1_wand_sepcon_adjoint.
  Intros result_matrix_2 rg_2 retval_2.
  assert (Hresult_mst : return_is_mst g_high_level_spec rg_2).
  {
    match goal with
    | Hsafe_ret : safeExec (prim_state_graph_matches rg_2) (return tt) _ |- _ =>
        unfold safeExec, safe in Hsafe_ret;
        destruct Hsafe_ret as [sigma [Hgraph Hsafe]]
    end.
    rewrite wp_ret in Hsafe.
    sets_unfold in Hsafe.
    unfold result_state in Hsafe.
    destruct Hsafe as [s0 [Hinit Hrun]].
    match goal with
    | Henv : PrimEnv g_high_level_spec src_high_level_spec |- _ =>
        pose proof (Prim2_correct_concrete
          g_high_level_spec src_high_level_spec Henv) as Hhoare
    end.
    unfold Hoare in Hhoare.
    specialize (Hhoare s0 tt sigma Hinit Hrun).
    unfold prim_state_graph_matches in Hgraph.
    rewrite <- Hgraph.
    exact Hhoare.
  }
  Exists result_matrix_2 rg_2 retval_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; exact Hresult_mst);
    try solve [cancel].
Qed. 
