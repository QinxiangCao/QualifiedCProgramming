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
From SimpleC.EE.LLM_bench.Algorithms.Prim Require Import prim_adjacency_matrix_goal.
From SimpleC.EE.LLM_bench.Algorithms.Prim Require Import prim_adjacency_matrix_proof_auto.
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
Require Import GraphLib.graph_basic.
Require Import ListLib.Base.Positional.
Require Import SumLib.ZRange.
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

Lemma proof_of_prim_adjacency_matrix_safety_wit_59_running_split_goal_1 : prim_adjacency_matrix_safety_wit_59_running_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_Zlength.
  Intros_p Hlowcost_len.
  apply derivable1s_coq_prop_r.
  rewrite PreH4.
  destruct PreH15 as [_ Hsum_bound].
  specialize (Hsum_bound i).
  assert (Hi : 0 <= i < Zlength l_lowcost) by (rewrite Hlowcost_len; lia).
  specialize (Hsum_bound Hi).
  lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_safety_wit_59_running_split_goal_2 : prim_adjacency_matrix_safety_wit_59_running_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply IntArray.full_Zlength.
  Intros_p Hlowcost_len.
  apply derivable1s_coq_prop_r.
  rewrite PreH4.
  destruct PreH15 as [_ Hsum_bound].
  specialize (Hsum_bound i).
  assert (Hi : 0 <= i < Zlength l_lowcost) by (rewrite Hlowcost_len; lia).
  specialize (Hsum_bound Hi).
  lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_safety_wit_59_running : prim_adjacency_matrix_safety_wit_59_running.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_safety_wit_59_running_split_goal_1.
  - Goal_apply proof_of_prim_adjacency_matrix_safety_wit_59_running_split_goal_2.
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_1_split_goal_1 : prim_adjacency_matrix_entail_wit_1_split_goal_1.
Proof. LLM_pre_process ltac:(int_auto). Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_1 : prim_adjacency_matrix_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_1_split_goal_1.
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_2_split_goal_1 : prim_adjacency_matrix_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (repeat_Z 0 (i + 1)) with (repeat_Z 0 i ++ 0 :: nil).
  reflexivity.
  symmetry; apply repeat_Z_tail; lia.
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_2 : prim_adjacency_matrix_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_2_split_goal_1.
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_3_split_goal_1 : prim_adjacency_matrix_entail_wit_3_split_goal_1.
Proof. LLM_pre_process ltac:(int_auto). Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_3_split_goal_2 : prim_adjacency_matrix_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace i with n_pre by lia.
  reflexivity.
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_3 : prim_adjacency_matrix_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_3_split_goal_2.
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_4_split_goal_1 : prim_adjacency_matrix_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  symmetry; apply repeat_Z_tail; lia.
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_4 : prim_adjacency_matrix_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_4_split_goal_1.
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_5_split_goal_1 : prim_adjacency_matrix_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace i with n_pre by lia.
  reflexivity.
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_5 : prim_adjacency_matrix_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_5_split_goal_1.
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_7_boot_split_goal_1 : prim_adjacency_matrix_entail_wit_7_boot_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply init_lowcost_values_in_range; lia.
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_7_boot : prim_adjacency_matrix_entail_wit_7_boot.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_7_boot_split_goal_1.
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_8_1_boot_split_goal_1 : prim_adjacency_matrix_entail_wit_8_1_boot_split_goal_1.
Proof.
  intros n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    l_visited_2 l_edge_parent_2 l_lowcost_2
    minIndex min i j PreH1 PreH2 PreH3 PreH4 PreH5
    PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros _.
  assert (Hj0 : j = 0).
  {
    destruct (Z.eq_dec j 0) as [Heq | Hneq]; auto.
    assert (Hj_ge_1 : 1 <= j) by lia.
    specialize (PreH18 Hj_ge_1).
    destruct PreH18 as [Hmin _].
    rewrite Hmin in PreH1.
    rewrite PreH20 in PreH1.
    rewrite Znth_replace_Znth_Diff in PreH1.
    - unfold repeat_Z in PreH1.
      rewrite Znth_repeat_lt in PreH1.
      + lia.
      + rewrite Z2Nat.id by lia.
        lia.
    - unfold repeat_Z.
      rewrite Zlength_correct, repeat_length.
      lia.
    - unfold repeat_Z.
      rewrite Zlength_correct, repeat_length.
      lia.
    - unfold not; intros H; apply Hneq; symmetry; exact H.
  }
  rewrite Hj0.
  split; [| reflexivity].
  rewrite PreH20.
  rewrite Znth_replace_Znth_Same.
  - reflexivity.
  - unfold repeat_Z.
    rewrite Zlength_correct, repeat_length.
    lia.
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_8_1_boot_split_goal_2 : prim_adjacency_matrix_entail_wit_8_1_boot_split_goal_2.
Proof.
  intros n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    l_visited_2 l_edge_parent_2 l_lowcost_2
    minIndex min i j PreH1 PreH2 PreH3 PreH4 PreH5
    PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  destruct (Z.eq_dec j 0) as [Hj | Hj].
  - subst j.
    rewrite PreH20.
    rewrite Znth_replace_Znth_Same.
    + lia.
    + unfold repeat_Z.
      rewrite Zlength_correct, repeat_length.
      rewrite Z2Nat.id by lia.
      lia.
  - rewrite PreH20.
    rewrite Znth_replace_Znth_Diff.
    + unfold repeat_Z.
      rewrite Znth_repeat_lt.
      * lia.
      * rewrite Z2Nat.id by lia; lia.
    + unfold repeat_Z.
      rewrite Zlength_correct, repeat_length.
      rewrite Z2Nat.id by lia.
      lia.
    + unfold repeat_Z.
      rewrite Zlength_correct, repeat_length.
      rewrite Z2Nat.id by lia.
      lia.
    + intros H; apply Hj; symmetry; exact H.
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_8_1_boot : prim_adjacency_matrix_entail_wit_8_1_boot.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_8_1_boot_split_goal_1.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_8_1_boot_split_goal_2.
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_8_2_boot : prim_adjacency_matrix_entail_wit_8_2_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  unfold prim_adjacency_matrix_graph_model in Hgraph_model.
  assert (Hmin_next :
    min_vertex_in_range
      g_low_level_spec s_2 (j + 1) 1000000000 j
      l_lowcost_2 l_edge_parent_2).
		  {
		    eapply min_vertex_in_range_take_current_from_arrays;
			      [ exact Hgraph_model
			      | exact PreH19
			      | exact PreH22
				      | exact PreH26
				      | lia
				      | exact PreH2
				      | exact PreH1
				      | exact PreH27
				      | exact PreH28 ].
		  }
  Exists l_lowcost_2 l_edge_parent_2 l_visited_2 s_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [qcp_light_sep | cancel].
	  apply derivable1s_coq_prop_r.
	  pose proof (lowcost_parent_match_unvisited_nonneg
	    n_pre matrix_low_level_spec g_low_level_spec s_2
	    l_lowcost_2 l_edge_parent_2 l_visited_2 1000000000 j
	    Hgraph_model ltac:(lia) ltac:(lia) PreH19 PreH22 PreH2) as Hlow_nonneg.
	  lia.
  Unshelve.
  all: try solve [qcp_light_sep | cancel | lia | assumption | reflexivity].
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_8_3_boot : prim_adjacency_matrix_entail_wit_8_3_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hnot_candidate :
    ~ candidate_vertex g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000 j).
  {
    intros Hcand.
    unfold candidate_vertex in Hcand.
    destruct Hcand as [Hj_graph [Hj_not_valid _]].
    destruct (PreH18 j Hj_graph) as [Hvisited_to_valid _].
    apply Hj_not_valid.
    apply Hvisited_to_valid.
    exact PreH1.
  }
  assert (Hmin_next :
    min_vertex_in_range
      g_low_level_spec s_2 (j + 1) 1000000000 minIndex
      l_lowcost_2 l_edge_parent_2).
  {
    eapply min_vertex_in_range_skip_not_candidate; eauto; lia.
  }
  Exists l_lowcost_2 l_edge_parent_2 l_visited_2 s_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [qcp_light_sep | cancel].
  Unshelve.
  all: try solve [qcp_light_sep | cancel | lia | assumption | reflexivity].
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_8_4_boot_split_goal_1 : prim_adjacency_matrix_entail_wit_8_4_boot_split_goal_1.
Proof.
  intros n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    l_visited_2 l_edge_parent_2 l_lowcost_2
    minIndex min i j PreH1 PreH2 PreH3 PreH4 PreH5
    PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22.
  intros _.
  assert (Hj_pos : 1 <= j).
  {
    destruct (Z.eq_dec j 0) as [Heq | Hneq].
    - subst j.
      rewrite PreH22 in PreH1.
      unfold repeat_Z in PreH1.
      rewrite Znth_repeat_lt in PreH1.
      + lia.
      + rewrite Z2Nat.id by lia.
        lia.
    - lia.
  }
  exact (PreH17 Hj_pos).
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_8_4_boot : prim_adjacency_matrix_entail_wit_8_4_boot.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_8_4_boot_split_goal_1.
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_8_5_boot_split_goal_1 : prim_adjacency_matrix_entail_wit_8_5_boot_split_goal_1.
Proof.
  intros n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    l_visited_2 l_edge_parent_2 l_lowcost_2
    minIndex min i j PreH1 PreH2 PreH3 PreH4 PreH5
    PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23.
  intros _.
  assert (Hj_pos : 1 <= j).
  {
    destruct (Z.eq_dec j 0) as [Heq | Hneq].
    - subst j.
      destruct (PreH17 eq_refl) as [Hmin _].
      rewrite Hmin in PreH1.
      rewrite PreH20 in PreH1.
      rewrite Znth_replace_Znth_Same in PreH1.
      + lia.
      + unfold repeat_Z.
        rewrite Zlength_correct, repeat_length.
        lia.
    - lia.
  }
  exact (PreH18 Hj_pos).
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_8_5_boot : prim_adjacency_matrix_entail_wit_8_5_boot.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_8_5_boot_split_goal_1.
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_8_6_boot : prim_adjacency_matrix_entail_wit_8_6_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hmin_next :
    min_vertex_in_range
      g_low_level_spec s_2 (j + 1) 1000000000 minIndex
      l_lowcost_2 l_edge_parent_2).
  {
    eapply min_vertex_in_range_skip_not_better_from_value;
      [ lia
      | exact PreH26
      | exact PreH1
      | exact PreH27
      | exact PreH28 ].
  }
  Exists l_lowcost_2 l_edge_parent_2 l_visited_2 s_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [qcp_light_sep | cancel].
  Unshelve.
  all: try solve [qcp_light_sep | cancel | lia | assumption | reflexivity].
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_9_2_boot : prim_adjacency_matrix_entail_wit_9_2_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  unfold prim_adjacency_matrix_graph_model in Hgraph_model.
  assert (Hj : j = n_pre) by lia.
  subst j.
  assert (Hcand_exists :
    candidate_vertex_exists_in_range
	      n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2
	      1000000000).
			  { apply PreH23; lia. }
		  assert (HminIndex_ne : minIndex <> -1).
			  {
				    eapply min_vertex_in_range_not_minus_one;
					      [exact Hcand_exists | exact PreH24].
			  }
  assert (Hselected_min :
    selected_parent_edge_is_min_cut_edge
      g_low_level_spec s_2 l_edge_parent_2 minIndex).
			  {
				    eapply min_vertex_parent_is_min_cut_edge;
					      [exact Hgraph_model | exact PreH20 | exact PreH24 | exact HminIndex_ne].
				  }
					  destruct (min_vertex_parent_pair_exists
					    n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2
					    1000000000 minIndex PreH24 HminIndex_ne)
			    as [u Hpair].
		  assert (Hmin_eq : min = Znth minIndex l_lowcost_2 0)
		    by (apply PreH26; exact HminIndex_ne).
		  assert (HminIndex_range : 0 <= minIndex < n_pre)
		    by (pose proof (PreH27 HminIndex_ne); lia).
				  Exists u minIndex l_lowcost_2 l_edge_parent_2 l_visited_2 s_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [qcp_light_sep | cancel].
Qed.
Ltac intros_prim_adj_wit_10_1_boot :=
  intros n_pre X_low_level_spec src_low_level_spec g_low_level_spec
	    matrix_low_level_spec l_visited_2 l_lowcost l_edge_parent i minIndex
	    min row_ptr_2 __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5
		    PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
		    PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22.

Lemma proof_of_prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_1 :
  prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_1.
Proof.
  intros_prim_adj_wit_10_1_boot.
  apply derivable1s_coq_prop_r.
  rewrite PreH19.
  eapply initSt_lowcost_sum_matches_state;
    [reflexivity | lia | exact PreH11].
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_2 :
  prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_2.
Proof.
  intros_prim_adj_wit_10_1_boot.
  apply derivable1s_coq_prop_r.
  exact (initSt_state_vertex_count g_low_level_spec 0).
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_3 :
  prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_3.
Proof.
  intros_prim_adj_wit_10_1_boot.
  apply derivable1s_coq_prop_r.
  rewrite PreH22.
  eapply initSt_visited_matches_state_zero_repeat;
    [exact PreH1 | reflexivity].
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_4 :
  prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_4.
Proof.
  intros_prim_adj_wit_10_1_boot.
  apply derivable1s_coq_prop_r.
  eapply initSt_growing_subgraph_state.
  rewrite <- PreH8.
  exact PreH12.
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_5 :
  prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_5.
Proof.
  intros_prim_adj_wit_10_1_boot.
  apply derivable1s_coq_prop_r.
  apply initStPred_Prim2_to_loop0.
  rewrite <- PreH8.
  exact PreH16.
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_6 :
  prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_6.
Proof.
  intros_prim_adj_wit_10_1_boot.
  apply derivable1s_coq_prop_r.
  pose proof PreH1 as Hmodel.
  unfold prim_adjacency_matrix_graph_model, adjacency_matrix_model in Hmodel.
  destruct Hmodel as [[_ Hrow_len] _].
  rewrite (Hrow_len 0); lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_spatial :
  prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_spatial.
Proof.
  intros_prim_adj_wit_10_1_boot.
  pose proof PreH1 as Hmodel.
  unfold prim_adjacency_matrix_graph_model, adjacency_matrix_model in Hmodel.
  destruct Hmodel as [[Hmatrix_len Hrow_len] _].
  replace (Znth minIndex matrix_low_level_spec nil)
    with (Znth minIndex matrix_low_level_spec __default__List_Z)
    by (symmetry; apply Znth_indep; rewrite Hmatrix_len; lia).
  qcp_light_sep.
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_10_1_boot : prim_adjacency_matrix_entail_wit_10_1_boot.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_spatial.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_1.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_2.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_3.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_4.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_5.
  - Goal_apply proof_of_prim_adjacency_matrix_entail_wit_10_1_boot_split_goal_6.
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_10_2_boot : prim_adjacency_matrix_entail_wit_10_2_boot.
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
    exact PreH11.
  }
		  destruct (selected_parent_add_to_mst_exists
		    g_low_level_spec 0 s_2 l_edge_parent minIndex u_2 v_2
		    Henv0 PreH17 PreH28) as [s_after Hadd].
  assert (Hsafe_after :
    safeExec (prim_state_is s_after)
      (Prim2_loop g_low_level_spec i) X_low_level_spec).
	  {
	    eapply (selected_parent_prim2_loop_step
	      n_pre matrix_low_level_spec g_low_level_spec 1000000000
	      i X_low_level_spec s_2 s_after l_edge_parent minIndex); eauto.
	    exact (prim_graph_valid g_low_level_spec 0 Henv0).
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
	    rewrite <- PreH19.
	    eapply selected_parent_add_to_mst_state_vertex_count; eauto.
	  }
  assert (Hparent_after :
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
  pose proof Hgraph_model as Hgraph_model_shape.
  unfold adjacency_matrix_model in Hgraph_model_shape.
  destruct Hgraph_model_shape as [[_ Hrow_len] _].
	  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
	    graph_pre minIndex n_pre matrix_low_level_spec).
  - dump_pre_spatial. lia.
	  - Intros row_ptr.
	    Exists row_ptr u_2 v_2 l_edge_parent l_visited_2 s_2 s_after l_lowcost.
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
				        Hgraph_model PreH21 PreH28 ltac:(lia)) as [Hmin_low Hmin_high];
				      rewrite PreH26;
				      lia
				    ];
				    try solve [
					      apply derivable1s_coq_prop_r;
					      eapply (selected_parent_add_to_mst_lowcost_sum_matches_state
					        g_low_level_spec s_2 s_after l_lowcost l_edge_parent
					        1000000000 minIndex);
					      [exact Henv0 | exact PreH17 | exact PreH21 | exact PreH22 | exact Hadd]
					    ];
			    try solve [qcp_light_sep | cancel; qcp_light_sep].
    all: try solve [dump_pre_spatial; assumption].
    all: try solve [dump_pre_spatial; lia].
	    all: try solve [apply derivable1s_coq_prop_r; dump_pre_spatial; assumption].
	    all: try solve [apply derivable1s_coq_prop_r; dump_pre_spatial; lia].
	    all: try solve [apply derivable1s_coq_prop_r; rewrite <- PreH7; dump_pre_spatial; assumption].
	    all: try solve [apply derivable1s_coq_prop_r; rewrite (Hrow_len minIndex); lia].
	    all: try solve [change (sizeof(PTR)) with ptr_size_Z; sepcon_assoc_change; cancel].
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_11_1_boot : prim_adjacency_matrix_entail_wit_11_1_boot.
Proof.
  right.
  intros n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec l_visited_2 l_lowcost0_2 l_edge_parent0_2
    s_after_2 i minIndex min
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
    PreH26.
  subst src_low_level_spec s_after_2 minIndex min
    l_lowcost0_2 l_edge_parent0_2 l_visited_2.
  Exists (default_edge_list n_pre).
  repeat (split_pure_spatial || split_pures);
    try reflexivity;
    try assumption;
    try lia;
    try solve [rewrite PreH5; reflexivity];
    try solve [rewrite PreH5; assumption];
    try solve [rewrite PreH5; apply scan_matrix_row_prefix_update_zero].
  all: try solve [apply derivable1s_coq_prop_r; reflexivity].
  all: try solve [apply derivable1s_coq_prop_r; assumption].
  all: try solve [apply derivable1s_coq_prop_r; lia].
  all: try solve [apply derivable1s_coq_prop_r; rewrite PreH5; reflexivity].
  all: try solve [apply derivable1s_coq_prop_r; rewrite PreH5; assumption].
  all: try solve [apply derivable1s_coq_prop_r; rewrite PreH5; apply scan_matrix_row_prefix_update_zero].
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_11_2_boot : prim_adjacency_matrix_entail_wit_11_2_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
	  Exists l_lowcost0_2 l_edge_parent0_2 u_2 v_2 l_edge_parent0_2
	    l_visited_2 s_2 s_after_2 l_lowcost0_2.
	  repeat (split_pure_spatial || split_pures);
	    try (dump_pre_spatial; assumption);
	    try (dump_pre_spatial; lia);
	    try solve [qcp_light_sep | cancel; qcp_light_sep].
  all: try solve [apply derivable1s_coq_prop_r; apply scan_matrix_row_prefix_update_zero].
  all: try solve [apply derivable1s_coq_prop_r; lia].
  all: try solve [cancel].
Qed.
Lemma proof_of_prim_adjacency_matrix_entail_wit_12_1_boot : prim_adjacency_matrix_entail_wit_12_1_boot.
Proof.
  left.
  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec lowcost visited row_ptr l_lowcost_2
    l_edge_parent_2 l_edge_parent0_2 l_lowcost0_2 l_visited_2
    s_after_2 min minIndex i j
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
    PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
    PreH34.
  sep_lift_L ((IntArray.full row_ptr
    (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth minIndex matrix_low_level_spec nil)) :: nil).
  assert (Hrow_range :
    0 <= j < Zlength (Znth minIndex matrix_low_level_spec nil))
    by (rewrite PreH8; lia).
  pose proof (IntArray.full_split_to_missing_i
    row_ptr j (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth minIndex matrix_low_level_spec nil) 0 Hrow_range) as Hsplit_row.
  sep_apply_L ((IntArray.full row_ptr
    (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth minIndex matrix_low_level_spec nil)) :: nil) Hsplit_row.
				  Exists l_lowcost_2 l_edge_parent_2 l_edge_parent0_2
				    l_lowcost0_2 l_visited_2 s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [qcp_light_sep | cancel; qcp_light_sep].
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_12_2_boot : prim_adjacency_matrix_entail_wit_12_2_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_lift_L ((IntArray.full row_ptr
    (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth minIndex matrix_low_level_spec nil)) :: nil).
	  assert (Hrow_range :
	    0 <= j < Zlength (Znth minIndex matrix_low_level_spec nil))
	    by (rewrite PreH8; lia).
  pose proof (IntArray.full_split_to_missing_i
    row_ptr j (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth minIndex matrix_low_level_spec nil) 0 Hrow_range) as Hsplit_row.
	  sep_apply_L ((IntArray.full row_ptr
	    (Zlength (Znth minIndex matrix_low_level_spec nil))
	    (Znth minIndex matrix_low_level_spec nil)) :: nil) Hsplit_row.
			  Exists l_lowcost_2 l_edge_parent_2 u_2 v_2 l_edge_parent0_2
			    l_visited_2 s_2 s_after_2 l_lowcost0_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [qcp_light_sep | cancel; qcp_light_sep].
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_13_1_boot : prim_adjacency_matrix_entail_wit_13_1_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hvisited_range : 0 <= j < n_pre) by lia.
  sep_apply (IntArray.full_split_to_missing_i
    visited j n_pre (replace_Znth minIndex 1 l_visited_2) 0
    Hvisited_range).
  assert (Hlowcost_range : 0 <= j < n_pre) by lia.
	  sep_apply (IntArray.full_split_to_missing_i
	    lowcost j n_pre l_lowcost_2 0 Hlowcost_range).
		  Exists l_lowcost_2 l_edge_parent_2 l_edge_parent0_2
		    l_lowcost0_2 l_visited_2 s_after_2.
		  repeat (split_pure_spatial || split_pures);
		    try (dump_pre_spatial; assumption);
		    try (dump_pre_spatial; lia);
		    try solve [qcp_light_sep | cancel; qcp_light_sep].
		  all: try lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_13_2_boot : prim_adjacency_matrix_entail_wit_13_2_boot.
Proof.
  right.
  intros n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec l_visited_2 l_lowcost0_2 l_lowcost_2
    l_edge_parent0_2 l_edge_parent_2 s_2 s_after_2 u_2 v_2
    j minIndex i min
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
    PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
    PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
    PreH42 PreH43 PreH44 PreH45.
  Exists l_edge_parent_2 u_2 v_2 l_edge_parent0_2
    s_2 s_after_2 l_lowcost0_2.
  repeat (split_pure_spatial || split_pures);
    try reflexivity;
    try assumption;
    try lia;
    try solve [rewrite PreH12; lia];
    try solve [rewrite PreH31; assumption];
    try solve [rewrite <- PreH16; assumption].
  all: try solve [apply derivable1s_coq_prop_r; reflexivity].
  all: try solve [apply derivable1s_coq_prop_r; assumption].
  all: try solve [apply derivable1s_coq_prop_r; lia].
  all: try solve [apply derivable1s_coq_prop_r; rewrite PreH12; lia].
  all: try solve [apply derivable1s_coq_prop_r; rewrite PreH31, PreH12; lia].
  all: try solve [apply derivable1s_coq_prop_r; rewrite PreH31; assumption].
  all: try solve [apply derivable1s_coq_prop_r; rewrite <- PreH16; assumption].
  all: try solve [apply derivable1s_coq_prop_r; rewrite PreH39, PreH31; lia].
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_14_1_boot : prim_adjacency_matrix_entail_wit_14_1_boot.
Proof.
  left.
	  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
	    matrix_low_level_spec l_visited_2 l_lowcost0_2 l_lowcost_2
	    l_edge_parent0_2 l_edge_parent_2 s_2 s_after_2 u_2 v_2 w
	    minIndex j i min selected_row visited lowcost
	    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
	    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
	    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
	    PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
	    PreH34 PreH35 PreH36 PreH37.
  pose proof PreH11 as Hmodel.
  unfold prim_adjacency_matrix_graph_model in Hmodel.
		  assert (Hrow_len :
			    Zlength (Znth minIndex matrix_low_level_spec nil) = n_pre) by
			    (unfold adjacency_matrix_model in Hmodel;
			     destruct Hmodel as [[_ Hrow_len_all] _];
			     apply Hrow_len_all; lia).
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
  assert (Hmin_bounds : INT_MIN <= min /\ min <= INT_MAX).
  {
    assert (Hmin_vertex : In minIndex (graph_vertices g_low_level_spec)).
    {
      eapply adjacency_matrix_vertex_in_graph; eauto; lia.
    }
    pose proof PreH25 as Hlowcost_parent_match.
    destruct Hlowcost_parent_match as [Hlowcost_parent_range _].
    pose proof (Hlowcost_parent_range minIndex Hmin_vertex)
      as [Hmin_lowcost_range _].
    pose proof (PreH34 minIndex Hmin_lowcost_range) as Hmin_value_range.
    rewrite PreH19.
    split; lia.
  }
  assert (Hj_not_state : ~ vvalid s_after_2.(Prim.graph_in_state) j).
  {
    intro Hv_valid.
    assert (Hj_graph : In j (graph_vertices g_low_level_spec)).
    {
      eapply adjacency_matrix_vertex_in_graph; eauto; lia.
    }
    destruct (PreH30 j Hj_graph) as [_ Hvalid_to_visited].
    apply Hvalid_to_visited in Hv_valid.
    apply Hv_valid. exact PreH2.
  }
  assert (Hvalue_bound :
    0 <= Znth j (Znth minIndex matrix_low_level_spec nil) 0 <= 1000000000).
  {
    pose proof Hmodel as Hmodel_entry.
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
    intros k Hk. apply PreH37. rewrite Hlowcost2_len. exact Hk.
  }
  assert (Hgraph_vertices_range :
    forall v, In v (graph_vertices g_low_level_spec) -> 0 <= v < Zlength l_lowcost_2).
  {
    intros v Hv.
    rewrite Hlowcost2_len.
    pose proof Hmodel as Hmodel_vertices.
    unfold adjacency_matrix_model in Hmodel_vertices.
    destruct Hmodel_vertices as [_ [Hvertices _]].
    rewrite Hvertices in Hv.
    rewrite <- In_Zrange in Hv.
    lia.
  }
				  Exists (replace_Znth j (Znth j (Znth minIndex matrix_low_level_spec nil) 0) l_lowcost_2)
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
	           [ apply Hlowcost2_bound;
	             rewrite Zlength_replace_Znth in Hk;
	             rewrite Hlowcost2_len in Hk; exact Hk
	           | rewrite Hlowcost2_len; lia
	           | rewrite Hlowcost2_len; lia
	           | lia ] ]);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [qcp_light_sep | cancel; qcp_light_sep].
		  apply derivable1s_coq_prop_r.
			  eapply scan_matrix_row_prefix_update_snoc.
			  - lia.
				  - exact PreH35.
				  - change (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
				      with (matrix_entry matrix_low_level_spec minIndex j).
				    apply scan_one_matrix_neighbor_update_take with (n := n_pre).
				    + exact Hmodel.
	    + lia.
	    + lia.
	    + intro Hv_valid.
	      assert (Hj_graph : In j (graph_vertices g_low_level_spec)).
	      {
	        eapply adjacency_matrix_vertex_in_graph; eauto; lia.
	      }
					      destruct (PreH30 j Hj_graph) as [_ Hvalid_to_visited].
		      apply Hvalid_to_visited in Hv_valid.
		      apply Hv_valid. exact PreH2.
			    + unfold matrix_entry. exact PreH4.
			    + unfold matrix_entry. exact PreH1.
  all: try solve [apply derivable1s_coq_prop_r; eauto].
  all: try solve [apply derivable1s_coq_prop_r; lia].
	  all: try solve [
	    apply derivable1s_coq_prop_r;
	    eapply lowcost_sum_matches_state_replace_outside
	      with (g := g_low_level_spec) (bound := 1000000000);
			    [ exact PreH29
    | exact Hj_not_state
    | rewrite Hlowcost2_len; lia
    | exact Hvalue_bound
		    | rewrite Hlowcost2_len; exact PreH15
    | exact Hgraph_vertices_range
    | intros v Hv; apply Hlowcost2_bound; rewrite Hlowcost2_len in Hv; exact Hv
			    | exact PreH36 ]
	  ].
	  all: try solve [qcp_light_sep | cancel; qcp_light_sep].
	  - apply derivable1s_coq_prop_r.
	    eapply lowcost_sum_matches_state_replace_outside
	      with (g := g_low_level_spec) (bound := 1000000000).
			    + exact PreH29.
    + exact Hj_not_state.
    + rewrite Hlowcost2_len; lia.
    + exact Hvalue_bound.
		    + rewrite Hlowcost2_len; exact PreH15.
	    + exact Hgraph_vertices_range.
	    + intros v Hv. apply Hlowcost2_bound. rewrite Hlowcost2_len in Hv. exact Hv.
			    + exact PreH36.
	  - apply derivable1s_coq_prop_r.
	    unfold lowcost_values_in_range; intros k Hk.
	    rewrite Zlength_replace_Znth in Hk.
	    rewrite Hlowcost2_len in Hk.
	    destruct (Z.eq_dec k j) as [-> | Hneq].
	    + rewrite Znth_replace_Znth_same_local.
	      * exact Hvalue_bound.
	      * rewrite Hlowcost2_len; lia.
	    + rewrite Znth_replace_Znth_diff_local.
	      * apply Hlowcost2_bound. exact Hk.
	      * rewrite Hlowcost2_len; lia.
	      * rewrite Hlowcost2_len; lia.
	      * lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_14_2_boot : prim_adjacency_matrix_entail_wit_14_2_boot.
Proof.
  right.
	  intros n_pre X_low_level_spec src_low_level_spec g_low_level_spec
	    matrix_low_level_spec l_visited_2 l_lowcost0_2 l_lowcost_2
	    l_edge_parent0_2 l_edge_parent_2 s_after_2 w minIndex j i min
	    selected_row visited lowcost
		    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
		    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
			    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
				    PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
				    PreH34 PreH35 PreH36 PreH37 PreH38.
  pose proof PreH17 as Hmodel.
  unfold prim_adjacency_matrix_graph_model in Hmodel.
			  pose proof PreH33 as Hlowcost0_eq.
	  pose proof PreH34 as Hedge_parent0_eq.
	  pose proof PreH35 as Hvisited_eq.
			  subst s_after_2.
  try rewrite Hlowcost0_eq in *.
  try rewrite Hedge_parent0_eq in *.
  try rewrite Hvisited_eq in *.
					  assert (Hrow_len :
					    Zlength (Znth minIndex matrix_low_level_spec nil) = n_pre) by
					    (unfold adjacency_matrix_model in Hmodel;
					     destruct Hmodel as [[_ Hrow_len_all] _];
					     apply Hrow_len_all; lia).
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
		    (Znth j (replace_Znth minIndex 1 (repeat_Z 0 n_pre)) 0)
		    (replace_Znth minIndex 1 (repeat_Z 0 n_pre))); try lia.
		  rewrite replace_Znth_Znth by lia.
  prop_apply (IntArray.missing_i_Zlength lowcost j 0 n_pre l_lowcost_2).
  Intros.
  assert (Hlowcost2_len : Zlength l_lowcost_2 = n_pre) by lia.
		  sep_apply (IntArray.missing_i_merge_to_full
		    lowcost j n_pre (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
		    l_lowcost_2); try lia.
  assert (Hvalue_bound :
    0 <= Znth j (Znth minIndex matrix_low_level_spec nil) 0 <= 1000000000).
  {
	    pose proof Hmodel as Hmodel_entry.
    unfold adjacency_matrix_model in Hmodel_entry.
    destruct Hmodel_entry as [_ [_ [Hentry _]]].
    specialize (Hentry minIndex j ltac:(lia) ltac:(lia)).
    unfold matrix_entry in Hentry.
    destruct Hentry as [Heq | Hrange].
    - exfalso. apply PreH10. exact Heq.
    - lia.
  }
	  assert (Hj_not_state : ~ vvalid (Prim.graph_in_state (initSt g_low_level_spec src_low_level_spec)) j).
	  {
	    intro Hv_valid.
	    assert (Hj_graph : In j (graph_vertices g_low_level_spec)).
    {
      eapply adjacency_matrix_vertex_in_graph; eauto; lia.
    }
    destruct (PreH29 j Hj_graph) as [_ Hvalid_to_visited].
    apply Hvalid_to_visited in Hv_valid.
    apply Hv_valid. exact PreH8.
  }
		  assert (Hlowcost2_bound :
		    forall k, 0 <= k < n_pre -> 0 <= Znth k l_lowcost_2 0 <= 1000000000).
		  {
			    intros k Hk. apply PreH38. rewrite Hlowcost2_len. exact Hk.
	  }
  assert (Hgraph_vertices_range :
    forall v, In v (graph_vertices g_low_level_spec) -> 0 <= v < Zlength l_lowcost_2).
  {
    intros v Hv.
    rewrite Hlowcost2_len.
	    pose proof Hmodel as Hmodel_vertices.
    unfold adjacency_matrix_model in Hmodel_vertices.
    destruct Hmodel_vertices as [_ [Hvertices _]].
    rewrite Hvertices in Hv.
    rewrite <- In_Zrange in Hv.
    lia.
  }
			  Exists (replace_Znth j (Znth j (Znth minIndex matrix_low_level_spec nil) 0) l_lowcost_2)
			    (replace_Znth j (undirected_edge minIndex j) l_edge_parent_2).
	  repeat (split_pure_spatial || split_pures);
    try (apply derivable1s_coq_prop_r;
         unfold lowcost_values_in_range; intros k Hk;
         destruct (Z.eq_dec k j) as [-> | Hneq];
	         [ rewrite Znth_replace_Znth_same_local;
	           [ exact Hvalue_bound | rewrite Hlowcost2_len; lia ]
	         | rewrite Znth_replace_Znth_diff_local;
	           [ apply Hlowcost2_bound;
	             rewrite Zlength_replace_Znth in Hk;
	             rewrite Hlowcost2_len in Hk; exact Hk
	           | rewrite Hlowcost2_len; lia
	           | rewrite Hlowcost2_len; lia
	           | lia ] ]);
	    try (dump_pre_spatial; assumption);
	    try (dump_pre_spatial; lia);
	    try solve [qcp_light_sep | cancel; qcp_light_sep].
	  apply derivable1s_coq_prop_r.
		  eapply scan_matrix_row_prefix_update_snoc.
		  - lia.
			  - exact PreH36.
			  - change (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
			      with (matrix_entry matrix_low_level_spec minIndex j).
			    apply scan_one_matrix_neighbor_update_take with (n := n_pre).
			    + exact Hmodel.
		    + lia.
		    + lia.
		    + intro Hv_valid.
		      assert (Hj_graph : In j (graph_vertices g_low_level_spec)).
		      {
		        eapply adjacency_matrix_vertex_in_graph; eauto; lia.
		      }
			      destruct (PreH29 j Hj_graph) as [_ Hvalid_to_visited].
		      pose proof (Hvalid_to_visited Hv_valid).
		      lia.
		    + exact PreH10.
		    + exact PreH7.
	  all: try solve [
	    apply derivable1s_coq_prop_r;
	    eapply lowcost_sum_matches_state_replace_outside
	      with (g := g_low_level_spec) (bound := 1000000000);
	    [ exact PreH28
    | exact Hj_not_state
    | rewrite Hlowcost2_len; lia
    | exact Hvalue_bound
	    | rewrite Hlowcost2_len; exact PreH21
    | exact Hgraph_vertices_range
    | intros v Hv; apply Hlowcost2_bound; rewrite Hlowcost2_len in Hv; exact Hv
	    | exact PreH37 ]
	  ].
	  - apply derivable1s_coq_prop_r.
	    eapply lowcost_sum_matches_state_replace_outside
	      with (g := g_low_level_spec) (bound := 1000000000).
	    + exact PreH28.
    + exact Hj_not_state.
    + rewrite Hlowcost2_len; lia.
    + exact Hvalue_bound.
	    + rewrite Hlowcost2_len; exact PreH21.
    + exact Hgraph_vertices_range.
    + intros v Hv. apply Hlowcost2_bound. rewrite Hlowcost2_len in Hv. exact Hv.
	    + exact PreH37.
  - apply derivable1s_coq_prop_r.
    unfold lowcost_values_in_range; intros k Hk.
    rewrite Zlength_replace_Znth in Hk.
    rewrite Hlowcost2_len in Hk.
    destruct (Z.eq_dec k j) as [-> | Hneq].
    + rewrite Znth_replace_Znth_same_local.
      * exact Hvalue_bound.
      * rewrite Hlowcost2_len; lia.
    + rewrite Znth_replace_Znth_diff_local.
      * apply Hlowcost2_bound. exact Hk.
      * rewrite Hlowcost2_len; lia.
      * rewrite Hlowcost2_len; lia.
      * lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_14_3_boot : prim_adjacency_matrix_entail_wit_14_3_boot.
Proof.
  left.
	  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
	    matrix_low_level_spec l_visited_2 l_lowcost0_2 l_lowcost_2
	    l_edge_parent0_2 l_edge_parent_2 s_2 s_after_2 u_2 v_2 w
	    minIndex j i min selected_row visited lowcost
	    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
			    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
				    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
				    PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
				    PreH34 PreH35 PreH36 PreH37.
  pose proof PreH11 as Hmodel.
  unfold prim_adjacency_matrix_graph_model in Hmodel.
	  assert (Hrow_len :
		    Zlength (Znth minIndex matrix_low_level_spec nil) = n_pre) by
		    (unfold adjacency_matrix_model in Hmodel;
		     destruct Hmodel as [[_ Hrow_len_all] _];
		     apply Hrow_len_all; lia).
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
	  assert (Hmin_bounds : INT_MIN <= min /\ min <= INT_MAX).
	  {
	    assert (Hmin_vertex : In minIndex (graph_vertices g_low_level_spec)).
	    {
	      eapply adjacency_matrix_vertex_in_graph; eauto; lia.
	    }
		    pose proof PreH25 as Hlowcost_parent_match.
	    destruct Hlowcost_parent_match as [Hlowcost_parent_range _].
	    pose proof (Hlowcost_parent_range minIndex Hmin_vertex)
	      as [Hmin_lowcost_range _].
		    pose proof (PreH34 minIndex Hmin_lowcost_range) as Hmin_value_range.
		    rewrite PreH19.
	    split; lia.
	  }
  Exists l_lowcost_2 l_edge_parent_2 u_2 v_2
    l_edge_parent0_2 l_visited_2 s_2 s_after_2 l_lowcost0_2.
  repeat (split_pure_spatial || split_pures);
    try (apply derivable1s_coq_prop_r; destruct Hmin_bounds; lia);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [qcp_light_sep | cancel; qcp_light_sep].
  apply derivable1s_coq_prop_r.
	  eapply scan_matrix_row_prefix_update_snoc.
	  - lia.
			  - exact PreH35.
	  - apply scan_one_matrix_neighbor_update_skip.
	    right; right.
	    unfold matrix_entry.
	    lia.
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_14_4_boot : prim_adjacency_matrix_entail_wit_14_4_boot.
Proof.
  right.
	  intros n_pre X_low_level_spec src_low_level_spec g_low_level_spec
	    matrix_low_level_spec l_visited_2 l_lowcost0_2 l_lowcost_2
	    l_edge_parent0_2 l_edge_parent_2 s_after_2 w minIndex j i min
	    selected_row visited lowcost
	    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
		    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
		    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
		    PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
		    PreH34 PreH35 PreH36 PreH37 PreH38.
  pose proof PreH17 as Hmodel.
  unfold prim_adjacency_matrix_graph_model in Hmodel.
		  assert (Hrow_len :
			    Zlength (Znth minIndex matrix_low_level_spec nil) = n_pre) by
		    (unfold adjacency_matrix_model in Hmodel;
		     destruct Hmodel as [[_ Hrow_len_all] _];
		     apply Hrow_len_all; lia).
	  assert (Hj_row :
	    0 <= j < Zlength (Znth minIndex matrix_low_level_spec nil)) by
	    (rewrite Hrow_len; lia).
	  assert (Hscan_one :
	    scan_one_matrix_neighbor_update g_low_level_spec matrix_low_level_spec
	      1000000000 s_after_2 minIndex j
	      l_lowcost_2 l_edge_parent_2 l_lowcost_2 l_edge_parent_2).
	  {
	    apply scan_one_matrix_neighbor_update_skip.
	    right; right.
	    unfold matrix_entry.
	    rewrite <- PreH9.
	    lia.
	  }
	  assert (Hscan_next :
	    scan_matrix_row_prefix_update g_low_level_spec matrix_low_level_spec
	      1000000000 s_after_2 minIndex (j + 1)
	      l_lowcost0_2 l_edge_parent0_2 l_lowcost_2 l_edge_parent_2).
		  {
		    eapply scan_matrix_row_prefix_update_snoc.
		    - lia.
				    - exact PreH36.
		    - exact Hscan_one.
		  }
		  sep_apply (int_array_missing_store_merge_to_full
		    selected_row j
		    (Zlength (Znth minIndex matrix_low_level_spec nil))
		    (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
		    (Znth minIndex matrix_low_level_spec nil)); try exact Hj_row.
		  rewrite replace_Znth_Znth by exact Hj_row.
		  sep_apply (int_array_missing_store_merge_to_full
		    visited j n_pre
		    (Znth j (replace_Znth minIndex 1 l_visited_2) 0)
		    (replace_Znth minIndex 1 l_visited_2)); try lia.
		  rewrite replace_Znth_Znth by lia.
		  sep_apply (int_array_missing_store_merge_to_full
		    lowcost j n_pre (Znth j l_lowcost_2 0) l_lowcost_2); try lia.
		  rewrite replace_Znth_Znth by lia.
				  pose proof PreH33 as Hlowcost0_eq.
				  pose proof PreH34 as Hedge_parent0_eq.
				  pose proof PreH35 as Hvisited_eq.
	  subst s_after_2.
	  try rewrite Hlowcost0_eq in *.
	  try rewrite Hedge_parent0_eq in *.
	  try rewrite Hvisited_eq in *.
		  Exists l_lowcost_2 l_edge_parent_2.
		  repeat (split_pure_spatial || split_pures);
		    try (dump_pre_spatial; assumption);
		    try (dump_pre_spatial; lia);
		    try solve [qcp_light_sep | cancel; qcp_light_sep].
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_14_5_boot : prim_adjacency_matrix_entail_wit_14_5_boot.
Proof.
  right.
		  intros n_pre X_low_level_spec src_low_level_spec g_low_level_spec
		    matrix_low_level_spec l_visited_2 l_lowcost0_2 l_lowcost_2
		    l_edge_parent0_2 l_edge_parent_2 s_after_2 w minIndex j i min
		    selected_row visited lowcost
			    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
				    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
				    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
				    PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
				    PreH34 PreH35 PreH36 PreH37.
  pose proof PreH16 as Hmodel.
  unfold prim_adjacency_matrix_graph_model in Hmodel.
			  pose proof PreH32 as Hlowcost0_eq.
			  pose proof PreH33 as Hedge_parent0_eq.
			  pose proof PreH34 as Hvisited_eq.
	  subst s_after_2.
	  try rewrite Hlowcost0_eq in *.
	  try rewrite Hedge_parent0_eq in *.
	  try rewrite Hvisited_eq in *.
	  assert (Hrow_len :
		    Zlength (Znth minIndex matrix_low_level_spec nil) = n_pre) by
		    (unfold adjacency_matrix_model in Hmodel;
		     destruct Hmodel as [[_ Hrow_len_all] _];
		     apply Hrow_len_all; lia).
  assert (Hj_row :
    0 <= j < Zlength (Znth minIndex matrix_low_level_spec nil)) by
    (rewrite Hrow_len; lia).
	  sep_apply (int_array_missing_store_merge_to_full
	    selected_row j
	    (Zlength (Znth minIndex matrix_low_level_spec nil))
	    (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
    (Znth minIndex matrix_low_level_spec nil)); try exact Hj_row.
  rewrite replace_Znth_Znth by exact Hj_row.
  sep_apply (IntArray.missing_i_merge_to_full
    visited j n_pre
    (Znth j (replace_Znth minIndex 1 (repeat_Z 0 n_pre)) 0)
    (replace_Znth minIndex 1 (repeat_Z 0 n_pre))); try lia.
  rewrite replace_Znth_Znth by lia.
  sep_apply (IntArray.missing_i_merge_to_full
    lowcost j n_pre (Znth j l_lowcost_2 0) l_lowcost_2); try lia.
  rewrite replace_Znth_Znth by lia.
  Exists l_lowcost_2 l_edge_parent_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [qcp_light_sep | cancel; qcp_light_sep].
  apply derivable1s_coq_prop_r.
	  eapply scan_matrix_row_prefix_update_snoc.
	  - lia.
			  - exact PreH35.
  - apply scan_one_matrix_neighbor_update_skip.
    left.
	    assert (Hj_graph : In j (graph_vertices g_low_level_spec)).
	    { eapply adjacency_matrix_vertex_in_graph; eauto; lia. }
			    apply (proj1 (PreH28 j Hj_graph)).
	    exact PreH7.
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_14_6_boot : prim_adjacency_matrix_entail_wit_14_6_boot.
Proof.
  left.
	  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
	    matrix_low_level_spec l_visited_2 l_lowcost0_2 l_lowcost_2
	    l_edge_parent0_2 l_edge_parent_2 s_2 s_after_2 u_2 v_2 w
	    minIndex j i min selected_row visited lowcost
		    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
			    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
			    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
			    PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
			    PreH34 PreH35 PreH36.
  pose proof PreH10 as Hmodel.
  unfold prim_adjacency_matrix_graph_model in Hmodel.
		  assert (Hrow_len :
		    Zlength (Znth minIndex matrix_low_level_spec nil) = n_pre) by
		    (unfold adjacency_matrix_model in Hmodel;
		     destruct Hmodel as [[_ Hrow_len_all] _];
		     apply Hrow_len_all; lia).
  assert (Hj_row :
    0 <= j < Zlength (Znth minIndex matrix_low_level_spec nil)) by
    (rewrite Hrow_len; lia).
  sep_apply_l_atomic (int_array_missing_store_merge_to_full
    selected_row j
    (Zlength (Znth minIndex matrix_low_level_spec nil))
	    (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
	    (Znth minIndex matrix_low_level_spec nil)).
  - apply derivable1s_coq_prop_r; exact Hj_row.
  -
  rewrite replace_Znth_Znth by exact Hj_row.
  sep_apply (int_array_missing_store_merge_to_full
    visited j n_pre
    (Znth j (replace_Znth minIndex 1 l_visited_2) 0)
    (replace_Znth minIndex 1 l_visited_2)); try lia.
  rewrite replace_Znth_Znth by lia.
	  sep_apply (int_array_missing_store_merge_to_full
	    lowcost j n_pre (Znth j l_lowcost_2 0) l_lowcost_2); try lia.
	  rewrite replace_Znth_Znth by lia.
	  assert (Hmin_bounds : INT_MIN <= min /\ min <= INT_MAX).
	  {
	    assert (Hmin_vertex : In minIndex (graph_vertices g_low_level_spec)).
	    {
	      eapply adjacency_matrix_vertex_in_graph; eauto; lia.
	    }
		    pose proof PreH24 as Hlowcost_parent_match.
	    destruct Hlowcost_parent_match as [Hlowcost_parent_range _].
	    pose proof (Hlowcost_parent_range minIndex Hmin_vertex)
	      as [Hmin_lowcost_range _].
		    pose proof (PreH33 minIndex Hmin_lowcost_range) as Hmin_value_range.
		    rewrite PreH18.
	    split; lia.
	  }
	  Exists l_lowcost_2 l_edge_parent_2 u_2 v_2
	    l_edge_parent0_2 l_visited_2 s_2 s_after_2 l_lowcost0_2.
	  repeat (split_pure_spatial || split_pures);
    try (apply derivable1s_coq_prop_r; destruct Hmin_bounds; lia);
	    try (dump_pre_spatial; assumption);
	    try (dump_pre_spatial; lia);
	    try solve [qcp_light_sep | cancel; qcp_light_sep].
	  apply derivable1s_coq_prop_r.
		  eapply scan_matrix_row_prefix_update_snoc.
		  + lia.
				  + exact PreH34.
		  + apply scan_one_matrix_neighbor_update_skip.
		    left.
		    assert (Hj_graph : In j (graph_vertices g_low_level_spec)).
		    { eapply adjacency_matrix_vertex_in_graph; eauto; lia. }
		    apply (proj1 (PreH29 j Hj_graph)).
	    exact PreH1.
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_14_7_boot : prim_adjacency_matrix_entail_wit_14_7_boot.
Proof.
  left.
  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec l_visited_2 l_lowcost0_2 l_lowcost_2
    l_edge_parent0_2 l_edge_parent_2 s_after_2 row_ptr j minIndex i
    min visited lowcost
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
    PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
    PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40.
  sep_apply (int_array_missing_store_merge_to_full
    row_ptr j
    (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
    (Znth minIndex matrix_low_level_spec nil)); try lia.
  rewrite replace_Znth_Znth by lia.
  Exists l_lowcost_2 l_edge_parent_2 l_edge_parent0_2
    l_lowcost0_2 l_visited_2 s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [qcp_light_sep | cancel; qcp_light_sep].
  apply derivable1s_coq_prop_r.
		  eapply scan_matrix_row_prefix_update_snoc.
		  - lia.
			  - exact PreH38.
  - apply scan_one_matrix_neighbor_update_skip.
    right; left.
    unfold matrix_entry.
    exact PreH1.
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_14_8_boot : prim_adjacency_matrix_entail_wit_14_8_boot.
Proof.
  left.
  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec l_visited_2 l_lowcost0_2 l_lowcost_2
    l_edge_parent0_2 l_edge_parent_2 s_2 s_after_2 u_2 v_2 row_ptr
    j minIndex i min visited lowcost
	    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
		    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
		    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
		    PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
		    PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
		    PreH42 PreH43 PreH44 PreH45.
  sep_apply (int_array_missing_store_merge_to_full
    row_ptr j
    (Zlength (Znth minIndex matrix_low_level_spec nil))
    (Znth j (Znth minIndex matrix_low_level_spec nil) 0)
    (Znth minIndex matrix_low_level_spec nil)); try lia.
  rewrite replace_Znth_Znth by lia.
  Exists l_lowcost_2 l_edge_parent_2 u_2 v_2 l_edge_parent0_2
    l_visited_2 s_2 s_after_2 l_lowcost0_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [qcp_light_sep | cancel; qcp_light_sep].
		  apply derivable1s_coq_prop_r.
			  eapply scan_matrix_row_prefix_update_snoc.
			  - lia.
				  - exact PreH43.
  - apply scan_one_matrix_neighbor_update_skip.
    right; left.
    unfold matrix_entry.
    exact PreH1.
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_15_1_boot : prim_adjacency_matrix_entail_wit_15_1_boot.
Proof.
  right.
  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec row_ptr l_lowcost_2 l_edge_parent_2
    l_edge_parent0_2 l_lowcost0_2 l_visited_2 s_after_2
    min minIndex i j
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
    PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34.
  assert (Hj_eq : j = n_pre) by lia.
  subst j.
  subst src_low_level_spec.
  subst s_after_2.
  subst minIndex.
  assert (Hscan_full :
    scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec
      1000000000 (initSt g_low_level_spec 0) 0
      (replace_Znth 0 0 (repeat_Z 1000000000 n_pre))
      (default_edge_list n_pre) l_lowcost_2 l_edge_parent_2).
  {
    unfold scan_matrix_row_full_update, scan_matrix_row_prefix_update.
    rewrite <- PreH27.
    rewrite <- PreH28.
    exact PreH30.
  }
  sep_apply_l_atomic (int_ptr_array2_missing_store_row_merge_to_full
    graph_pre 0 n_pre row_ptr matrix_low_level_spec
    (Znth 0 matrix_low_level_spec nil)).
  - apply derivable1s_coq_prop_r; lia.
  -
  rewrite replace_Znth_Znth by lia.
  Exists (default_edge_list n_pre) l_edge_parent_2
    l_visited_2 (initSt g_low_level_spec 0)
    (replace_Znth 0 0 (repeat_Z 1000000000 n_pre)).
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [
      eapply graph_matrix_lib.GraphMatrixPtr.store_graph_intro;
      exact PreH9
    ];
    try solve [apply derivable1s_coq_prop_r; exact Hscan_full];
    try solve [
      apply derivable1s_coq_prop_r;
      replace i with 0 by lia;
      exact PreH21
    ];
    try solve [qcp_light_sep | cancel; qcp_light_sep].
  + apply derivable1s_coq_prop_r.
    apply initSt_selected_edges_match_state.
  + apply derivable1s_coq_prop_r.
    eapply scan_matrix_row_full_update_lowcost_parent_match_init.
    * unfold prim_adjacency_matrix_graph_model in PreH9.
      exact PreH9.
    * reflexivity.
    * exact PreH11.
    * exact Hscan_full.
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_15_2_boot : prim_adjacency_matrix_entail_wit_15_2_boot.
Proof.
  right.
  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec row_ptr l_lowcost_2
    l_edge_parent_2 u v l_edge_parent0_2 l_visited_2
    s s_after_2 l_lowcost0_2 min minIndex i j
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
    PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
    PreH34 PreH35 PreH36 PreH37 PreH38 PreH39.
  assert (Hj_eq : j = n_pre) by lia.
  subst j.
  pose proof PreH9 as Hmodel.
  unfold prim_adjacency_matrix_graph_model in Hmodel.
  assert (Hscan_full :
    scan_matrix_row_full_update n_pre g_low_level_spec matrix_low_level_spec
      1000000000 s_after_2 minIndex l_lowcost0_2 l_edge_parent0_2
      l_lowcost_2 l_edge_parent_2).
	  {
	    unfold scan_matrix_row_full_update, scan_matrix_row_prefix_update.
	    exact PreH35.
	  }
  sep_apply_l_atomic (int_ptr_array2_missing_store_row_merge_to_full
    graph_pre minIndex n_pre row_ptr matrix_low_level_spec
    (Znth minIndex matrix_low_level_spec nil)).
  - apply derivable1s_coq_prop_r; split; [exact PreH6 | exact PreH7].
  -
  rewrite replace_Znth_Znth by lia.
  Exists l_edge_parent0_2 l_edge_parent_2 l_visited_2 s_after_2 l_lowcost0_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [
      eapply graph_matrix_lib.GraphMatrixPtr.store_graph_intro;
      exact PreH9
    ];
    try solve [qcp_light_sep | cancel; qcp_light_sep].
	  + apply derivable1s_coq_prop_r.
    unfold scan_matrix_row_full_update, scan_matrix_row_prefix_update in Hscan_full.
    eapply scan_matrix_row_update_selected_edges_match_state.
    * exact PreH32.
    * intros cur Hcur.
      destruct PreH25 as [Hrange _].
      exact (Hrange cur Hcur).
    * intros cur Hcur.
      rewrite <- In_Zrange in Hcur.
      eapply adjacency_matrix_vertex_in_graph; eauto.
    * exact Hscan_full.
	  + apply derivable1s_coq_prop_r.
    apply (scan_matrix_row_full_update_lowcost_parent_match_after_add
      n_pre matrix_low_level_spec g_low_level_spec 1000000000
      s s_after_2 l_lowcost0_2 l_edge_parent0_2
      l_lowcost_2 l_edge_parent_2 minIndex).
	    * exact Hmodel.
    * exact PreH25.
    * exact PreH28.
    * exact Hscan_full.
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_16_1_boot : prim_adjacency_matrix_entail_wit_16_1_boot.
Proof.
  left.
  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec l_visited_2 l_lowcost0 l_lowcost_2
    l_edge_parent0 l_edge_parent_2 s_after_2 i minIndex min visited lowcost
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24.
  Exists l_lowcost_2 l_edge_parent_2
    (replace_Znth minIndex 1 l_visited_2) s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [qcp_light_sep | cancel; qcp_light_sep].
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_16_2_boot : prim_adjacency_matrix_entail_wit_16_2_boot.
Proof.
  left.
  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec l_visited_2 l_lowcost0 l_lowcost_2
    l_edge_parent0 l_edge_parent_2 s_after_2 i minIndex min visited lowcost
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24.
  Exists l_lowcost_2 l_edge_parent_2
    (replace_Znth minIndex 1 l_visited_2) s_after_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [qcp_light_sep | cancel; qcp_light_sep].
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_17_1_running : prim_adjacency_matrix_entail_wit_17_1_running.
Proof.
  left.
  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec l_visited_2 l_lowcost_2 l_edge_parent_2
    s_after i_2 minIndex min lowcost visited l_lowcost_3
    l_edge_parent_3 l_visited_3 s_2 i
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
    PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
    PreH34 PreH35 PreH36 PreH37.
  Exists l_lowcost_3 l_edge_parent_3 l_visited_3 s_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [apply derivable1s_coq_prop_r; apply min_vertex_in_range_empty];
    try solve [qcp_light_sep | cancel; qcp_light_sep].
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_17_2_running : prim_adjacency_matrix_entail_wit_17_2_running.
Proof.
  left.
  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec l_visited_2 l_lowcost_2 l_edge_parent_2
    s_after i_2 minIndex min lowcost visited l_lowcost_3
    l_edge_parent_3 l_visited_3 s_2 i
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
    PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33
    PreH34 PreH35 PreH36 PreH37.
  Exists l_lowcost_3 l_edge_parent_3 l_visited_3 s_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [apply derivable1s_coq_prop_r; apply min_vertex_in_range_empty];
    try solve [qcp_light_sep | cancel; qcp_light_sep].
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_18_1_running : prim_adjacency_matrix_entail_wit_18_1_running.
Proof.
  left.
  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec l_visited l_lowcost l_edge_parent s_after
    i minIndex min visited lowcost
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    PreH18 PreH19 PreH20 PreH21.
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  unfold prim_adjacency_matrix_graph_model in Hgraph_model.
  Exists l_lowcost l_edge_parent l_visited s_after.
  pose proof (prim_connected _ _ PreH11) as Hconnected.
  pose proof (state_vertex_count_positive_exists
    s_after (proj1 PreH14) ltac:(rewrite PreH16; lia)) as Hnonempty.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [
      apply derivable1s_coq_prop_r;
      intros Hlt;
      eapply unfinished_connected_state_has_candidate_vertex_by_count;
      eauto;
      rewrite PreH16; exact Hlt
    ];
    try solve [
      apply derivable1s_coq_prop_r;
      replace ((i + 1) - 1) with i by lia;
      exact PreH21
    ];
    try solve [qcp_light_sep | cancel; qcp_light_sep].
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_18_2_running : prim_adjacency_matrix_entail_wit_18_2_running.
Proof.
  left.
  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec l_visited l_lowcost l_edge_parent s_after
    i_2 minIndex_2 min_2 visited lowcost
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    PreH18 PreH19 PreH20 PreH21.
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  unfold prim_adjacency_matrix_graph_model in Hgraph_model.
  Exists l_lowcost l_edge_parent l_visited s_after.
  pose proof (prim_connected _ _ PreH11) as Hconnected.
  pose proof (state_vertex_count_positive_exists
    s_after (proj1 PreH14) ltac:(rewrite PreH16; lia)) as Hnonempty.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [
      apply derivable1s_coq_prop_r;
      intros Hlt;
      eapply unfinished_connected_state_has_candidate_vertex_by_count;
      eauto;
      rewrite PreH16; exact Hlt
    ];
    try solve [
      apply derivable1s_coq_prop_r;
      replace ((i_2 + 1) - 1) with i_2 by lia;
      exact PreH21
    ];
    try solve [qcp_light_sep | cancel; qcp_light_sep].
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_19_1_running : prim_adjacency_matrix_entail_wit_19_1_running.
Proof.
  left.
  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec l_visited_2 l_lowcost_2 l_edge_parent_2
    s_after i minIndex min lowcost visited l_lowcost_3 l_edge_parent_3
    l_visited_3 s_2 i_2
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  unfold prim_adjacency_matrix_graph_model in Hgraph_model.
  assert (Hsafe_ret :
    safeExec (prim_state_is s_2) (return tt) X_low_level_spec).
  {
    eapply Prim2_loop_finish with
      (n := n_pre) (matrix := matrix_low_level_spec)
      (inf := 1000000000) (i := i_2).
    - exact (prim_graph_valid g_low_level_spec src_low_level_spec PreH8).
    - exact Hgraph_model.
    - lia.
    - lia.
    - exact PreH17.
  }
  Exists l_edge_parent_3 l_visited_3 s_2 l_lowcost_3.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; exact Hsafe_ret);
    try (dump_pre_spatial; rewrite PreH11; lia);
    try (dump_pre_spatial; unfold lowcost_prefix_sum; simpl; reflexivity);
    try (dump_pre_spatial; lia);
    try solve [qcp_light_sep | cancel; qcp_light_sep].
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_19_2_running : prim_adjacency_matrix_entail_wit_19_2_running.
Proof.
  left.
  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec l_visited_2 l_lowcost_2 l_edge_parent_2
    s_after i minIndex min lowcost visited l_lowcost_3 l_edge_parent_3
    l_visited_3 s_2 i_2
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37.
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  unfold prim_adjacency_matrix_graph_model in Hgraph_model.
  assert (Hsafe_ret :
    safeExec (prim_state_is s_2) (return tt) X_low_level_spec).
  {
    eapply Prim2_loop_finish with
      (n := n_pre) (matrix := matrix_low_level_spec)
      (inf := 1000000000) (i := i_2).
    - exact (prim_graph_valid g_low_level_spec src_low_level_spec PreH8).
    - exact Hgraph_model.
    - lia.
    - lia.
    - exact PreH17.
  }
  Exists l_edge_parent_3 l_visited_3 s_2 l_lowcost_3.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; exact Hsafe_ret);
    try (dump_pre_spatial; rewrite PreH11; lia);
    try (dump_pre_spatial; unfold lowcost_prefix_sum; simpl; reflexivity);
    try (dump_pre_spatial; lia);
    try solve [qcp_light_sep | cancel; qcp_light_sep].
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_20_running : prim_adjacency_matrix_entail_wit_20_running.
Proof.
  left.
  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec lowcost visited l_edge_parent_2 l_visited_2
    s_2 l_lowcost_2 ret i
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
  Exists l_edge_parent_2 l_visited_2 s_2 l_lowcost_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; rewrite PreH4, lowcost_prefix_sum_snoc by lia; reflexivity);
    try (dump_pre_spatial; lia);
    try solve [qcp_light_sep | cancel; qcp_light_sep].
Qed.

Lemma proof_of_prim_adjacency_matrix_entail_wit_21_running : prim_adjacency_matrix_entail_wit_21_running.
Proof.
  left.
  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec lowcost visited l_edge_parent_2 l_visited_2
    s_2 l_lowcost_2 ret i
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
	  assert (Hi_eq : i = n_pre) by lia.
	  subst i.
	  prop_apply (IntArray.full_Zlength lowcost n_pre l_lowcost_2).
	  Intros_p Hlowcost_len.
  prop_apply (@graph_matrix_lib.GraphMatrixPtr.store_graph_model n_pre
    (prim_adjacency_matrix_graph_model n_pre g_low_level_spec 1000000000)
    graph_pre matrix_low_level_spec).
  Intros_p Hgraph_model.
  unfold prim_adjacency_matrix_graph_model in Hgraph_model.
	  assert (Hprefix_full :
	    lowcost_prefix_sum n_pre l_lowcost_2 =
	    graph_total_weight s_2.(Prim.graph_in_state)).
  {
    eapply lowcost_prefix_sum_full_state.
    - exact Hgraph_model.
    - exact PreH10.
    - exact PreH12.
    - exact PreH15.
  }
  assert (Hsafe_graph :
    safeExec
      (prim_state_graph_matches s_2.(Prim.graph_in_state))
      (return tt) X_low_level_spec).
  {
    eapply safeExec_conseq; [exact PreH17|].
    intros st Hst.
    unfold prim_state_is in Hst.
    subst st.
    unfold prim_state_graph_matches.
    reflexivity.
  }
  assert (Hresult_weight :
    prim_result_weight s_2.(Prim.graph_in_state) ret).
  {
    unfold prim_result_weight.
    rewrite <- Hprefix_full.
    exact PreH4.
  }
  assert (Hresult_range :
    prim_result_weight_in_int64_range s_2.(Prim.graph_in_state)).
  {
    unfold prim_result_weight_in_int64_range.
    rewrite <- Hprefix_full.
    assert (Hprefix_bound :
      0 <= lowcost_prefix_sum n_pre l_lowcost_2 <=
        n_pre * 1000000000).
	    {
	      apply lowcost_prefix_sum_bound; try lia.
	      intros v Hv.
	      rewrite <- In_Zrange in Hv.
	      apply PreH16. rewrite Hlowcost_len. lia.
	    }
    destruct PreH8 as [_ Htotal_bound].
    split; lia.
  }
  Exists s_2.(Prim.graph_in_state) l_edge_parent_2 l_visited_2 s_2 l_lowcost_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; exact Hsafe_graph);
    try (dump_pre_spatial; exact Hresult_weight);
    try (dump_pre_spatial; exact Hresult_range);
    try (dump_pre_spatial; unfold prim_state_graph_matches; reflexivity);
    try (dump_pre_spatial; lia);
    try solve [qcp_light_sep | cancel; qcp_light_sep].
Qed.

Lemma proof_of_prim_adjacency_matrix_return_wit_1_running : prim_adjacency_matrix_return_wit_1_running.
Proof.
  left.
  intros graph_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
    matrix_low_level_spec l_edge_parent s rg_2 ret l_visited l_lowcost
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17.
  Exists rg_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try solve [qcp_light_sep | cancel; qcp_light_sep].
Qed.

Lemma proof_of_prim_adjacency_matrix_derive_high_level_spec_by_low_level_spec : prim_adjacency_matrix_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists matrix_high_level_spec g_high_level_spec src_high_level_spec
    (result_state (initStPred g_high_level_spec src_high_level_spec)
       (Prim2 g_high_level_spec)).
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try (dump_pre_spatial;
      apply safeExec_result_state;
      exists (initSt g_high_level_spec src_high_level_spec);
      reflexivity).
  cancel (graph_matrix_lib.GraphMatrixPtr.store_graph n_pre
    (prim_adjacency_matrix_graph_model n_pre g_high_level_spec 1000000000)
    graph_pre matrix_high_level_spec).
  apply derivable1_wand_sepcon_adjoint.
  Intros rg_2 retval_2.
  assert (Hresult_mst : return_is_mst g_high_level_spec rg_2).
  {
    match goal with
    | Hsafe : safeExec (prim_state_graph_matches rg_2) (return tt)
        (result_state (initStPred g_high_level_spec src_high_level_spec)
          (Prim2 g_high_level_spec)),
      Henv : PrimEnv g_high_level_spec src_high_level_spec |- _ =>
        unfold safeExec, safe in Hsafe;
        destruct Hsafe as [sigma [Hgraph Hsafe]];
        rewrite wp_ret in Hsafe;
        sets_unfold in Hsafe;
        unfold result_state in Hsafe;
        destruct Hsafe as [s0 [Hinit Hrun]];
        pose proof (Prim2_correct_concrete
          g_high_level_spec src_high_level_spec Henv) as Hhoare;
        unfold Hoare in Hhoare;
        specialize (Hhoare s0 tt sigma Hinit Hrun);
        unfold prim_state_graph_matches in Hgraph;
        rewrite <- Hgraph;
        exact Hhoare
    end.
  }
  Exists rg_2 retval_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; exact Hresult_mst);
    try solve [qcp_light_sep | cancel; qcp_light_sep].
Qed.
