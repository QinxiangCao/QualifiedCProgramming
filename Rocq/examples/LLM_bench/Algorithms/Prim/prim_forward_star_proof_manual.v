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
From SimpleC.EE.LLM_bench.Algorithms.Prim Require Import prim_forward_star_goal.
From SimpleC.EE.LLM_bench.Algorithms.Prim Require Import prim_forward_star_proof_auto.
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
Require Import SimpleC.EE.LLM_bench.Algorithms.Prim.prim_forward_star_lib.
Require Import ListLib.Base.Positional.
Require Import SumLib.ZRange.
Local Open Scope sac.

Lemma proof_of_prim_entail_wit_1 : prim_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  
  Exists (@nil Z) (@nil Z) (@nil Z).
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval_4 (2 * m_pre)).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval_5 (2 * m_pre)).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval_6 (2 * m_pre)).
    change (2 * 0) with 0.
    rewrite (IntArray.seg_empty retval_4 0 0).
    rewrite (IntArray.seg_empty retval_5 0 0).
    rewrite (IntArray.seg_empty retval_6 0 0).
    entailer!.
  - split_pures; try (dump_pre_spatial; assumption); try (dump_pre_spatial; lia).
    entailer!.
    apply directed_array_graph_prefix_0_nil.
    rewrite (array_graph_edge_count
               n_pre m_pre lf_low_level_spec lt_low_level_spec
               lw_low_level_spec g_low_level_spec PreH10).
    lia.
Qed. 

Lemma proof_of_prim_entail_wit_2 : prim_entail_wit_2.
Proof.
   LLM_pre_process ltac:(int_auto).
  Exists ((l_from_new_prefix_2 ++ (Znth i lf_low_level_spec 0 :: nil)) ++
            (Znth i lt_low_level_spec 0 :: nil))
         ((l_to_new_prefix_2 ++ (Znth i lt_low_level_spec 0 :: nil)) ++
            (Znth i lf_low_level_spec 0 :: nil))
         ((l_weight_new_prefix_2 ++ (Znth i lw_low_level_spec 0 :: nil)) ++
            (Znth i lw_low_level_spec 0 :: nil)).
  split_pure_spatial.
  - replace (2 * (i + 1)) with (2 * i + 1 + 1) by lia.
    entailer!.
  - split_pures; try (dump_pre_spatial; assumption); try (dump_pre_spatial; lia).
    entailer!.
    apply (directed_array_graph_prefix_snoc
             n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
             g_low_level_spec i); [assumption | assumption | lia].
Qed. 

Lemma proof_of_prim_entail_wit_3_split_goal_1 : prim_entail_wit_3_split_goal_1.
Proof.
  pre_process.
  entailer!.
  apply (directed_array_graph_prefix_finish
           g_low_level_spec
           l_from_new_prefix l_to_new_prefix l_weight_new_prefix i);
    try assumption.
  - rewrite (array_graph_edge_count
               n_pre m_pre lf_low_level_spec lt_low_level_spec
               lw_low_level_spec g_low_level_spec PreH12).
    lia.
  - rewrite (array_graph_edge_count
               n_pre m_pre lf_low_level_spec lt_low_level_spec
               lw_low_level_spec g_low_level_spec PreH12).
    lia.
Qed.









Lemma proof_of_prim_entail_wit_3 : prim_entail_wit_3.
Proof.
  aggressive_pre_process.
  - exact (proof_of_prim_entail_wit_3_split_goal_1
             m_pre n_pre X_low_level_spec src_low_level_spec
             g_low_level_spec lw_low_level_spec lt_low_level_spec
             lf_low_level_spec
             l_from_new_prefix l_to_new_prefix l_weight_new_prefix i
             PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
             PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15).
  - exact PreH11.
  - exact PreH10.
  - exact PreH9.
  - change (repeat_Z (-1) 0) with (@nil Z); reflexivity.
  
Qed. 

Lemma proof_of_prim_entail_wit_4_split_goal_1 : prim_entail_wit_4_split_goal_1.
Proof.
  pre_process.
  rewrite <- repeat_Z_tail by lia.
  entailer!.
Qed.

Lemma proof_of_prim_entail_wit_4 : prim_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_entail_wit_4_split_goal_1.
Qed. 









Lemma proof_of_prim_entail_wit_5_split_goal_5 : prim_entail_wit_5_split_goal_5.
Proof.
  pre_process;
  replace i with n_pre by lia.
  entailer!.
Qed.

Lemma proof_of_prim_entail_wit_5 : prim_entail_wit_5.
Proof.
  aggressive_pre_process.
  - exact PreH11.
  - exact PreH10.
  - exact PreH9.
  - change (repeat_Z (-1) 0) with (@nil Z); reflexivity.
  - Goal_apply proof_of_prim_entail_wit_5_split_goal_5.
Qed. 

Lemma proof_of_prim_entail_wit_6_split_goal_1 : prim_entail_wit_6_split_goal_1.
Proof.
  pre_process.
  rewrite <- repeat_Z_tail by lia.
  entailer!.
Qed.

Lemma proof_of_prim_entail_wit_6 : prim_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_entail_wit_6_split_goal_1.
Qed. 

Lemma proof_of_prim_entail_wit_7_split_goal_1 : prim_entail_wit_7_split_goal_1.
Proof.
  pre_process.
  replace i with (2 * m_pre) by lia.
  entailer!.
  apply first_link_matches_inserted_vertex_directed_edges_empty.
  - unfold repeat_Z.
    rewrite Zlength_correct, repeat_length.
    pose proof (array_graph_vertex_count _ _ _ _ _ _ PreH12).
    lia.
  - unfold repeat_Z.
    rewrite Zlength_correct, repeat_length.
    pose proof (array_graph_edge_count _ _ _ _ _ _ PreH12).
    lia.
  - intros v Hv.
    assert (Hv_range : 0 <= v < n_pre) by
      (eapply array_graph_vertex_range; eauto).
    unfold repeat_Z.
    rewrite Znth_repeat_lt.
    reflexivity.
    rewrite Z2Nat.id by lia.
    lia.
Qed.







Lemma proof_of_prim_entail_wit_7 : prim_entail_wit_7.
Proof.
  aggressive_pre_process.
  - exact (proof_of_prim_entail_wit_7_split_goal_1
             m_pre n_pre X_low_level_spec src_low_level_spec
             g_low_level_spec lw_low_level_spec lt_low_level_spec
             lf_low_level_spec
             l_from_new_2 l_to_new_2 l_weight_new_2 i
             PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
             PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15).
  - exact PreH11.
  - exact PreH10.
  - exact PreH9.
Qed. 







Lemma proof_of_prim_entail_wit_8_split_goal_4 : prim_entail_wit_8_split_goal_4.
Proof.
  pre_process.
  entailer!.
  pose proof (directed_array_graph_from_range
    n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
    g_low_level_spec l_from_new l_to_new_2 l_weight_new_2 i
    PreH12 PreH14
    (fun e He => PreH9 e He)
    (fun e He => PreH10 e He)
    ltac:(lia)) as Hrange.
  exact (proj2 Hrange).
Qed.

Lemma proof_of_prim_entail_wit_8_split_goal_5 : prim_entail_wit_8_split_goal_5.
Proof.
  pre_process.
  entailer!.
  pose proof (directed_array_graph_from_range
    n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
    g_low_level_spec l_from_new l_to_new_2 l_weight_new_2 i
    PreH12 PreH14
    (fun e He => PreH9 e He)
    (fun e He => PreH10 e He)
    ltac:(lia)) as Hrange.
  exact (proj1 Hrange).
Qed.

Lemma proof_of_prim_entail_wit_8 : prim_entail_wit_8.
Proof.
  aggressive_pre_process.
  - exact PreH11.
  - exact PreH10.
  - exact PreH9.
  - Goal_apply proof_of_prim_entail_wit_8_split_goal_4.
  - Goal_apply proof_of_prim_entail_wit_8_split_goal_5.
Qed. 

Lemma proof_of_prim_entail_wit_9_split_goal_1 : prim_entail_wit_9_split_goal_1.
Proof.
  pre_process.
  entailer!.
  eapply first_link_matches_inserted_vertex_directed_edges_insert; eauto.
  - eapply array_graph_vertex_in; eauto; lia.
  - intros v Hv.
    pose proof PreH17 as Hmatch_len.
    destruct Hmatch_len as [Hfirst_len _].
    pose proof (array_graph_vertex_count _ _ _ _ _ _ PreH14) as Hvertex_count.
    pose proof (array_graph_vertex_range
      n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
      g_low_level_spec v PreH14 Hv) as Hv_range.
    lia.
  - pose proof PreH17 as Hmatch_len.
    destruct Hmatch_len as [_ [Hlink_len _]].
    pose proof (array_graph_edge_count _ _ _ _ _ _ PreH14) as Hedge_count.
    lia.
Qed.







Lemma proof_of_prim_entail_wit_9 : prim_entail_wit_9.
Proof.
  aggressive_pre_process.
  - exact (proof_of_prim_entail_wit_9_split_goal_1
             m_pre n_pre X_low_level_spec src_low_level_spec
             g_low_level_spec lw_low_level_spec lt_low_level_spec
             lf_low_level_spec l_first_2 l_link_2
             l_from_new_2 l_to_new_2 l_weight_new_2
             i u
             PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
             PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
             PreH16 PreH17 PreH18).
  - exact PreH13.
  - exact PreH12.
  - exact PreH11.
Qed. 

Lemma proof_of_prim_entail_wit_10_split_goal_1 : prim_entail_wit_10_split_goal_1.
Proof.
  pre_process.
  entailer!.
  assert (Hi_eq : i = 2 * graph_edge_count g_low_level_spec).
  {
    pose proof (array_graph_edge_count _ _ _ _ _ _ PreH12) as Hedge_count.
    lia.
  }
  rewrite Hi_eq in PreH15.
  apply first_link_matches_inserted_vertex_directed_edges_finish.
  exact PreH15.
Qed.













Lemma proof_of_prim_entail_wit_10 : prim_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_entail_wit_10_split_goal_1.
  - exact PreH11.
  - exact PreH10.
  - exact PreH9.
  - change (repeat_Z 1000000000 0) with (@nil Z); reflexivity.
  - change (repeat_Z 0 0) with (@nil Z); reflexivity.
  - change (repeat_Z (-1) 0) with (@nil Z); reflexivity.
Qed. 

Lemma proof_of_prim_entail_wit_11_split_goal_1 : prim_entail_wit_11_split_goal_1.
Proof.
  pre_process.
  rewrite <- repeat_Z_tail by lia.
  entailer!.
Qed.

Lemma proof_of_prim_entail_wit_11_split_goal_2 : prim_entail_wit_11_split_goal_2.
Proof.
  pre_process.
  rewrite <- repeat_Z_tail by lia.
  entailer!.
Qed.

Lemma proof_of_prim_entail_wit_11_split_goal_3 : prim_entail_wit_11_split_goal_3.
Proof.
  pre_process.
  rewrite <- repeat_Z_tail by lia.
  entailer!.
Qed.

Lemma proof_of_prim_entail_wit_11 : prim_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_prim_entail_wit_11_split_goal_2.
  - Goal_apply proof_of_prim_entail_wit_11_split_goal_3.
Qed. 







Lemma proof_of_prim_entail_wit_12_split_goal_4 : prim_entail_wit_12_split_goal_4.
Proof.
  pre_process.
  replace i with n_pre by lia.
  entailer!.
Qed.

Lemma proof_of_prim_entail_wit_12_split_goal_5 : prim_entail_wit_12_split_goal_5.
Proof.
  pre_process.
  replace i with n_pre by lia.
  entailer!.
Qed.

Lemma proof_of_prim_entail_wit_12_split_goal_6 : prim_entail_wit_12_split_goal_6.
Proof.
  pre_process.
  replace i with n_pre by lia.
  entailer!.
Qed.

Lemma proof_of_prim_entail_wit_12 : prim_entail_wit_12.
Proof.
  aggressive_pre_process.
  - exact PreH11.
  - exact PreH10.
  - exact PreH9.
  - Goal_apply proof_of_prim_entail_wit_12_split_goal_4.
  - Goal_apply proof_of_prim_entail_wit_12_split_goal_5.
  - Goal_apply proof_of_prim_entail_wit_12_split_goal_6.
Qed. 







Lemma proof_of_prim_entail_wit_13_boot : prim_entail_wit_13_boot.
Proof.
  right.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 







Lemma proof_of_prim_entail_wit_14_boot : prim_entail_wit_14_boot.
Proof.
  aggressive_pre_process.
  - exact PreH22.
  - exact PreH21.
  - exact PreH20.
Qed. 

Lemma proof_of_prim_entail_wit_15_1_boot_split_goal_1 : prim_entail_wit_15_1_boot_split_goal_1.
Proof.
  pre_process.
  assert (Hj0 : j = 0).
  {
    destruct (Z.eq_dec j 0) as [Heq | Hneq]; auto.
    assert (Hj_ge_1 : 1 <= j) by lia.
    specialize (PreH21 Hj_ge_1).
    destruct PreH21 as [Hmin _].
    rewrite Hmin in PreH1.
    rewrite PreH23 in PreH1.
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
    - unfold not; intros Hdiff; apply Hneq; symmetry; exact Hdiff.
  }
  rewrite Hj0.
  split; [| reflexivity].
  rewrite PreH23.
  rewrite Znth_replace_Znth_Same.
  - reflexivity.
  - unfold repeat_Z.
    rewrite Zlength_correct, repeat_length.
    lia.
Qed.

Lemma proof_of_prim_entail_wit_15_1_boot : prim_entail_wit_15_1_boot.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_entail_wit_15_1_boot_split_goal_1.
Qed. 

Lemma proof_of_prim_entail_wit_15_2_boot : prim_entail_wit_15_2_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hmin_next :
    min_vertex_in_range
      g_low_level_spec s_2 (j + 1) 1000000000 j
      l_lowcost_2 l_edge_parent_2).
  {
    eapply min_vertex_in_range_take_current;
	      [ exact PreH14
	      | exact PreH22
	      | exact PreH25
	      | exact PreH27
	      | lia
	      | exact PreH2
	      | exact PreH1
	      | exact PreH28
	      | exact PreH29 ].
  }
  Exists l_lowcost_2 l_edge_parent_2 l_visited_2 s_2
         l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [entailer! | cancel].
  Unshelve.
  all: try solve [entailer! | cancel | lia | assumption | reflexivity].
Qed. 

Lemma proof_of_prim_entail_wit_15_3_boot_split_goal_1 : prim_entail_wit_15_3_boot_split_goal_1.
Proof.
  pre_process.
  assert (Hj_pos : 1 <= j).
  {
    destruct (Z.eq_dec j 0) as [Heq | Hneq].
    - subst j.
      destruct (PreH20 eq_refl) as [Hmin _].
      subst min.
      rewrite PreH23 in PreH1.
      rewrite Znth_replace_Znth_Same in PreH1.
      + lia.
      + unfold repeat_Z.
        rewrite Zlength_correct, repeat_length.
        lia.
    - lia.
  }
  destruct (PreH21 Hj_pos) as [Hmin HminIndex].
  entailer!.
Qed.

Lemma proof_of_prim_entail_wit_15_3_boot : prim_entail_wit_15_3_boot.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_entail_wit_15_3_boot_split_goal_1.
Qed. 

Lemma proof_of_prim_entail_wit_15_4_boot : prim_entail_wit_15_4_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hmin_next :
    min_vertex_in_range
      g_low_level_spec s_2 (j + 1) 1000000000 minIndex
      l_lowcost_2 l_edge_parent_2).
  {
    eapply min_vertex_in_range_skip_not_better;
	      [ exact PreH14
	      | exact PreH22
	      | exact PreH25
	      | exact PreH27
	      | lia
	      | exact PreH2
	      | exact PreH1
	      | exact PreH28
	      | exact PreH29 ].
  }
  Exists l_lowcost_2 l_edge_parent_2 l_visited_2 s_2
         l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [entailer! | cancel].
  Unshelve.
  all: try solve [entailer! | cancel | dump_pre_spatial; assumption | dump_pre_spatial; lia].
Qed. 

Lemma proof_of_prim_entail_wit_15_5_boot_split_goal_1 : prim_entail_wit_15_5_boot_split_goal_1.
Proof.
  pre_process.
  exfalso.
  rewrite PreH23 in PreH1.
  unfold repeat_Z in PreH1.
  rewrite Znth_repeat_lt in PreH1.
  - lia.
  - rewrite Z2Nat.id by lia.
    lia.
Qed.

Lemma proof_of_prim_entail_wit_15_5_boot : prim_entail_wit_15_5_boot.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_entail_wit_15_5_boot_split_goal_1.
Qed. 

Lemma proof_of_prim_entail_wit_15_6_boot : prim_entail_wit_15_6_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hmin_next :
    min_vertex_in_range
      g_low_level_spec s_2 (j + 1) 1000000000 minIndex
      l_lowcost_2 l_edge_parent_2).
  {
    eapply min_vertex_in_range_skip_visited;
	      [ exact PreH13
	      | exact PreH21
	      | exact PreH26
	      | lia
	      | exact PreH1 ].
  }
  Exists l_lowcost_2 l_edge_parent_2 l_visited_2 s_2
         l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [entailer! | cancel].
  Unshelve.
  all: try solve [entailer! | cancel | dump_pre_spatial; assumption | dump_pre_spatial; lia].
Qed. 







Lemma proof_of_prim_entail_wit_16_1_boot : prim_entail_wit_16_1_boot.
Proof.
  right.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_prim_entail_wit_16_2_boot : prim_entail_wit_16_2_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hj_eq : j = n_pre) by lia.
  subst j.
  assert (Hcand_exists :
    candidate_vertex_exists_in_range
      n_pre g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2 1000000000).
  { apply PreH24; lia. }
  assert (HminIndex_not_minus_one : minIndex <> -1).
  {
    eapply min_vertex_in_range_not_minus_one; eauto.
  }
  assert (HminIndex_range : 0 <= minIndex < n_pre).
  {
    pose proof PreH28 as Hrange.
    apply Hrange in HminIndex_not_minus_one.
    lia.
  }
  assert (Hmin_value : min = Znth minIndex l_lowcost_2 0).
  { apply PreH27; exact HminIndex_not_minus_one. }
  assert (Hselected :
    selected_parent_edge_is_min_cut_edge
      g_low_level_spec s_2 l_edge_parent_2 minIndex).
  {
    eapply min_vertex_parent_is_min_cut_edge; eauto.
  }
  Exists l_lowcost_2 l_edge_parent_2 l_visited_2 s_2
         l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try solve [entailer! | cancel].
  Unshelve.
  all: try solve [entailer! | cancel | lia | assumption | reflexivity].
Qed. 

Lemma proof_of_prim_entail_wit_17_1_boot : prim_entail_wit_17_1_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hsrc_graph : In src_low_level_spec (graph_vertices g_low_level_spec)).
  {
    subst src_low_level_spec.
    eapply array_graph_vertex_in; eauto; lia.
  }
  assert (Hvisited_init :
    visited_matches_state g_low_level_spec
      (initSt g_low_level_spec src_low_level_spec)
      (replace_Znth minIndex 1 l_visited_2)).
  {
    rewrite PreH19, PreH21.
    unfold visited_matches_state.
    intros v Hv.
    rewrite initSt_vvalid.
    rewrite PreH6.
    destruct (Z.eq_dec v 0) as [Hv0 | Hv0].
    - subst v.
      rewrite Znth_replace_Znth_same_local.
      + split; intros _; [reflexivity | lia].
      + unfold repeat_Z.
        rewrite Zlength_correct, repeat_length.
        rewrite Z2Nat.id by lia.
        lia.
    - assert (Hv_range : 0 <= v < n_pre)
        by (eapply array_graph_vertex_range; eauto).
      rewrite Znth_replace_Znth_diff_local.
      + unfold repeat_Z.
        rewrite Znth_repeat_lt by lia.
        split; intros H; [contradiction | contradiction].
      + unfold repeat_Z.
        rewrite Zlength_correct, repeat_length.
        rewrite Z2Nat.id by lia.
        lia.
      + unfold repeat_Z.
        rewrite Zlength_correct, repeat_length.
        rewrite Z2Nat.id by lia.
        lia.
      + intro Heq; apply Hv0; symmetry; exact Heq.
  }
  assert (Hstate_after :
    selected_state_after_add
      g_low_level_spec src_low_level_spec i n_pre
      (initSt g_low_level_spec src_low_level_spec)
      (initSt g_low_level_spec src_low_level_spec)
      l_from_new_2 l_to_new_2 (repeat_Z (-1) n_pre)
      (replace_Znth 0 0 (repeat_Z 1000000000 n_pre))
      (repeat_Z 0 n_pre) minIndex).
  {
    left.
    split.
    - exact PreH16.
    - split.
      + rewrite PreH19, PreH6. reflexivity.
      + split.
        * unfold initStPred. reflexivity.
        * split.
          -- rewrite PreH6. reflexivity.
          -- split.
             ++ reflexivity.
             ++ split.
                ** reflexivity.
                ** rewrite <- PreH21. exact Hvisited_init.
  }
  assert (Hsafe :
    safeExec
      (prim_state_is (initSt g_low_level_spec src_low_level_spec))
      (Prim2_loop g_low_level_spec i) X_low_level_spec).
  {
    rewrite PreH16.
    unfold Prim2, Prim2_loop, initStPred, prim_state_is in *.
    exact PreH17.
  }
	  assert (Hstate_count_after :
	    state_vertex_count (initSt g_low_level_spec src_low_level_spec) = i + 1).
	  {
	    rewrite PreH16.
	    rewrite initSt_state_vertex_count.
	    lia.
	  }
  assert (Hparent_after :
    parent_edges_match_state
      g_low_level_spec src_low_level_spec
      (initSt g_low_level_spec src_low_level_spec) l_edge_parent_2).
  {
    unfold parent_edges_match_state.
    split.
    - apply initSt_vvalid; reflexivity.
    - split.
      + intros v _ Hv_not_src Hv_valid.
        apply initSt_vvalid in Hv_valid.
        contradiction.
      + intros e.
        split.
        * intro He.
          unfold initSt in He.
          simpl in He.
          unfold empty_graph_of, graph_instance, edge_valid in He.
          simpl in He.
          contradiction.
        * intros [v [_ [Hv_not_src [Hv _]]]].
          apply initSt_vvalid in Hv.
          contradiction.
  }
	  assert (Hscan :
    scan_minIndex_adjacency_prefix_update
      g_low_level_spec
      (initSt g_low_level_spec src_low_level_spec)
      l_from_new_2 l_first l_link_2 l_to_new_2 l_weight_new_2
      minIndex (Znth minIndex l_first 0)
      (replace_Znth 0 0 (repeat_Z 1000000000 n_pre))
      (repeat_Z (-1) n_pre)
      l_lowcost_2 l_edge_parent_2).
  {
    rewrite PreH19, PreH20, PreH22.
    eapply scan_minIndex_adjacency_prefix_start; eauto.
    rewrite <- PreH19.
    eapply array_graph_vertex_in; eauto.
  }
	  Exists l_lowcost_2 l_edge_parent_2
	         (initSt g_low_level_spec src_low_level_spec)
	         (initSt g_low_level_spec src_low_level_spec)
	         (repeat_Z (-1) n_pre)
	         (repeat_Z 0 n_pre)
	         (replace_Znth 0 0 (repeat_Z 1000000000 n_pre))
	         l_first l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2.
	  rewrite PreH20, PreH21, PreH22.
  rewrite PreH20 in Hscan.
  rewrite PreH22 in Hscan.
  rewrite PreH22 in Hparent_after.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; exact Hstate_after);
    try (dump_pre_spatial; exact Hsafe);
    try (dump_pre_spatial; exact Hstate_count_after);
    try (dump_pre_spatial; exact Hparent_after);
    try (dump_pre_spatial; exact Hscan);
    try (dump_pre_spatial; lia);
    try solve [entailer! | cancel].
Qed. 

Lemma proof_of_prim_entail_wit_17_2_boot : prim_entail_wit_17_2_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  prop_apply (IntArray.full_Zlength visited n_pre (replace_Znth minIndex 1 l_visited_2)).
  Intros_p Hvisited_replace_len.
  assert (Hvisited_len : Zlength l_visited_2 = n_pre).
  {
    rewrite <- Hvisited_replace_len.
    symmetry.
    apply Zlength_replace_Znth_local.
  }
	  assert (Hcand_minIndex :
	    candidate_vertex
	      g_low_level_spec s_2 l_lowcost_2 l_edge_parent_2
	      1000000000 minIndex).
	  {
	    destruct PreH28 as [[Hminus _] | [Hcand _]].
	    - contradiction.
	    - exact Hcand.
	  }
  pose proof Hcand_minIndex as Hcand_minIndex_for_graph.
  destruct Hcand_minIndex_for_graph as [HminIndex_graph _].
  assert (Hg_valid : graph_wf g_low_level_spec).
  {
    eapply array_graph_gvalid; eauto.
  }
	  destruct (selected_parent_add_to_mst_exists
	    n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
	    g_low_level_spec s_2 l_from_new_2 l_to_new_2
	    l_lowcost_2 l_edge_parent_2 minIndex
	    PreH12 PreH9 PreH10 PreH19 PreH28 PreH1)
	    as [x_u [x_v [s_next [Hpair [Hadd Hcount_next]]]]].
  assert (Hstate_count_next : state_vertex_count s_next = i + 1).
  {
    rewrite Hcount_next.
    rewrite PreH21.
    lia.
  }
  assert (Hsafe_next :
    safeExec (prim_state_is s_next)
      (Prim2_loop g_low_level_spec i) X_low_level_spec).
  {
    eapply selected_parent_prim2_loop_step; eauto.
  }
	  assert (Hvisited_next :
	    visited_matches_state g_low_level_spec s_next
	      (replace_Znth minIndex 1 l_visited_2)).
	  {
	    eapply selected_parent_add_to_mst_visited_matches; eauto.
	  }
  assert (Hparent_next :
    parent_edges_match_state
      g_low_level_spec src_low_level_spec s_next l_edge_parent_2).
  {
    unfold parent_edges_match_state in *.
    destruct PreH22 as [Hsrc_old [Hparent_range_old Hparent_exact_old]].
    pose proof Hadd as Hadd_for_edge.
    destruct Hadd_for_edge as [u_add [v_add [Hpair_add Hadd_edge]]].
    destruct Hadd_edge as [Hadd_vvalid Hadd_evalid Hadd_step].
    split.
    - eapply selected_parent_add_to_mst_old_vvalid; eauto.
    - split.
      + intros v Hv_in Hv_not_src Hv_next.
        rewrite (selected_parent_add_to_mst_vvalid
          g_low_level_spec s_2 s_next
          l_from_new_2 l_to_new_2 l_edge_parent_2 minIndex v Hadd)
          in Hv_next.
        destruct Hv_next as [Hv_old | Hv_new].
        * eapply Hparent_range_old; eauto.
        * subst v.
          destruct Hcand_minIndex as [_ [_ [_ [Hde_range _]]]].
          exact Hde_range.
      + intros e.
        split.
        * intro He_next.
          apply Hadd_evalid in He_next as [He_old | He_new].
          -- apply Hparent_exact_old in He_old.
             destruct He_old as [v [Hv_graph [Hv_not_src [Hv_old Heq]]]].
             exists v.
             split; [exact Hv_graph |].
             split; [exact Hv_not_src |].
             split; [| exact Heq].
             eapply selected_parent_add_to_mst_old_vvalid; eauto.
          -- subst e.
             exists minIndex.
             split; [exact HminIndex_graph |].
             split.
             ++ intro Hsrc_eq.
                subst minIndex.
                destruct Hcand_minIndex as [_ [Hnot_valid _]].
                contradiction.
             ++ split.
                ** eapply selected_parent_add_to_mst_minIndex_vvalid; eauto.
                ** reflexivity.
        * intros [v [Hv_graph [Hv_not_src [Hv_next Heq]]]].
          apply Hadd_evalid.
          rewrite (selected_parent_add_to_mst_vvalid
            g_low_level_spec s_2 s_next
            l_from_new_2 l_to_new_2 l_edge_parent_2 minIndex v Hadd)
            in Hv_next.
          destruct Hv_next as [Hv_old | Hv_new].
          -- left.
             apply Hparent_exact_old.
             exists v.
             split; [exact Hv_graph |].
             split; [exact Hv_not_src |].
             split; [exact Hv_old | exact Heq].
          -- subst v.
             right.
             exact Heq.
  }
  assert (Hstate_after :
    selected_state_after_add g_low_level_spec src_low_level_spec i n_pre
      s_2 s_next l_from_new_2 l_to_new_2 l_edge_parent_2
      l_lowcost_2 l_visited_2 minIndex).
  {
    right. split; [lia |].
    split; [exact PreH19 |].
    split; [exact PreH20 |].
    split; [exact PreH23 |].
    split; [exact PreH27 |].
    exists x_u, x_v.
    split; [exact Hpair |].
    split; [exact Hadd |].
    exact Hvisited_next.
  }
  assert (Hscan : scan_minIndex_adjacency_prefix_update
    g_low_level_spec s_next l_from_new_2 l_first l_link_2
    l_to_new_2 l_weight_new_2 minIndex (Znth minIndex l_first 0)
    l_lowcost_2 l_edge_parent_2 l_lowcost_2 l_edge_parent_2).
  { eapply scan_minIndex_adjacency_prefix_start; eauto. }
  Exists l_lowcost_2 l_edge_parent_2 s_next s_next x_u x_v
    l_lowcost_2 l_edge_parent_2 l_visited_2 s_2
    l_first l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2.
  entailer!.
Qed. 

Lemma proof_of_prim_entail_wit_18_1_boot : prim_entail_wit_18_1_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (array_graph_edge_count
    n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
    g_low_level_spec PreH19) as Hcount.
  assert (Hde_range_m : 0 <= current_e < 2 * m_pre) by lia.
  assert (Hde_range_g : 0 <= current_e < 2 * graph_edge_count g_low_level_spec) by lia.
  pose proof (scan_minIndex_adjacency_prefix_current_in
    g_low_level_spec s_after_2 l_from_new_2 l_first_2 l_link
    l_to_new_2 l_weight_new_2 minIndex current_e
    l_lowcost_2 l_edge_parent_2 l_lowcost_cur l_edge_parent_cur
    PreH7 PreH42) as Hcurrent_in.
  assert (Hfrom_eq : Znth current_e l_from_new_2 0 = minIndex).
  {
    rewrite vertex_directed_edges_In in Hcurrent_in.
    exact (proj2 Hcurrent_in).
  }
  assert (Hedge_valid : edge_valid g_low_level_spec (current_e / 2)).
  { eapply array_graph_directed_edge_valid; eauto. }
  pose proof (selected_state_after_add_minIndex_vvalid
    g_low_level_spec src_low_level_spec i n_pre s_2 s_after_2
    l_from_new_2 l_to_new_2 l_edge_parent_2 l_lowcost_2
    l_visited_2 minIndex PreH38) as Hmin_valid_after.
  assert (Hv_graph : In (Znth current_e l_to_new_2 0) (graph_vertices g_low_level_spec)).
  {
    eapply array_graph_vertex_in; [exact PreH19 |].
    split; [exact PreH4 | exact PreH3].
  }
  pose proof (selected_state_after_add_visited
    g_low_level_spec src_low_level_spec i n_pre s_2 s_after_2
    l_from_new_2 l_to_new_2 l_edge_parent_2 l_lowcost_2
    l_visited_2 minIndex PreH38) as Hvisited_after.
  pose proof
    (fun Hto_valid =>
       let Hvalid_to_visited :=
         proj2 (Hvisited_after (Znth current_e l_to_new_2 0) Hv_graph) in
       let Hvisited_nonzero := Hvalid_to_visited Hto_valid in
       Hvisited_nonzero PreH2)
    as Hto_not_valid.
  assert (Hcut :
    is_cut_edge_to_vertex g_low_level_spec s_after_2
      (Znth current_e l_to_new_2 0) (current_e / 2)).
  {
    eapply directed_edge_is_cut_edge_to_vertex.
    - exact PreH21.
    - eapply array_graph_gvalid; eauto.
    - exact Hde_range_g.
    - exact Hedge_valid.
    - exact
        (eq_rect minIndex
           (fun v => graph_basic.vvalid s_after_2.(Prim.graph_in_state) v)
           Hmin_valid_after
           (Znth current_e l_from_new_2 0)
           (eq_sym Hfrom_eq)).
    - exact Hto_not_valid.
  }
  assert (Hone :
    scan_one_directed_edge_update
      g_low_level_spec s_after_2 l_to_new_2 l_weight_new_2
      l_lowcost_cur l_edge_parent_cur current_e
      (replace_Znth (Znth current_e l_to_new_2 0)
        (Znth current_e l_weight_new_2 0) l_lowcost_cur)
      (replace_Znth (Znth current_e l_to_new_2 0)
        current_e l_edge_parent_cur)).
  {
    unfold scan_one_directed_edge_update.
    left.
    refine (conj Hcut _).
    refine (conj PreH1 _).
    split; reflexivity.
  }
  assert (Hscan_next :
    scan_minIndex_adjacency_prefix_update
      g_low_level_spec s_after_2 l_from_new_2 l_first_2 l_link
      l_to_new_2 l_weight_new_2 minIndex
      (Znth current_e l_link 0)
      l_lowcost_2 l_edge_parent_2
      (replace_Znth (Znth current_e l_to_new_2 0)
        (Znth current_e l_weight_new_2 0) l_lowcost_cur)
      (replace_Znth (Znth current_e l_to_new_2 0)
        current_e l_edge_parent_cur)).
  {
    eapply scan_minIndex_adjacency_prefix_step; eauto.
  }
  assert (Hparent_updated :
    parent_edges_match_state
      g_low_level_spec src_low_level_spec s_after_2
      (replace_Znth (Znth current_e l_to_new_2 0)
         current_e l_edge_parent_cur)).
  {
    unfold parent_edges_match_state in *.
    destruct PreH41 as [Hsrc_after [Hparent_range_old Hparent_exact_old]].
    split; [exact Hsrc_after|].
    split.
    - intros v Hv_in Hv_not_src Hv_valid.
      destruct (Z.eq_dec v (Znth current_e l_to_new_2 0)) as [Hv_eq | Hv_neq].
      + subst v.
        contradiction.
      + rewrite Znth_replace_Znth_diff_nonneg_local.
        * eapply Hparent_range_old; eauto.
        * exact PreH4.
        * eapply array_graph_vertex_range; eauto.
        * congruence.
    - intros e.
      split.
      + intro He.
        apply Hparent_exact_old in He.
        destruct He as [v [Hv_graph_parent [Hv_not_src [Hv_valid Heq]]]].
        exists v.
        split; [exact Hv_graph_parent|].
        split; [exact Hv_not_src|].
        split; [exact Hv_valid|].
        destruct (Z.eq_dec v (Znth current_e l_to_new_2 0)) as [Hv_eq | Hv_neq].
        * subst v; contradiction.
        * rewrite Znth_replace_Znth_diff_nonneg_local.
          -- exact Heq.
          -- exact PreH4.
          -- eapply array_graph_vertex_range; eauto.
          -- congruence.
      + intros [v [Hv_graph_parent [Hv_not_src [Hv_valid Heq]]]].
        apply Hparent_exact_old.
        exists v.
        split; [exact Hv_graph_parent|].
        split; [exact Hv_not_src|].
        split; [exact Hv_valid|].
        destruct (Z.eq_dec v (Znth current_e l_to_new_2 0)) as [Hv_eq | Hv_neq].
        * subst v; contradiction.
        * rewrite Znth_replace_Znth_diff_nonneg_local in Heq.
          -- exact Heq.
          -- exact PreH4.
          -- eapply array_graph_vertex_range; eauto.
          -- congruence.
  }
  Exists (replace_Znth (Znth current_e l_to_new_2 0)
           (Znth current_e l_weight_new_2 0) l_lowcost_cur)
         (replace_Znth (Znth current_e l_to_new_2 0)
           current_e l_edge_parent_cur)
         s_next_2 x_u_2 x_v_2
         l_lowcost_2 l_edge_parent_2 l_visited_2
         s_2 s_after_2 l_first_2 l_from_new_2 l_to_new_2
         l_weight_new_2 current_e l_link.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; exact Hparent_updated);
    try (dump_pre_spatial; lia).
  all: try solve [
      entailer!
    | sep_apply store_int_undef_store_int;
      sep_apply store_int_undef_store_int;
      cancel
    | cancel
    ].
Qed. 

Lemma proof_of_prim_entail_wit_18_2_boot : prim_entail_wit_18_2_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (array_graph_edge_count
    n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
    g_low_level_spec PreH19) as Hcount.
  assert (Hde_range_m : 0 <= current_e < 2 * m_pre) by lia.
  assert (Hde_range_g : 0 <= current_e < 2 * graph_edge_count g_low_level_spec) by lia.
  pose proof (scan_minIndex_adjacency_prefix_current_in
    g_low_level_spec s_after_2 l_from_new_2 l_first_2 l_link
    l_to_new_2 l_weight_new_2 minIndex current_e
    l_lowcost_2 l_edge_parent_2 l_lowcost_cur l_edge_parent_cur
    PreH7 PreH33) as Hcurrent_in.
  assert (Hfrom_eq : Znth current_e l_from_new_2 0 = minIndex).
  {
    rewrite vertex_directed_edges_In in Hcurrent_in.
    exact (proj2 Hcurrent_in).
  }
  assert (Hedge_valid : edge_valid g_low_level_spec (current_e / 2)).
  { eapply array_graph_directed_edge_valid; eauto. }
  pose proof (selected_state_after_add_minIndex_vvalid
    g_low_level_spec src_low_level_spec i n_pre s_2 s_after_2
    l_from_new_2 l_to_new_2 l_edge_parent_2 l_lowcost_2
    l_visited_2 minIndex PreH29) as Hmin_valid_after.
  assert (Hv_graph : In (Znth current_e l_to_new_2 0) (graph_vertices g_low_level_spec)).
  {
    eapply array_graph_vertex_in; [exact PreH19 |].
    split; [exact PreH4 | exact PreH3].
  }
  pose proof (selected_state_after_add_visited
    g_low_level_spec src_low_level_spec i n_pre s_2 s_after_2
    l_from_new_2 l_to_new_2 l_edge_parent_2 l_lowcost_2
    l_visited_2 minIndex PreH29) as Hvisited_after.
  pose proof
    (fun Hto_valid =>
       let Hvalid_to_visited :=
         proj2 (Hvisited_after (Znth current_e l_to_new_2 0) Hv_graph) in
       let Hvisited_nonzero := Hvalid_to_visited Hto_valid in
       Hvisited_nonzero PreH2)
    as Hto_not_valid.
  assert (Hcut :
    is_cut_edge_to_vertex g_low_level_spec s_after_2
      (Znth current_e l_to_new_2 0) (current_e / 2)).
  {
    eapply directed_edge_is_cut_edge_to_vertex.
    - exact PreH21.
    - eapply array_graph_gvalid; eauto.
    - exact Hde_range_g.
    - exact Hedge_valid.
    - exact
        (eq_rect minIndex
           (fun v => graph_basic.vvalid s_after_2.(Prim.graph_in_state) v)
           Hmin_valid_after
           (Znth current_e l_from_new_2 0)
           (eq_sym Hfrom_eq)).
    - exact Hto_not_valid.
  }
  assert (Hone :
    scan_one_directed_edge_update
      g_low_level_spec s_after_2 l_to_new_2 l_weight_new_2
      l_lowcost_cur l_edge_parent_cur current_e
      (replace_Znth (Znth current_e l_to_new_2 0)
        (Znth current_e l_weight_new_2 0) l_lowcost_cur)
      (replace_Znth (Znth current_e l_to_new_2 0)
        current_e l_edge_parent_cur)).
  {
    unfold scan_one_directed_edge_update.
    left.
    refine (conj Hcut _).
    refine (conj PreH1 _).
    split; reflexivity.
  }
  assert (Hscan_next :
    scan_minIndex_adjacency_prefix_update
      g_low_level_spec s_after_2 l_from_new_2 l_first_2 l_link
      l_to_new_2 l_weight_new_2 minIndex
      (Znth current_e l_link 0)
      l_lowcost_2 l_edge_parent_2
      (replace_Znth (Znth current_e l_to_new_2 0)
        (Znth current_e l_weight_new_2 0) l_lowcost_cur)
      (replace_Znth (Znth current_e l_to_new_2 0)
        current_e l_edge_parent_cur)).
  {
    eapply scan_minIndex_adjacency_prefix_step; eauto.
  }
  assert (Hparent_updated :
    parent_edges_match_state
      g_low_level_spec src_low_level_spec s_after_2
      (replace_Znth (Znth current_e l_to_new_2 0)
         current_e l_edge_parent_cur)).
  {
    unfold parent_edges_match_state in *.
    destruct PreH32 as [Hsrc_after [Hparent_range_old Hparent_exact_old]].
    split; [exact Hsrc_after|].
    split.
    - intros v Hv_in Hv_not_src Hv_valid.
      destruct (Z.eq_dec v (Znth current_e l_to_new_2 0)) as [Hv_eq | Hv_neq].
      + subst v.
        contradiction.
      + rewrite Znth_replace_Znth_diff_nonneg_local.
        * eapply Hparent_range_old; eauto.
        * exact PreH4.
        * eapply array_graph_vertex_range; eauto.
        * congruence.
    - intros e.
      split.
      + intro He.
        apply Hparent_exact_old in He.
        destruct He as [v [Hv_graph_parent [Hv_not_src [Hv_valid Heq]]]].
        exists v.
        split; [exact Hv_graph_parent|].
        split; [exact Hv_not_src|].
        split; [exact Hv_valid|].
        destruct (Z.eq_dec v (Znth current_e l_to_new_2 0)) as [Hv_eq | Hv_neq].
        * subst v; contradiction.
        * rewrite Znth_replace_Znth_diff_nonneg_local.
          -- exact Heq.
          -- exact PreH4.
          -- eapply array_graph_vertex_range; eauto.
          -- congruence.
      + intros [v [Hv_graph_parent [Hv_not_src [Hv_valid Heq]]]].
        apply Hparent_exact_old.
        exists v.
        split; [exact Hv_graph_parent|].
        split; [exact Hv_not_src|].
        split; [exact Hv_valid|].
        destruct (Z.eq_dec v (Znth current_e l_to_new_2 0)) as [Hv_eq | Hv_neq].
        * subst v; contradiction.
        * rewrite Znth_replace_Znth_diff_nonneg_local in Heq.
          -- exact Heq.
          -- exact PreH4.
          -- eapply array_graph_vertex_range; eauto.
          -- congruence.
  }
  Exists (replace_Znth (Znth current_e l_to_new_2 0)
           (Znth current_e l_weight_new_2 0) l_lowcost_cur)
         (replace_Znth (Znth current_e l_to_new_2 0)
           current_e l_edge_parent_cur)
         s_2 l_edge_parent_2 l_visited_2 l_lowcost_2
         s_after_2 l_first_2 l_from_new_2 l_to_new_2
         l_weight_new_2 current_e l_link.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; exact Hparent_updated);
    try (dump_pre_spatial; lia).
  all: try solve [
      entailer!
    | sep_apply store_int_undef_store_int;
      sep_apply store_int_undef_store_int;
      cancel
    | cancel
    ].
Qed. 

Lemma proof_of_prim_entail_wit_18_3_boot : prim_entail_wit_18_3_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hv_graph : In (Znth current_e l_to_new_2 0) (graph_vertices g_low_level_spec)).
  {
    eapply array_graph_vertex_in; [exact PreH18 |].
    split; [exact PreH3 | exact PreH2].
  }
  pose proof (selected_state_after_add_visited
    g_low_level_spec src_low_level_spec i n_pre s_2 s_after_2
    l_from_new_2 l_to_new_2 l_edge_parent_2 l_lowcost_2
    l_visited_2 minIndex PreH28) as Hvisited_after.
  assert (Hnot_cut :
    ~ is_cut_edge_to_vertex g_low_level_spec s_after_2
        (Znth current_e l_to_new_2 0) (current_e / 2)).
  {
    eapply visited_nonzero_not_cut_edge_to_vertex.
    - exact Hvisited_after.
    - exact Hv_graph.
    - exact PreH1.
  }
  assert (Hone :
    scan_one_directed_edge_update
      g_low_level_spec s_after_2 l_to_new_2 l_weight_new_2
      l_lowcost_cur l_edge_parent_cur current_e
      l_lowcost_cur l_edge_parent_cur).
  {
    right.
    split.
    - left; exact Hnot_cut.
    - split; reflexivity.
  }
  assert (Hscan_next :
    scan_minIndex_adjacency_prefix_update
      g_low_level_spec s_after_2 l_from_new_2 l_first_2 l_link
      l_to_new_2 l_weight_new_2 minIndex
      (Znth current_e l_link 0)
      l_lowcost_2 l_edge_parent_2
      l_lowcost_cur l_edge_parent_cur).
  {
    eapply scan_minIndex_adjacency_prefix_step; eauto.
  }
  Exists l_lowcost_cur l_edge_parent_cur
         s_2 l_edge_parent_2 l_visited_2 l_lowcost_2
         s_after_2 l_first_2 l_from_new_2 l_to_new_2
         l_weight_new_2 current_e l_link.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia).
  all: try solve [
      entailer!
    | sep_apply store_int_undef_store_int;
      sep_apply store_int_undef_store_int;
      cancel
    | cancel
    ].
Qed. 

Lemma proof_of_prim_entail_wit_18_4_boot : prim_entail_wit_18_4_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (selected_state_after_add_visited
    g_low_level_spec src_low_level_spec i n_pre s_2 s_after_2
    l_from_new_2 l_to_new_2 l_edge_parent_2 l_lowcost_2
    l_visited_2 minIndex PreH37) as Hvisited_after.
  assert (Hv_graph : In (Znth current_e l_to_new_2 0) (graph_vertices g_low_level_spec)).
  {
    eapply array_graph_vertex_in; [exact PreH18 |].
    split; [exact PreH3 | exact PreH2].
  }
  assert (Hnot_cut :
    ~ is_cut_edge_to_vertex g_low_level_spec s_after_2
        (Znth current_e l_to_new_2 0) (current_e / 2)).
  {
    eapply visited_nonzero_not_cut_edge_to_vertex.
    - exact Hvisited_after.
    - exact Hv_graph.
    - exact PreH1.
  }
  assert (Hone :
    scan_one_directed_edge_update
      g_low_level_spec s_after_2 l_to_new_2 l_weight_new_2
      l_lowcost_cur l_edge_parent_cur current_e
      l_lowcost_cur l_edge_parent_cur).
  {
    right.
    split.
    - left; exact Hnot_cut.
    - split; reflexivity.
  }
  assert (Hscan_next :
    scan_minIndex_adjacency_prefix_update
      g_low_level_spec s_after_2 l_from_new_2 l_first_2 l_link
      l_to_new_2 l_weight_new_2 minIndex
      (Znth current_e l_link 0)
      l_lowcost_2 l_edge_parent_2
      l_lowcost_cur l_edge_parent_cur).
  {
    eapply scan_minIndex_adjacency_prefix_step; eauto.
  }
  Exists l_lowcost_cur l_edge_parent_cur
         s_next_2 x_u_2 x_v_2
         l_lowcost_2 l_edge_parent_2 l_visited_2
         s_2 s_after_2 l_first_2 l_from_new_2 l_to_new_2
         l_weight_new_2 current_e l_link.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia).
  all: try solve [
      entailer!
    | sep_apply store_int_undef_store_int;
      sep_apply store_int_undef_store_int;
      cancel
    | cancel
    ].
Qed. 

Lemma proof_of_prim_entail_wit_18_5_boot : prim_entail_wit_18_5_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hfalse : False).
  {
    assert (Hde : 0 <= current_e < 2 * m_pre) by lia.
    pose proof (directed_array_graph_to_range
      n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
      g_low_level_spec l_from_new_2 l_to_new_2 l_weight_new_2 current_e
      PreH16 PreH18 PreH13 PreH14 Hde) as Hto_range.
    destruct Hto_range as [Hto_ge _].
    apply (Z.lt_irrefl 0).
    eapply Z.le_lt_trans; [exact Hto_ge | apply Z.gt_lt; exact PreH1].
  }
  Exists l_lowcost_cur l_edge_parent_cur s_2
         l_edge_parent_2 l_visited_2 l_lowcost_2 s_after_2
         l_first_2 l_from_new_2 l_to_new_2 l_weight_new_2 current_e l_link.
  repeat (split_pure_spatial || split_pures);
    try contradiction;
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try cancel.
Qed. 

Lemma proof_of_prim_entail_wit_18_6_boot : prim_entail_wit_18_6_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  
  assert (Hfalse : False).
  {
    assert (Hde : 0 <= current_e < 2 * m_pre) by lia.
    pose proof (directed_array_graph_to_range
      n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
      g_low_level_spec l_from_new_2 l_to_new_2 l_weight_new_2 current_e
      PreH16 PreH18 PreH13 PreH14 Hde) as Hto_range.
    destruct Hto_range as [Hto_ge _].
    apply (Z.lt_irrefl 0).
    eapply Z.le_lt_trans; [exact Hto_ge | apply Z.gt_lt; exact PreH1].
  }
  Exists l_lowcost_cur l_edge_parent_cur s_next_2 x_u_2 x_v_2
         l_lowcost_2 l_edge_parent_2 l_visited_2 s_2 s_after_2
         l_first_2 l_from_new_2 l_to_new_2 l_weight_new_2 current_e l_link.
  repeat (split_pure_spatial || split_pures);
    try contradiction;
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try cancel.
Qed. 

Lemma proof_of_prim_entail_wit_18_7_boot : prim_entail_wit_18_7_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  
  assert (Hfalse : False).
  {
    assert (Hde : 0 <= current_e < 2 * m_pre) by lia.
    pose proof (directed_array_graph_to_range
      n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
      g_low_level_spec l_from_new_2 l_to_new_2 l_weight_new_2 current_e
      PreH17 PreH19 PreH14 PreH15 Hde) as Hto_range.
    destruct Hto_range as [_ Hto_lt].
    apply (Z.lt_irrefl n_pre).
    eapply Z.le_lt_trans; [apply Z.ge_le; exact PreH1 | exact Hto_lt].
  }
  Exists l_lowcost_cur l_edge_parent_cur s_next_2 x_u_2 x_v_2
         l_lowcost_2 l_edge_parent_2 l_visited_2 s_2 s_after_2
         l_first_2 l_from_new_2 l_to_new_2 l_weight_new_2 current_e l_link.
  repeat (split_pure_spatial || split_pures);
    try contradiction;
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try cancel.
Qed. 

Lemma proof_of_prim_entail_wit_18_8_boot : prim_entail_wit_18_8_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  
  assert (Hfalse : False).
  {
    assert (Hde : 0 <= current_e < 2 * m_pre) by lia.
    pose proof (directed_array_graph_to_range
      n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
      g_low_level_spec l_from_new_2 l_to_new_2 l_weight_new_2 current_e
      PreH17 PreH19 PreH14 PreH15 Hde) as Hto_range.
    destruct Hto_range as [_ Hto_lt].
    apply (Z.lt_irrefl n_pre).
    eapply Z.le_lt_trans; [apply Z.ge_le; exact PreH1 | exact Hto_lt].
  }
  Exists l_lowcost_cur l_edge_parent_cur s_2
         l_edge_parent_2 l_visited_2 l_lowcost_2 s_after_2
         l_first_2 l_from_new_2 l_to_new_2 l_weight_new_2 current_e l_link.
  repeat (split_pure_spatial || split_pures);
    try contradiction;
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try cancel.
Qed. 

Lemma proof_of_prim_entail_wit_18_9_boot : prim_entail_wit_18_9_boot.
Proof.
  right.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hone :
    scan_one_directed_edge_update
      g_low_level_spec s_after_2 l_to_new_2 l_weight_new_2
      l_lowcost_cur l_edge_parent_cur current_e
      l_lowcost_cur l_edge_parent_cur).
  {
    right.
    split.
    - right. apply Z.ge_le. exact PreH1.
    - split; reflexivity.
  }
  assert (Hscan_next :
    scan_minIndex_adjacency_prefix_update
      g_low_level_spec s_after_2 l_from_new_2 l_first_2 l_link
      l_to_new_2 l_weight_new_2 minIndex
      (Znth current_e l_link 0)
      l_lowcost_2 l_edge_parent_2
      l_lowcost_cur l_edge_parent_cur).
  {
    eapply scan_minIndex_adjacency_prefix_step; eauto.
  }
  Exists s_next_2 x_u_2 x_v_2 l_lowcost_2 l_edge_parent_2 l_visited_2
         s_2 s_after_2 current_e.
  entailer!.
  all: try rewrite PreH27;
       try rewrite <- PreH12;
       try exact Hscan_next;
       try assumption; try reflexivity; try lia.
Qed. 

Lemma proof_of_prim_entail_wit_18_10_boot : prim_entail_wit_18_10_boot.
Proof.
  right.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst src_low_level_spec i min minIndex l_lowcost_2 l_visited_2 l_edge_parent_2.
  assert (Hone :
    scan_one_directed_edge_update
      g_low_level_spec s_after_2 l_to_new_2 l_weight_new_2
      l_lowcost_cur l_edge_parent_cur current_e
      l_lowcost_cur l_edge_parent_cur).
  {
    right.
    split.
    - right. apply Z.ge_le. exact PreH1.
    - split; reflexivity.
  }
  assert (Hscan_next :
    scan_minIndex_adjacency_prefix_update
      g_low_level_spec s_after_2 l_from_new_2 l_first_2 l_link
      l_to_new_2 l_weight_new_2 0
      (Znth current_e l_link 0)
      (replace_Znth 0 0 (repeat_Z 1000000000 n_pre)) (repeat_Z (-1) n_pre)
      l_lowcost_cur l_edge_parent_cur).
  {
    eapply scan_minIndex_adjacency_prefix_step; eauto.
  }
  Exists s_2 s_after_2 current_e.
  entailer!.
  all: try exact Hscan_next;
       try assumption; try reflexivity; try lia.
Qed. 

Lemma proof_of_prim_entail_wit_19_1_boot : prim_entail_wit_19_1_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_lowcost_next l_edge_parent_next
         s_2 s_after_2 l_edge_parent_2 l_visited_2 l_lowcost_2
         l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2.
  entailer!.
Qed. 

Lemma proof_of_prim_entail_wit_19_2_boot : prim_entail_wit_19_2_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_lowcost_next l_edge_parent_next
         s_after_2 s_next_2 x_u_2 x_v_2
         l_lowcost_2 l_edge_parent_2 l_visited_2 s_2
         l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2.
  entailer!.
Qed. 

Lemma proof_of_prim_entail_wit_19_3_boot : prim_entail_wit_19_3_boot.
Proof.
  LLM_pre_process ltac:(auto).
  pose proof (scan_minIndex_adjacency_prefix_current_in
    g_low_level_spec s_after_2 l_from_new_2 l_first_2 l_link_2
    l_to_new_2 l_weight_new_2 minIndex current_e
    l_lowcost_2 l_edge_parent_2 l_lowcost_cur_2 l_edge_parent_cur_2
    PreH2 PreH28) as Hcurrent_in.
  pose proof (vertex_directed_edges_range
    g_low_level_spec l_from_new_2 minIndex current_e Hcurrent_in)
    as [Hcur_ge _].
  assert (Hfalse : False) by lia.
  destruct Hfalse.
Qed. 

Lemma proof_of_prim_entail_wit_19_4_boot : prim_entail_wit_19_4_boot.
Proof.
  LLM_pre_process ltac:(auto).
  pose proof (scan_minIndex_adjacency_prefix_current_in
    g_low_level_spec s_after_2 l_from_new_2 l_first_2 l_link_2
    l_to_new_2 l_weight_new_2 minIndex current_e
    l_lowcost_2 l_edge_parent_2 l_lowcost_cur_2 l_edge_parent_cur_2
    PreH2 PreH37) as Hcurrent_in.
  pose proof (vertex_directed_edges_range
    g_low_level_spec l_from_new_2 minIndex current_e Hcurrent_in)
    as [Hcur_ge _].
  assert (Hfalse : False) by lia.
  destruct Hfalse.
Qed. 

Lemma proof_of_prim_entail_wit_19_5_boot : prim_entail_wit_19_5_boot.
Proof.
  LLM_pre_process ltac:(auto).
  pose proof (array_graph_edge_count
    n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
    g_low_level_spec PreH15) as Hcount.
  pose proof (scan_minIndex_adjacency_prefix_current_in
    g_low_level_spec s_after_2 l_from_new_2 l_first_2 l_link_2
    l_to_new_2 l_weight_new_2 minIndex current_e
    l_lowcost_2 l_edge_parent_2 l_lowcost_cur_2 l_edge_parent_cur_2
    PreH3 PreH38) as Hcurrent_in.
  pose proof (vertex_directed_edges_range
    g_low_level_spec l_from_new_2 minIndex current_e Hcurrent_in)
    as [_ Hcur_lt].
  assert (Hfalse : False) by lia.
  destruct Hfalse.
Qed. 

Lemma proof_of_prim_entail_wit_19_6_boot : prim_entail_wit_19_6_boot.
Proof.
  LLM_pre_process ltac:(auto).
  pose proof (array_graph_edge_count
    n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
    g_low_level_spec PreH15) as Hcount.
  pose proof (scan_minIndex_adjacency_prefix_current_in
    g_low_level_spec s_after_2 l_from_new_2 l_first_2 l_link_2
    l_to_new_2 l_weight_new_2 minIndex current_e
    l_lowcost_2 l_edge_parent_2 l_lowcost_cur_2 l_edge_parent_cur_2
    PreH3 PreH29) as Hcurrent_in.
  pose proof (vertex_directed_edges_range
    g_low_level_spec l_from_new_2 minIndex current_e Hcurrent_in)
    as [_ Hcur_lt].
  assert (Hfalse : False) by lia.
  destruct Hfalse.
Qed. 

Lemma proof_of_prim_entail_wit_20_1_boot : prim_entail_wit_20_1_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hscan_done :
    scan_minIndex_adjacency_update
      g_low_level_spec s_after_2 l_from_new_2 l_first_2 l_link_2
      l_to_new_2 l_weight_new_2 minIndex
      l_lowcost_2 l_edge_parent_2 l_lowcost_cur l_edge_parent_cur).
  {
    eapply scan_minIndex_adjacency_prefix_finish.
    rewrite <- PreH1.
    exact PreH36.
  }
  assert (Hgrowing_after : growing_subgraph_state g_low_level_spec s_after_2).
  {
    eapply selected_state_after_add_growing with
      (n := n_pre) (m := m_pre)
      (from := lf_low_level_spec) (to := lt_low_level_spec)
      (wt := lw_low_level_spec)
      (src := src_low_level_spec) (i := i)
      (s_before := s_2)
      (from_new := l_from_new_2) (to_new := l_to_new_2)
      (edge_parent := l_edge_parent_2)
      (lowcost := l_lowcost_2) (visited := l_visited_2)
      (minIndex := minIndex); eauto.
    eapply array_graph_vertex_in; eauto; lia.
  }
  assert (Hvisited_after :
    visited_matches_state g_low_level_spec s_after_2
      (replace_Znth minIndex 1 l_visited_2)).
  { eapply selected_state_after_add_visited; eauto. }
  assert (Hlowcost_after :
    lowcost_parent_match
      g_low_level_spec s_after_2 l_lowcost_cur l_edge_parent_cur
      1000000000).
		  {
		    eapply scan_minIndex_adjacency_update_lowcost_parent_match; try eassumption.
		    - intros e He. apply PreH12; exact He.
		    - eapply array_graph_vertex_in; eauto; lia.
		  }
  Exists l_lowcost_cur l_edge_parent_cur s_next_2 x_u_2 x_v_2
         l_lowcost_2 l_edge_parent_2 l_visited_2 s_2 s_after_2
         l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2.
  entailer!.
Qed. 

Lemma proof_of_prim_entail_wit_20_2_boot : prim_entail_wit_20_2_boot.
Proof.
  LLM_pre_process ltac:(int_auto).
  
  assert (Hscan_done :
    scan_minIndex_adjacency_update
      g_low_level_spec s_after_2 l_from_new_2 l_first_2 l_link_2
      l_to_new_2 l_weight_new_2 minIndex
      l_lowcost_2 l_edge_parent_2 l_lowcost_cur l_edge_parent_cur).
  {
    eapply scan_minIndex_adjacency_prefix_finish.
    rewrite <- PreH1.
    exact PreH27.
  }
  assert (Hgrowing_after : growing_subgraph_state g_low_level_spec s_after_2).
  {
    eapply selected_state_after_add_growing with
      (n := n_pre) (m := m_pre)
      (from := lf_low_level_spec) (to := lt_low_level_spec)
      (wt := lw_low_level_spec)
      (src := src_low_level_spec) (i := i)
      (s_before := s_2)
      (from_new := l_from_new_2) (to_new := l_to_new_2)
      (edge_parent := l_edge_parent_2)
      (lowcost := l_lowcost_2) (visited := l_visited_2)
      (minIndex := minIndex); eauto.
    eapply array_graph_vertex_in; eauto; lia.
  }
  assert (Hvisited_after :
    visited_matches_state g_low_level_spec s_after_2
      (replace_Znth minIndex 1 l_visited_2)).
  { eapply selected_state_after_add_visited; eauto. }
  assert (Hlowcost_after :
    lowcost_parent_match
      g_low_level_spec s_after_2 l_lowcost_cur l_edge_parent_cur
      1000000000).
		  {
		    eapply scan_minIndex_adjacency_update_lowcost_parent_match; try eassumption.
		    - intros e He. apply PreH12; exact He.
		    - eapply array_graph_vertex_in; eauto; lia.
		  }
  Exists l_lowcost_cur l_edge_parent_cur s_2
         l_edge_parent_2 l_visited_2 l_lowcost_2 s_after_2
         l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2.
  entailer!.
Qed. 

Lemma proof_of_prim_entail_wit_21_1_running : prim_entail_wit_21_1_running.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_lowcost_3 l_edge_parent_3 l_visited_3 s_3
         l_first_3 l_link_3 l_from_new_3 l_to_new_3 l_weight_new_3.
  entailer!.
  apply min_vertex_in_range_empty.
Qed. 

Lemma proof_of_prim_entail_wit_21_2_running : prim_entail_wit_21_2_running.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_lowcost_3 l_edge_parent_3 l_visited_3 s_3
         l_first_3 l_link_3 l_from_new_3 l_to_new_3 l_weight_new_3.
  entailer!.
  apply min_vertex_in_range_empty.
Qed. 

Lemma proof_of_prim_entail_wit_22_1_running : prim_entail_wit_22_1_running.
Proof.
  LLM_pre_process ltac:(int_auto).
  
  assert (Hcandidate_next :
    (i + 1 < n_pre) ->
    candidate_vertex_exists_in_range
      n_pre g_low_level_spec s_after
      l_lowcost_next l_edge_parent_next 1000000000).
  {
    intros Hlt.
    eapply unfinished_connected_state_has_candidate_vertex_by_count with
      (m := m_pre) (from := lf_low_level_spec)
      (to := lt_low_level_spec) (wt := lw_low_level_spec).
    - exact PreH15.
    - exact (prim_connected g_low_level_spec src_low_level_spec PreH16).
    - exact PreH30.
    - exists minIndex.
      eapply selected_state_after_add_minIndex_vvalid; eauto.
    - rewrite PreH27.
      lia.
    - exact PreH33.
  }
  Exists l_lowcost_next l_edge_parent_next
         (replace_Znth minIndex 1 l_visited) s_after
         l_first l_link l_from_new l_to_new l_weight_new.
  replace ((i + 1) - 1) with i by lia.
  entailer!.
Qed. 

Lemma proof_of_prim_entail_wit_22_2_running : prim_entail_wit_22_2_running.
Proof.
  LLM_pre_process ltac:(int_auto).
  
  assert (Hcandidate_next :
    (i_2 + 1 < n_pre) ->
    candidate_vertex_exists_in_range
      n_pre g_low_level_spec s_after
      l_lowcost_next l_edge_parent_next 1000000000).
  {
    intros Hlt.
    eapply unfinished_connected_state_has_candidate_vertex_by_count with
      (m := m_pre) (from := lf_low_level_spec)
      (to := lt_low_level_spec) (wt := lw_low_level_spec).
    - exact PreH15.
    - exact (prim_connected g_low_level_spec src_low_level_spec PreH16).
    - exact PreH39.
    - exists minIndex_2.
      eapply selected_state_after_add_minIndex_vvalid; eauto.
    - rewrite PreH36.
      lia.
    - exact PreH42.
  }
  Exists l_lowcost_next l_edge_parent_next
         (replace_Znth minIndex_2 1 l_visited) s_after
         l_first l_link l_from_new l_to_new l_weight_new.
  replace ((i_2 + 1) - 1) with i_2 by lia.
  entailer!.
Qed. 

Lemma proof_of_prim_entail_wit_23_1_running : prim_entail_wit_23_1_running.
Proof.
  LLM_pre_process ltac:(int_auto).
  
  assert (Hsafe_ret :
    safeExec (prim_state_is s_3) (return tt) X_low_level_spec).
  {
    eapply Prim2_loop_finish with
      (n := n_pre) (m := m_pre)
      (from := lf_low_level_spec) (to := lt_low_level_spec)
      (wt := lw_low_level_spec) (i := i_2); eauto.
    exact (prim_graph_valid g_low_level_spec src_low_level_spec PreH13).
  }
  assert (Hstate_full : state_vertex_count s_3 = n_pre).
  { rewrite PreH18; lia. }
  assert (Hparent_all :
    forall v,
      1 <= v < n_pre ->
      0 <= Znth v l_edge_parent_3 0 < 2 * m_pre).
  {
    intros v Hv.
    eapply (parent_edges_match_state_all_range
      n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
      g_low_level_spec src_low_level_spec s_3 l_edge_parent_3 v); eauto; lia.
  }
  assert (Hparent_one :
    1 < n_pre ->
      0 <= Znth 1 l_edge_parent_3 0 < 2 * m_pre).
  { intro Hlt; apply Hparent_all; lia. }
  assert (Hprefix :
    prim_result_graph_matches_array_prefix
      n_pre 0 nil nil nil g_low_level_spec s_3.(Prim.graph_in_state)
      l_edge_parent_3 l_from_new_3 l_to_new_3 l_weight_new_3).
  {
    unfold prim_result_graph_matches_array_prefix.
    split; [lia|].
    split; [rewrite Zlength_nil; lia|].
    split; [rewrite Zlength_nil; lia|].
    split; [rewrite Zlength_nil; lia|].
    intros k0 Hk0.
    simpl in Hk0.
    contradiction.
  }
  Exists nil nil nil s_3.(Prim.graph_in_state)
         l_lowcost_3 l_edge_parent_3 l_visited_3 s_3
         l_first_3 l_link_3 l_from_new_3 l_to_new_3 l_weight_new_3.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.undef_full_to_undef_seg out_u (n_pre - 1)).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg out_v (n_pre - 1)).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg out_wt (n_pre - 1)).
    rewrite (IntArray.seg_empty out_u 0 0).
    rewrite (IntArray.seg_empty out_v 0 0).
    rewrite (IntArray.seg_empty out_wt 0 0).
    cancel (IntArray.full from_arr_pre m_pre lf_low_level_spec).
    cancel (IntArray.full to_arr_pre m_pre lt_low_level_spec).
    cancel (IntArray.full weight_arr_pre m_pre lw_low_level_spec).
    cancel (IntArray.undef_seg out_u 0 (n_pre - 1)).
    cancel (IntArray.undef_seg out_v 0 (n_pre - 1)).
    cancel (IntArray.undef_seg out_wt 0 (n_pre - 1)).
    cancel (IntArray.full from_new (2 * m_pre) l_from_new_3).
    cancel (IntArray.full to_new (2 * m_pre) l_to_new_3).
    cancel (IntArray.full weight_new (2 * m_pre) l_weight_new_3).
    cancel (IntArray.full first n_pre l_first_3).
    cancel (IntArray.full link (2 * m_pre) l_link_3).
    cancel (IntArray.full lowcost n_pre l_lowcost_3).
    cancel (IntArray.full visited n_pre l_visited_3).
    cancel (IntArray.full edge_parent n_pre l_edge_parent_3).
    entailer!.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; exact Hstate_full);
      try (dump_pre_spatial; exact Hparent_all);
      try (dump_pre_spatial; exact Hparent_one);
      try (dump_pre_spatial; exact Hsafe_ret);
      try (dump_pre_spatial; exact Hprefix);
      try (dump_pre_spatial; unfold prim_state_graph_matches; reflexivity);
      try (dump_pre_spatial; lia).
Qed. 

Lemma proof_of_prim_entail_wit_23_2_running : prim_entail_wit_23_2_running.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hsafe_ret :
    safeExec (prim_state_is s_3) (return tt) X_low_level_spec).
  {
    eapply Prim2_loop_finish with
      (n := n_pre) (m := m_pre)
      (from := lf_low_level_spec) (to := lt_low_level_spec)
      (wt := lw_low_level_spec) (i := i_2); eauto.
    exact (prim_graph_valid g_low_level_spec src_low_level_spec PreH13).
  }
  assert (Hstate_full : state_vertex_count s_3 = n_pre).
  { rewrite PreH18; lia. }
  assert (Hparent_all :
    forall v,
      1 <= v < n_pre ->
      0 <= Znth v l_edge_parent_3 0 < 2 * m_pre).
  {
    intros v Hv.
    eapply (parent_edges_match_state_all_range
      n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
      g_low_level_spec src_low_level_spec s_3 l_edge_parent_3 v); eauto; lia.
  }
  assert (Hparent_one :
    1 < n_pre ->
      0 <= Znth 1 l_edge_parent_3 0 < 2 * m_pre).
  { intro Hlt; apply Hparent_all; lia. }
  assert (Hprefix :
    prim_result_graph_matches_array_prefix
      n_pre 0 nil nil nil g_low_level_spec s_3.(Prim.graph_in_state)
      l_edge_parent_3 l_from_new_3 l_to_new_3 l_weight_new_3).
  {
    unfold prim_result_graph_matches_array_prefix.
    split; [lia|].
    split; [rewrite Zlength_nil; lia|].
    split; [rewrite Zlength_nil; lia|].
    split; [rewrite Zlength_nil; lia|].
    intros k0 Hk0.
    simpl in Hk0.
    contradiction.
  }
  Exists nil nil nil s_3.(Prim.graph_in_state)
         l_lowcost_3 l_edge_parent_3 l_visited_3 s_3
         l_first_3 l_link_3 l_from_new_3 l_to_new_3 l_weight_new_3.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.undef_full_to_undef_seg out_u (n_pre - 1)).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg out_v (n_pre - 1)).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg out_wt (n_pre - 1)).
    rewrite (IntArray.seg_empty out_u 0 0).
    rewrite (IntArray.seg_empty out_v 0 0).
    rewrite (IntArray.seg_empty out_wt 0 0).
    cancel (IntArray.full from_arr_pre m_pre lf_low_level_spec).
    cancel (IntArray.full to_arr_pre m_pre lt_low_level_spec).
    cancel (IntArray.full weight_arr_pre m_pre lw_low_level_spec).
    cancel (IntArray.undef_seg out_u 0 (n_pre - 1)).
    cancel (IntArray.undef_seg out_v 0 (n_pre - 1)).
    cancel (IntArray.undef_seg out_wt 0 (n_pre - 1)).
    cancel (IntArray.full from_new (2 * m_pre) l_from_new_3).
    cancel (IntArray.full to_new (2 * m_pre) l_to_new_3).
    cancel (IntArray.full weight_new (2 * m_pre) l_weight_new_3).
    cancel (IntArray.full first n_pre l_first_3).
    cancel (IntArray.full link (2 * m_pre) l_link_3).
    cancel (IntArray.full lowcost n_pre l_lowcost_3).
    cancel (IntArray.full visited n_pre l_visited_3).
    cancel (IntArray.full edge_parent n_pre l_edge_parent_3).
    entailer!.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; exact Hstate_full);
      try (dump_pre_spatial; exact Hparent_all);
      try (dump_pre_spatial; exact Hparent_one);
      try (dump_pre_spatial; exact Hsafe_ret);
      try (dump_pre_spatial; exact Hprefix);
      try (dump_pre_spatial; unfold prim_state_graph_matches; reflexivity);
      try (dump_pre_spatial; lia).
Qed. 

Lemma proof_of_prim_entail_wit_24_running : prim_entail_wit_24_running.
Proof.
  LLM_pre_process ltac:(int_auto).
  set (de := Znth i l_edge_parent_2 0).
  set (new_u := Znth de l_from_new_2 0).
  set (new_v := Znth de l_to_new_2 0).
  set (new_w := Znth de l_weight_new_2 0).
  Exists (l_out_u_2 ++ (new_u :: nil))
         (l_out_v_2 ++ (new_v :: nil))
         (l_out_wt_2 ++ (new_w :: nil))
         rg_2
         l_lowcost_2 l_edge_parent_2 l_visited_2 s_2
         l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2.
  split_pure_spatial.
  - cancel (IntArray.full from_arr_pre m_pre lf_low_level_spec).
    cancel (IntArray.full to_arr_pre m_pre lt_low_level_spec).
    cancel (IntArray.full weight_arr_pre m_pre lw_low_level_spec).
    replace (mst_idx + 1) with i by lia.
    cancel (IntArray.seg out_u 0 i (l_out_u_2 ++ (new_u :: nil))).
    cancel (IntArray.undef_seg out_u i (n_pre - 1)).
    cancel (IntArray.seg out_v 0 i (l_out_v_2 ++ (new_v :: nil))).
    cancel (IntArray.undef_seg out_v i (n_pre - 1)).
    cancel (IntArray.seg out_wt 0 i (l_out_wt_2 ++ (new_w :: nil))).
    cancel (IntArray.undef_seg out_wt i (n_pre - 1)).
    cancel (IntArray.full from_new (2 * m_pre) l_from_new_2).
    cancel (IntArray.full to_new (2 * m_pre) l_to_new_2).
    cancel (IntArray.full weight_new (2 * m_pre) l_weight_new_2).
    cancel (IntArray.full first n_pre l_first_2).
    cancel (IntArray.full link (2 * m_pre) l_link_2).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full visited n_pre l_visited_2).
    cancel (IntArray.full edge_parent n_pre l_edge_parent_2).
  - assert (Hprefix_next :
      prim_result_graph_matches_array_prefix
        n_pre (mst_idx + 1)
        (l_out_u_2 ++ (new_u :: nil))
        (l_out_v_2 ++ (new_v :: nil))
        (l_out_wt_2 ++ (new_w :: nil))
        g_low_level_spec rg_2
        l_edge_parent_2 l_from_new_2 l_to_new_2 l_weight_new_2).
    {
      unfold prim_result_graph_matches_array_prefix in *.
      destruct PreH28 as [Hidx_range [Hlen_u [Hlen_v [Hlen_w Hslots]]]].
      split; [lia|].
      split.
      { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
      split.
      { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
      split.
      { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
      intros k0 Hk.
        assert (Hk_cases : In k0 (Zrange 0 mst_idx) \/ k0 = mst_idx).
        {
          rewrite <- In_Zrange in Hk.
          destruct (Z_lt_ge_dec k0 mst_idx).
          - left. apply In_Zrange. lia.
          - right. lia.
        }
        destruct Hk_cases as [Hk_old | Hk_new].
        + specialize (Hslots k0 Hk_old).
          destruct Hslots as [Hevalid [Hstep [Hweight [Hfrom [Hto Hwt]]]]].
          split; [exact Hevalid|].
          split.
          * rewrite Znth_app_l_local by (rewrite Hlen_u; rewrite <- In_Zrange in Hk_old; lia).
            rewrite Znth_app_l_local by (rewrite Hlen_v; rewrite <- In_Zrange in Hk_old; lia).
            exact Hstep.
          * split.
            -- rewrite Znth_app_l_local by (rewrite Hlen_w; rewrite <- In_Zrange in Hk_old; lia).
               exact Hweight.
            -- split.
               ++ rewrite Znth_app_l_local by (rewrite Hlen_u; rewrite <- In_Zrange in Hk_old; lia).
                  exact Hfrom.
               ++ split.
                  ** rewrite Znth_app_l_local by (rewrite Hlen_v; rewrite <- In_Zrange in Hk_old; lia).
                     exact Hto.
                  ** rewrite Znth_app_l_local by (rewrite Hlen_w; rewrite <- In_Zrange in Hk_old; lia).
                     exact Hwt.
        + subst k0.
          assert (Hi_eq : i = mst_idx + 1) by lia.
          subst de new_u new_v new_w.
          rewrite Hi_eq in *.
          set (de1 := Znth (mst_idx + 1) l_edge_parent_2 0).
          assert (Hde_range : 0 <= de1 < 2 * graph_edge_count g_low_level_spec).
          {
            pose proof (array_graph_edge_count _ _ _ _ _ _ PreH18) as Hecount.
            rewrite Hecount.
            subst de1.
            split; [exact PreH3 | exact PreH2].
          }
          assert (He_rg : graph_basic.evalid rg_2 (de1 / 2)).
          {
            unfold prim_state_graph_matches in PreH27.
            subst rg_2.
            destruct PreH25 as [_ [_ Hparent_exact]].
            apply Hparent_exact.
            exists (mst_idx + 1).
            split.
            - eapply array_graph_vertex_in; eauto; lia.
            - split.
              + lia.
              + split.
                * eapply completed_growing_subgraph_vvalid; eauto.
                  eapply array_graph_vertex_in; eauto; lia.
                * reflexivity.
          }
          assert (Hstep_g :
            graph_basic.step_aux g_low_level_spec (de1 / 2)
              (Znth de1 l_from_new_2 0) (Znth de1 l_to_new_2 0)).
          {
            eapply (directed_array_graph_step
              g_low_level_spec l_from_new_2 l_to_new_2 l_weight_new_2 de1).
            - exact PreH20.
            - apply (prim_graph_valid _ _ PreH19).
            - exact Hde_range.
            - eapply array_graph_directed_edge_valid.
              + exact PreH18.
              + subst de1.
                split; [exact PreH3 | exact PreH2].
          }
          assert (Hstep_rg :
            graph_basic.step_aux rg_2 (de1 / 2)
              (Znth de1 l_from_new_2 0) (Znth de1 l_to_new_2 0)).
          {
            unfold prim_state_graph_matches in PreH27.
            subst rg_2.
            destruct PreH25 as [_ [_ Hparent_exact]].
            apply Hparent_exact in He_rg.
            destruct He_rg as [v [Hv_in [Hv_not_src [Hv_valid Heq]]]].
            rewrite Heq.
            destruct PreH22 as [Hgvalid_s [_ Hsub_sg]].
            specialize (Hgvalid_s (Znth v l_edge_parent_2 0 / 2)).
            assert (He_s : graph_basic.evalid s_2.(Prim.graph_in_state)
                            (Znth v l_edge_parent_2 0 / 2)).
            {
              apply Hparent_exact.
              exists v; repeat split; auto.
            }
            specialize (Hgvalid_s He_s).
            destruct Hgvalid_s as [u0 [v0 Hstep_any]].
            destruct Hsub_sg as [_ Hsub_step].
            pose proof (Hsub_step u0 v0 (Znth v l_edge_parent_2 0 / 2)
              Hstep_any) as Hstep_g_any.
            rewrite Heq in Hstep_g.
            pose proof (graph_basic.step_aux_unique_undirected
              g_low_level_spec (Znth v l_edge_parent_2 0 / 2)
              u0 v0 (Znth de1 l_from_new_2 0) (Znth de1 l_to_new_2 0)
              (prim_graph_valid _ _ PreH19) Hstep_g_any Hstep_g) as Hunq.
            destruct Hunq as [[Hu Hv] | [Hu Hv]]; subst.
            - exact Hstep_any.
            - apply graph_basic.step_sym. exact Hstep_any.
          }
          split; [exact He_rg|].
          split.
          { rewrite Znth_app_r_local.
            - rewrite Hlen_u.
              replace (mst_idx - mst_idx) with 0 by lia.
              rewrite Znth_app_r_local.
              + rewrite Hlen_v.
                replace (mst_idx - mst_idx) with 0 by lia.
                unfold Znth; simpl.
                exact Hstep_rg.
              + lia.
            - lia. }
          split.
          * rewrite Znth_app_r_local.
            -- rewrite Hlen_w.
               replace (mst_idx - mst_idx) with 0 by lia.
               unfold Znth; simpl.
               eapply directed_array_graph_weight.
               ++ exact PreH20.
               ++ exact Hde_range.
            -- lia.
          * split.
            -- rewrite Znth_app_r_local.
               ++ rewrite Hlen_u.
                  replace (mst_idx - mst_idx) with 0 by lia.
                  unfold Znth; simpl. reflexivity.
               ++ lia.
            -- split.
               ++ rewrite Znth_app_r_local.
                  ** rewrite Hlen_v.
                     replace (mst_idx - mst_idx) with 0 by lia.
                     unfold Znth; simpl. reflexivity.
                  ** lia.
               ++ rewrite Znth_app_r_local.
                  ** rewrite Hlen_w.
                     replace (mst_idx - mst_idx) with 0 by lia.
                     unfold Znth; simpl. reflexivity.
                  ** lia.
    }
    unfold new_u, new_v, new_w, de in Hprefix_next.
    split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; exact Hprefix_next);
      try (dump_pre_spatial; lia);
      try (dump_pre_spatial; reflexivity);
      try solve [entailer! | cancel];
      try solve [
        apply derivable1s_coq_prop_r;
        intro Hnext;
        apply PreH29;
        lia
      ].
Qed. 

Lemma proof_of_prim_return_wit_1_running : prim_return_wit_1_running.
Proof.
  unfold prim_return_wit_1_running. right; intros.
  assert (Hidx_full : mst_idx = n_pre - 1) by lia.
  assert (Hsafe_ret : safeExec (prim_state_graph_matches rg_2)
    (return tt) X_low_level_spec).
  {
    eapply safeExec_conseq; [exact PreH28 |].
    intros st Hst. unfold prim_state_is in Hst. subst st. exact PreH24.
  }
  assert (Hresult : prim_result_graph_matches_array
    n_pre l_out_u l_out_v l_out_wt g_low_level_spec rg_2).
  {
    rewrite Hidx_full in PreH25.
    eapply prim_result_graph_matches_array_of_full_prefix; eauto.
  }
  Exists edge_parent l_edge_parent visited l_visited lowcost l_lowcost
    link l_link first l_first weight_new l_weight_new
    to_new l_to_new from_new l_from_new rg_2.
  entailer!.
Qed. 

Lemma proof_of_prim_derive_high_level_spec_by_low_level_spec : prim_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Exists lf_high_level_spec lt_high_level_spec lw_high_level_spec
         g_high_level_spec src_high_level_spec X_high_level_spec.
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia).
  cancel (IntArray.full from_arr_pre m_pre lf_high_level_spec).
  cancel (IntArray.full to_arr_pre m_pre lt_high_level_spec).
  cancel (IntArray.full weight_arr_pre m_pre lw_high_level_spec).
  apply derivable1_wand_sepcon_adjoint.
  Intros redge ledge.
  Intros rvis lvis.
  Intros rlow llow.
  Intros rlink llink.
  Intros rfirst lfirst.
  Intros rweight lweight.
  Intros rto lto.
  Intros rfrom lfrom.
  Intros retwt retv.
  Intros retu lru.
  Intros lrv lrwt.
  Intros rg ret.
  Exists redge ledge
         rvis lvis
         rlow llow
         rlink llink
         rfirst lfirst
         rweight lweight
         rto lto
         rfrom lfrom
         retwt retv.
  Exists retu lru lrv lrwt rg ret.
  split_pure_spatial.
  - entailer!.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; lia).
Qed. 

