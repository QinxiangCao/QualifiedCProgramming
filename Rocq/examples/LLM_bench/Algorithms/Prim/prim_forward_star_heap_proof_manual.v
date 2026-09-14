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
From SimpleC.SL Require Import IntLib.
From SimpleC.EE.LLM_bench.Algorithms.Prim Require Import prim_forward_star_heap_goal.
From SimpleC.EE.LLM_bench.Algorithms.Prim Require Import prim_forward_star_heap_proof_auto.
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
Require Import GraphLib.graph_basic.
Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue_decrease_key.priority_queue_decrease_key_lib.
Require Import SimpleC.EE.LLM_bench.Algorithms.Prim.prim_forward_star_heap_lib.
From ListLib.Base Require Import Positional.
Local Open Scope sac.

Lemma proof_of_prim_forward_star_heap_entail_wit_1 : prim_forward_star_heap_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  Exists (@nil Z) (@nil Z) (@nil Z).
  assert (Hcount : 0 <= graph_edge_count g_low_level_spec).
  {
    rewrite (array_graph_edge_count n_pre m_pre lf_low_level_spec
               lt_low_level_spec lw_low_level_spec g_low_level_spec PreH11).
    lia.
  }
  assert (Hprefix : directed_array_graph_prefix 0 g_low_level_spec nil nil nil).
  { apply directed_array_graph_prefix_0_nil; exact Hcount. }
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval_4 (2 * m_pre)).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval_5 (2 * m_pre)).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval_6 (2 * m_pre)).
  split_pure_spatial.
  - simpl.
    repeat rewrite IntArray.seg_empty.
    repeat cancel.
    LLM_pre_process ltac:(lia).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_2 : prim_forward_star_heap_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  Exists ((l_from_new_prefix_2 ++ (Znth i lf_low_level_spec 0 :: nil)) ++
            (Znth i lt_low_level_spec 0 :: nil))
         ((l_to_new_prefix_2 ++ (Znth i lt_low_level_spec 0 :: nil)) ++
            (Znth i lf_low_level_spec 0 :: nil))
         ((l_weight_new_prefix_2 ++ (Znth i lw_low_level_spec 0 :: nil)) ++
            (Znth i lw_low_level_spec 0 :: nil)).
  assert (Hnext :
    directed_array_graph_prefix (i + 1) g_low_level_spec
      ((l_from_new_prefix_2 ++ (Znth i lf_low_level_spec 0 :: nil)) ++
        (Znth i lt_low_level_spec 0 :: nil))
      ((l_to_new_prefix_2 ++ (Znth i lt_low_level_spec 0 :: nil)) ++
        (Znth i lf_low_level_spec 0 :: nil))
      ((l_weight_new_prefix_2 ++ (Znth i lw_low_level_spec 0 :: nil)) ++
        (Znth i lw_low_level_spec 0 :: nil))).
  {
    eapply directed_array_graph_prefix_snoc; eauto.
  }
  split_pure_spatial.
  - replace (2 * (i + 1)) with (2 * i + 1 + 1) by lia.
    repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_3 : prim_forward_star_heap_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  assert (Hi : i = m_pre) by lia.
  subst i.
  assert (Hcount : graph_edge_count g_low_level_spec = m_pre).
  {
    eapply array_graph_edge_count; eauto.
  }
  assert (Hdir : directed_array_graph g_low_level_spec
                   l_from_new_prefix l_to_new_prefix l_weight_new_prefix).
  {
    eapply directed_array_graph_prefix_finish; eauto; lia.
  }
  assert (Hfrom_len : Zlength l_from_new_prefix = 2 * m_pre).
  {
    unfold directed_array_graph_prefix in PreH16.
    tauto.
  }
  assert (Hto_len : Zlength l_to_new_prefix = 2 * m_pre).
  {
    unfold directed_array_graph_prefix in PreH16.
    tauto.
  }
  assert (Hwt_len : Zlength l_weight_new_prefix = 2 * m_pre).
  {
    unfold directed_array_graph_prefix in PreH16.
    tauto.
  }
  Exists l_from_new_prefix l_to_new_prefix l_weight_new_prefix.
  sep_apply_l_atomic
    (IntArray.seg_to_full from_new 0 (2 * m_pre) l_from_new_prefix).
  sep_apply_l_atomic
    (IntArray.seg_to_full to_new 0 (2 * m_pre) l_to_new_prefix).
  sep_apply_l_atomic
    (IntArray.seg_to_full weight_new 0 (2 * m_pre) l_weight_new_prefix).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval n_pre).
  replace (from_new + 0 * sizeof (INT)) with from_new by lia.
  replace (to_new + 0 * sizeof (INT)) with to_new by lia.
  replace (weight_new + 0 * sizeof (INT)) with weight_new by lia.
  replace (2 * m_pre - 0) with (2 * m_pre) by lia.
  split_pure_spatial.
  - change (repeat_Z (-1) 0) with (@nil Z).
    rewrite Hfrom_len, Hto_len, Hwt_len.
    repeat rewrite IntArray.seg_empty.
    repeat cancel.
    LLM_pre_process ltac:(lia).
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_4_split_goal_1 :
  prim_forward_star_heap_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  symmetry.
  apply repeat_Z_tail.
  lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_4 :
  prim_forward_star_heap_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prim_forward_star_heap_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_5 : prim_forward_star_heap_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists l_from_new_2 l_to_new_2 l_weight_new_2.
  assert (Hi_eq : i = n_pre) by lia.
  assert (Hfrom_len : Zlength l_from_new_2 = 2 * m_pre).
  {
    unfold directed_array_graph, directed_array_graph_prefix in PreH16.
    destruct PreH16 as [_ [Hlen _]].
    rewrite (array_graph_edge_count
               n_pre m_pre lf_low_level_spec lt_low_level_spec
               lw_low_level_spec g_low_level_spec PreH14) in Hlen.
    exact Hlen.
  }
  assert (Hto_len : Zlength l_to_new_2 = 2 * m_pre).
  {
    unfold directed_array_graph, directed_array_graph_prefix in PreH16.
    destruct PreH16 as [_ [_ [Hlen _]]].
    rewrite (array_graph_edge_count
               n_pre m_pre lf_low_level_spec lt_low_level_spec
               lw_low_level_spec g_low_level_spec PreH14) in Hlen.
    exact Hlen.
  }
  assert (Hwt_len : Zlength l_weight_new_2 = 2 * m_pre).
  {
    unfold directed_array_graph, directed_array_graph_prefix in PreH16.
    destruct PreH16 as [_ [_ [_ [Hlen _]]]].
    rewrite (array_graph_edge_count
               n_pre m_pre lf_low_level_spec lt_low_level_spec
               lw_low_level_spec g_low_level_spec PreH14) in Hlen.
    exact Hlen.
  }
  subst i.
  sep_apply_l_atomic
    (IntArray.seg_to_full first 0 n_pre (repeat_Z (-1) n_pre)).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg link (2 * m_pre)).
  replace (first + 0 * sizeof(INT)) with first by lia.
  replace (n_pre - 0) with n_pre by lia.
  rewrite Hfrom_len, Hto_len, Hwt_len.
  rewrite (IntArray.undef_seg_empty first n_pre).
  rewrite (IntArray.seg_empty link 0 0).
  asrt_simpl_pure.
  sepcon_assoc_change.
  andp_cancel.
  all: first [assumption | lia | nia | int_auto].
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_6_split_goal_1 :
  prim_forward_star_heap_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  symmetry.
  apply repeat_Z_tail.
  lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_6 :
  prim_forward_star_heap_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prim_forward_star_heap_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_7_split_goal_1 :
  prim_forward_star_heap_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace i with (2 * m_pre) by lia.
  apply first_link_matches_inserted_vertex_directed_edges_empty.
  - unfold repeat_Z.
    rewrite Zlength_correct, repeat_length.
    rewrite Z2Nat.id by lia.
    unfold array_graph in PreH14.
    destruct PreH14 as [Hvertices _].
    rewrite Hvertices.
    rewrite Zlength_Zrange by lia.
    lia.
  - unfold repeat_Z.
    rewrite Zlength_correct, repeat_length.
    rewrite Z2Nat.id by lia.
    rewrite (array_graph_edge_count
               n_pre m_pre lf_low_level_spec lt_low_level_spec
               lw_low_level_spec g_low_level_spec PreH14).
    reflexivity.
  - intros v Hv.
    unfold array_graph in PreH14.
    destruct PreH14 as [Hvertices _].
    rewrite Hvertices in Hv.
    rewrite <- SumLib.ZRange.In_Zrange in Hv.
    unfold repeat_Z.
    rewrite Znth_repeat_lt by lia.
    reflexivity.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_7_split_goal_2 :
  prim_forward_star_heap_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH13.
  exact H.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_7_split_goal_3 :
  prim_forward_star_heap_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH12.
  exact H.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_7_split_goal_4 :
  prim_forward_star_heap_entail_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH11.
  exact H.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_7 :
  prim_forward_star_heap_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_7_split_goal_3.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_7_split_goal_4.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_8 : prim_forward_star_heap_entail_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists l_first_2 l_link_2 l_to_new_2 l_weight_new_2 l_from_new.
  assert (Hfrom_len : Zlength l_from_new = 2 * m_pre).
  {
    unfold directed_array_graph, directed_array_graph_prefix in PreH16.
    destruct PreH16 as [_ [Hlen _]].
    rewrite (array_graph_edge_count
               n_pre m_pre lf_low_level_spec lt_low_level_spec
               lw_low_level_spec g_low_level_spec PreH14) in Hlen.
    exact Hlen.
  }
  assert (Hto_len : Zlength l_to_new_2 = 2 * m_pre).
  {
    unfold directed_array_graph, directed_array_graph_prefix in PreH16.
    destruct PreH16 as [_ [_ [Hlen _]]].
    rewrite (array_graph_edge_count
               n_pre m_pre lf_low_level_spec lt_low_level_spec
               lw_low_level_spec g_low_level_spec PreH14) in Hlen.
    exact Hlen.
  }
  assert (Hwt_len : Zlength l_weight_new_2 = 2 * m_pre).
  {
    unfold directed_array_graph, directed_array_graph_prefix in PreH16.
    destruct PreH16 as [_ [_ [_ [Hlen _]]]].
    rewrite (array_graph_edge_count
               n_pre m_pre lf_low_level_spec lt_low_level_spec
               lw_low_level_spec g_low_level_spec PreH14) in Hlen.
    exact Hlen.
  }
  split_pure_spatial.
  - rewrite Hfrom_len, Hto_len, Hwt_len.
    cancel (IntArray.full from_new (2 * m_pre) l_from_new).
    cancel (IntArray.full from_arr_pre m_pre lf_low_level_spec).
    cancel (IntArray.full to_arr_pre m_pre lt_low_level_spec).
    cancel (IntArray.full weight_arr_pre m_pre lw_low_level_spec).
    cancel (IntArray.undef_full out_u (n_pre - 1)).
    cancel (IntArray.undef_full out_v (n_pre - 1)).
    cancel (IntArray.undef_full out_wt (n_pre - 1)).
    cancel (IntArray.full to_new (2 * m_pre) l_to_new_2).
    cancel (IntArray.full weight_new (2 * m_pre) l_weight_new_2).
    cancel (IntArray.full first n_pre l_first_2).
    cancel (IntArray.full link (2 * m_pre) l_link_2).
  - split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; lia).
    + dump_pre_spatial.
      assert (Hi_range : 0 <= i < 2 * m_pre) by lia.
      pose proof (directed_array_graph_from_range
                    n_pre m_pre lf_low_level_spec lt_low_level_spec
                    lw_low_level_spec g_low_level_spec
                    l_from_new l_to_new_2 l_weight_new_2 i
                    PreH14 PreH16 PreH11 PreH12 Hi_range) as Hrange.
      destruct Hrange as [Hlo Hlt]; first [exact Hlo | exact Hlt | lia].
    + dump_pre_spatial.
      assert (Hi_range : 0 <= i < 2 * m_pre) by lia.
      pose proof (directed_array_graph_from_range
                    n_pre m_pre lf_low_level_spec lt_low_level_spec
                    lw_low_level_spec g_low_level_spec
                    l_from_new l_to_new_2 l_weight_new_2 i
                    PreH14 PreH16 PreH11 PreH12 Hi_range) as Hrange.
      destruct Hrange as [Hlo Hlt]; first [exact Hlo | exact Hlt | lia].
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_9 : prim_forward_star_heap_entail_wit_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (replace_Znth u i l_first_2)
         (replace_Znth i (Znth u l_first_2 0) l_link_2)
         l_from_new_2 l_to_new_2 l_weight_new_2.
  assert (Hfrom_len : Zlength l_from_new_2 = 2 * m_pre).
  {
    unfold directed_array_graph, directed_array_graph_prefix in PreH18.
    destruct PreH18 as [_ [Hlen _]].
    rewrite (array_graph_edge_count
               n_pre m_pre lf_low_level_spec lt_low_level_spec
               lw_low_level_spec g_low_level_spec PreH16) in Hlen.
    exact Hlen.
  }
  assert (Hto_len : Zlength l_to_new_2 = 2 * m_pre).
  {
    unfold directed_array_graph, directed_array_graph_prefix in PreH18.
    destruct PreH18 as [_ [_ [Hlen _]]].
    rewrite (array_graph_edge_count
               n_pre m_pre lf_low_level_spec lt_low_level_spec
               lw_low_level_spec g_low_level_spec PreH16) in Hlen.
    exact Hlen.
  }
  assert (Hwt_len : Zlength l_weight_new_2 = 2 * m_pre).
  {
    unfold directed_array_graph, directed_array_graph_prefix in PreH18.
    destruct PreH18 as [_ [_ [_ [Hlen _]]]].
    rewrite (array_graph_edge_count
               n_pre m_pre lf_low_level_spec lt_low_level_spec
               lw_low_level_spec g_low_level_spec PreH16) in Hlen.
    exact Hlen.
  }
  split_pure_spatial.
  - rewrite Hfrom_len, Hto_len, Hwt_len.
    cancel (IntArray.full from_arr_pre m_pre lf_low_level_spec).
    cancel (IntArray.full to_arr_pre m_pre lt_low_level_spec).
    cancel (IntArray.full weight_arr_pre m_pre lw_low_level_spec).
    cancel (IntArray.undef_full out_u (n_pre - 1)).
    cancel (IntArray.undef_full out_v (n_pre - 1)).
    cancel (IntArray.undef_full out_wt (n_pre - 1)).
    cancel (IntArray.full from_new (2 * m_pre) l_from_new_2).
    cancel (IntArray.full to_new (2 * m_pre) l_to_new_2).
    cancel (IntArray.full weight_new (2 * m_pre) l_weight_new_2).
    cancel (IntArray.full first n_pre (replace_Znth u i l_first_2)).
    cancel (IntArray.full link (2 * m_pre)
              (replace_Znth i (Znth u l_first_2 0) l_link_2)).
  - split_pures.
    all: try (dump_pre_spatial; assumption).
    all: try (dump_pre_spatial; lia).
    dump_pre_spatial.
    apply (first_link_matches_inserted_vertex_directed_edges_insert
             g_low_level_spec i l_from_new_2 l_first_2 l_link_2 u);
      try assumption.
    + apply array_graph_vertex_in with
        (n := n_pre) (m := m_pre)
        (from := lf_low_level_spec) (to := lt_low_level_spec)
        (wt := lw_low_level_spec);
        assumption || lia.
    + intros v Hv.
      assert (Hv_range : 0 <= v < n_pre) by
        (eapply array_graph_vertex_range; eauto).
      unfold first_link_matches_inserted_vertex_directed_edges in PreH19.
      destruct PreH19 as [Hfirst_len _].
      rewrite Hfirst_len.
      rewrite (array_graph_vertex_count
                 n_pre m_pre lf_low_level_spec lt_low_level_spec
                 lw_low_level_spec g_low_level_spec PreH16).
      exact Hv_range.
    + unfold first_link_matches_inserted_vertex_directed_edges in PreH19.
      destruct PreH19 as [_ [Hlink_len _]].
      rewrite Hlink_len.
      rewrite (array_graph_edge_count
                 n_pre m_pre lf_low_level_spec lt_low_level_spec
                 lw_low_level_spec g_low_level_spec PreH16).
      lia.
    + symmetry.
      exact PreH10.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_10_split_goal_1 :
  prim_forward_star_heap_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(try (lia || nia || int_auto)).
  apply first_link_matches_inserted_vertex_directed_edges_finish.
  replace (2 * graph_edge_count g_low_level_spec) with i.
  - exact PreH17.
  - rewrite (array_graph_edge_count
               n_pre m_pre lf_low_level_spec lt_low_level_spec
               lw_low_level_spec g_low_level_spec PreH14).
    lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_10_split_goal_2 :
  prim_forward_star_heap_entail_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(try (lia || nia || int_auto)).
  apply PreH13.
  exact H.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_10_split_goal_3 :
  prim_forward_star_heap_entail_wit_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(try (lia || nia || int_auto)).
  apply PreH12.
  exact H.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_10_split_goal_4 :
  prim_forward_star_heap_entail_wit_10_split_goal_4.
Proof.
  LLM_pre_process ltac:(try (lia || nia || int_auto)).
  apply PreH11.
  exact H.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_10_split_goal_5 :
  prim_forward_star_heap_entail_wit_10_split_goal_5.
Proof.
  LLM_pre_process ltac:(try (lia || nia || int_auto)).
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_10_split_goal_6 :
  prim_forward_star_heap_entail_wit_10_split_goal_6.
Proof.
  LLM_pre_process ltac:(try (lia || nia || int_auto)).
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_10_split_goal_7 :
  prim_forward_star_heap_entail_wit_10_split_goal_7.
Proof.
  LLM_pre_process ltac:(try (lia || nia || int_auto)).
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_10 :
  prim_forward_star_heap_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_10_split_goal_1.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_10_split_goal_2.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_10_split_goal_3.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_10_split_goal_4.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_10_split_goal_5.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_10_split_goal_6.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_10_split_goal_7.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_11_split_goal_1 :
  prim_forward_star_heap_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  symmetry.
  apply repeat_Z_tail; lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_11_split_goal_2 :
  prim_forward_star_heap_entail_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  symmetry.
  apply repeat_Z_tail; lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_11_split_goal_3 :
  prim_forward_star_heap_entail_wit_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  symmetry.
  apply repeat_Z_tail; lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_11 :
  prim_forward_star_heap_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_11_split_goal_2.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_11_split_goal_3.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_12_split_goal_1 :
  prim_forward_star_heap_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH13; exact H.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_12_split_goal_2 :
  prim_forward_star_heap_entail_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH12; exact H.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_12_split_goal_3 :
  prim_forward_star_heap_entail_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH11; exact H.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_12_split_goal_4 :
  prim_forward_star_heap_entail_wit_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  f_equal; lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_12_split_goal_5 :
  prim_forward_star_heap_entail_wit_12_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  f_equal; lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_12_split_goal_6 :
  prim_forward_star_heap_entail_wit_12_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  f_equal; lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_12 :
  prim_forward_star_heap_entail_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_12_split_goal_1.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_12_split_goal_2.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_12_split_goal_3.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_12_split_goal_4.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_12_split_goal_5.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_12_split_goal_6.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_13_split_goal_1 :
  prim_forward_star_heap_entail_wit_13_split_goal_1.
Proof.
  unfold prim_forward_star_heap_entail_wit_13_split_goal_1.
  intros m_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
         lw_low_level_spec lt_low_level_spec lf_low_level_spec
         l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2
         Hn Hn_int Hm Hcap_int Htmp_int Hcap Hsrc Hlf Hlt Hlw
         Hgraph Henv Hdir Hfirst Hsafe.
  exact Hlw.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_13_split_goal_2 :
  prim_forward_star_heap_entail_wit_13_split_goal_2.
Proof.
  unfold prim_forward_star_heap_entail_wit_13_split_goal_2.
  intros m_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
         lw_low_level_spec lt_low_level_spec lf_low_level_spec
         l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2
         Hn Hn_int Hm Hcap_int Htmp_int Hcap Hsrc Hlf Hlt Hlw
         Hgraph Henv Hdir Hfirst Hsafe.
  exact Hlt.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_13_split_goal_3 :
  prim_forward_star_heap_entail_wit_13_split_goal_3.
Proof.
  unfold prim_forward_star_heap_entail_wit_13_split_goal_3.
  intros m_pre n_pre X_low_level_spec src_low_level_spec g_low_level_spec
         lw_low_level_spec lt_low_level_spec lf_low_level_spec
         l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2
         Hn Hn_int Hm Hcap_int Htmp_int Hcap Hsrc Hlf Hlt Hlw
         Hgraph Henv Hdir Hfirst Hsafe.
  exact Hlf.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_13_split_goal_4 :
  prim_forward_star_heap_entail_wit_13_split_goal_4.
Proof.
  unfold prim_forward_star_heap_entail_wit_13_split_goal_4.
  intros.
  change (repeat_Z (-1) 0) with (@nil Z).
  reflexivity.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_13 :
  prim_forward_star_heap_entail_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_13_split_goal_1.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_13_split_goal_2.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_13_split_goal_3.
  - Goal_apply proof_of_prim_forward_star_heap_entail_wit_13_split_goal_4.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_14_split_goal_1 :
  prim_forward_star_heap_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  symmetry.
  apply repeat_Z_tail.
  lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_14 :
  prim_forward_star_heap_entail_wit_14.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_prim_forward_star_heap_entail_wit_14_split_goal_1.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_15 :
  prim_forward_star_heap_entail_wit_15.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  assert (Hpos_i : pos_i = n_pre) by lia.
  subst pos_i.
  subst heap_size.
  Exists l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2
         (partial_map_add partial_map_empty src_low_level_spec 0)
         partial_map_empty.
  sep_apply_l_atomic
    (IntArray.seg_to_full heap_pos 0 n_pre (repeat_Z (-1) n_pre)).
  replace (heap_pos + 0 * sizeof(INT)) with heap_pos by lia.
  replace (n_pre - 0) with n_pre by lia.
  change (repeat_Z (-1) n_pre) with (repeat_Z absent n_pre).
  unfold store_heap.
  Exists (@nil Z) (@nil Z) (repeat_Z absent n_pre).
  rewrite !IntArray.full_empty.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    + apply partial_map_empty_absent.
    + unfold prim_queue_map_initial.
      split; [reflexivity |].
      rewrite PreH8.
      reflexivity.
    + apply heap_representation_empty; lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_16 :
  prim_forward_star_heap_entail_wit_16.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  Exists l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2
         (initSt g_low_level_spec src_low_level_spec)
         (partial_map_add queue_map_empty 0 0).
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    + unfold prim_queue_map_initial.
      rewrite PreH10, PreH7.
      split; reflexivity.
    + unfold prim_heap_loop_state.
      left.
      split; [reflexivity |].
      split; [reflexivity |].
      split.
      * rewrite PreH7.
        unfold repeat_Z.
        rewrite Zlength_replace_Znth_local
          by (rewrite Zlength_correct, repeat_length, Z2Nat.id by lia; lia).
        rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
        reflexivity.
      * split.
        -- unfold repeat_Z.
           rewrite Zlength_correct, repeat_length, Nat2Z.id.
           reflexivity.
        -- split.
           ++ unfold repeat_Z.
              rewrite Zlength_correct, repeat_length, Nat2Z.id.
              reflexivity.
           ++ split.
              ** rewrite PreH10, PreH7.
                 reflexivity.
              ** assumption.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_19 :
  prim_forward_star_heap_entail_wit_19.
Proof.
  right.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  subst key_out_callee_v data_out_callee_v.
  assert (Hsrc_graph : In src_low_level_spec (graph_vertices g_low_level_spec)).
  {
    rewrite PreH10.
    eapply array_graph_vertex_in; eauto; lia.
  }
  pose proof (prim_heap_loop_pop_after
    n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
    g_low_level_spec src_low_level_spec chosen s_2
    l_lowcost_2 l_visited_2 l_edge_parent_2 queue_map_2
    (item_key popped) (item_data popped) X_low_level_spec
    PreH19 PreH18 Hsrc_graph ltac:(lia) PreH23 PreH3)
    as [Hpop [Hafter [Hvertex_range Hkey_range]]].
  Exists l_first_2
         (partial_map_remove queue_map_2 (item_data popped))
         s_2 l_visited_2 queue_map_2.
  sep_apply_l_atomic
    (IntArray.full_split_to_missing_i
       first (item_data popped) n_pre l_first_2 0);
    [apply derivable1s_coq_prop_r; exact Hvertex_range |].
  sep_apply_l_atomic
    (IntArray.full_split_to_missing_i
       visited (item_data popped) n_pre l_visited_2 0);
    [apply derivable1s_coq_prop_r; exact Hvertex_range |].
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_20 :
  prim_forward_star_heap_entail_wit_20.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  prop_apply (IntArray.full_Zlength lowcost n_pre l_lowcost_2).
  Intros_p Hlow_len.
  prop_apply (IntArray.missing_i_Zlength visited minIndex 0 n_pre l_visited_2).
  Intros_p Hvisited_len0.
  assert (Hvisited_len : Zlength l_visited_2 = n_pre) by lia.
  prop_apply (IntArray.full_Zlength edge_parent n_pre l_edge_parent_2).
  Intros_p Hparent_len.
  prop_apply (IntArray.missing_i_Zlength first minIndex 0 n_pre l_first).
  Intros_p Hfirst_len0.
  assert (Hfirst_len : Zlength l_first = n_pre) by lia.
  assert (Hsrc_graph :
    In src_low_level_spec (graph_vertices g_low_level_spec)).
  {
    rewrite PreH7.
    eapply array_graph_vertex_in; eauto; lia.
  }
  destruct (prim_heap_after_pop_scan_start
    n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
    g_low_level_spec src_low_level_spec chosen s_2
    l_from_new_2 l_first l_link_2 l_to_new_2 l_weight_new_2
    l_lowcost_2 l_visited_2 l_edge_parent_2
    queue_map_before_2 queue_map minIndex min X_low_level_spec
    PreH23 PreH20 PreH21 PreH22 PreH25 PreH26 Hsrc_graph
    Hlow_len Hvisited_len Hparent_len ltac:(lia) ltac:(lia) PreH19)
    as [s_after Hscan].
  Exists s_2 s_after l_from_new_2 l_first l_link_2 l_to_new_2
         l_weight_new_2 l_lowcost_2 l_visited_2 l_edge_parent_2
         queue_map l_lowcost_2 l_edge_parent_2 queue_map minIndex.
  sep_apply_l_atomic
    (IntArray.missing_i_merge_to_full
       first minIndex n_pre (Znth minIndex l_first 0) l_first);
    [apply derivable1s_coq_prop_r; lia |].
  rewrite replace_Znth_Znth by lia.
  sep_apply_l_atomic
    (IntArray.missing_i_merge_to_full
       visited minIndex n_pre 1 l_visited_2);
    [apply derivable1s_coq_prop_r; lia |].
  split_pure_spatial.
  - sepcon_assoc_change.
    sep_apply (store_int_undef_store_int (&( "minIndex" )) minIndex).
    cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_21 :
  prim_forward_star_heap_entail_wit_21.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  assert (Hweight_range :
    -2147483648 <= Znth current_edge l_weight_new 0 <= 2147483647).
  {
    pose proof (directed_array_graph_weight_range
      n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
      g_low_level_spec l_from_new_2 l_to_new l_weight_new current_edge
      PreH26 PreH28 PreH25 ltac:(lia)) as Hrange.
    destruct Hrange as [Hlo Hhi].
    split.
    - eapply Z.le_trans; [| exact Hlo].
      lia.
    - apply Z.lt_le_incl in Hhi.
      eapply Z.le_trans; [exact Hhi |].
      lia.
  }
  assert (Hupdate_pre :
    partial_map_update_or_add_pre queue_map_cur_2
      (Znth current_edge l_to_new 0)
      (Znth current_edge l_weight_new 0)).
  {
    eapply prim_heap_scan_state_update_or_add_pre.
    - exact PreH22.
    - reflexivity.
    - reflexivity.
    - exact PreH1.
  }
  sep_apply_l_atomic
    (store_heap_size_le_data_bound heap_cost heap_vertex heap_pos
       n_pre heap_capacity queue_map_cur_2 heap_size).
  Intros_p Hheap_size_le_n.
  pose proof (connected_array_graph_vertex_count_le_twice_edges
    n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
    g_low_level_spec PreH26
    (prim_connected g_low_level_spec src_low_level_spec PreH27)
    PreH8) as Hn_le_edges.
  assert (Hheap_size_lt_capacity : heap_size < heap_capacity) by lia.
  Exists s_2 s_after_2 l_from_new_2 l_first_2 l_link_2
         l_lowcost_2 l_edge_parent_2 queue_map_before_2
         queue_map_cur_2 l_edge_parent_cur_2
         (replace_Znth (Znth current_edge l_to_new 0) current_edge
            l_edge_parent_cur_2)
         (replace_Znth (Znth current_edge l_to_new 0)
            (Znth current_edge l_weight_new 0) l_lowcost_cur_2)
         l_visited_2 l_lowcost_cur_2 l_weight_new l_to_new selected_2.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_22 :
  prim_forward_star_heap_entail_wit_22.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  assert (Hn_after_nonneg : 0 <= n_after).
  {
    unfold partial_map_update_or_add_size in PreH1.
    destruct PreH1 as [[_ Hsize] | [_ Hsize]]; lia.
  }
  assert (Hn_after_capacity : n_after <= heap_capacity).
  {
    unfold partial_map_update_or_add_size in PreH1.
    destruct PreH1 as [[_ Hsize] | [_ Hsize]]; lia.
  }
  prop_apply
    (IntArray.full_Zlength visited n_pre
       (replace_Znth selected_2 1 l_visited_2)).
  Intros_p Hvisited_after_len.
  rewrite Zlength_replace_Znth in Hvisited_after_len.
  assert (Hmin_graph :
    In selected_2 (graph_vertices g_low_level_spec)).
  { eapply array_graph_vertex_in; eauto; lia. }
  assert (Hmin_visited :
    Znth selected_2 (replace_Znth selected_2 1 l_visited_2) 0 <> 0).
  {
    rewrite Znth_replace_Znth_same_local by lia.
    lia.
  }
  assert (Hmin_valid :
    vvalid s_after_2.(Prim.graph_in_state) selected_2).
  {
    eapply prim_heap_scan_state_visited_valid.
    - exact PreH29.
    - exact Hmin_graph.
    - exact Hmin_visited.
  }
  assert (Hscan_map :
    scan_one_directed_edge_update
      g_low_level_spec s_after_2 l_to_new_2 l_weight_new_2
      l_lowcost_cur_2 l_edge_parent_cur current_edge
      (replace_Znth (Znth current_edge l_to_new_2 0)
         (Znth current_edge l_weight_new_2 0) l_lowcost_cur_2)
      (replace_Znth (Znth current_edge l_to_new_2 0)
         current_edge l_edge_parent_cur) /\
    partial_map_update_one_directed_edge
      g_low_level_spec s_after_2 l_to_new_2 l_weight_new_2
      l_lowcost_cur_2 current_edge queue_map_cur_2
      (partial_map_update_or_add queue_map_cur_2
         (Znth current_edge l_to_new_2 0)
         (Znth current_edge l_weight_new_2 0))).
  {
    eapply (prim_heap_scan_state_current_edge_update
      n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
      g_low_level_spec src_low_level_spec chosen s_2 s_after_2
      l_from_new_2 l_first_2 l_link_2 l_to_new_2 l_weight_new_2
      l_lowcost_2 (replace_Znth selected_2 1 l_visited_2) l_edge_parent_2
      l_lowcost_cur_2 l_edge_parent_cur current_edge selected_2 min
      queue_map_before_2 queue_map_cur_2 X_low_level_spec);
      try eassumption; try lia.
    - rewrite PreH23 in PreH24.
      rewrite PreH22 in PreH24.
      exact PreH24.
    - rewrite PreH22 in PreH25.
      exact PreH25.
  }
  destruct Hscan_map as [Hscan_one Hmap_one].
  assert (Hscan_next :
    prim_heap_scan_state
      g_low_level_spec src_low_level_spec chosen s_2 s_after_2
      l_from_new_2 l_first_2 l_link_2 l_to_new_2 l_weight_new_2
      l_lowcost_2 (replace_Znth selected_2 1 l_visited_2) l_edge_parent_2
      l_lowcost_next_2 l_edge_parent_next_2
      (Znth current_edge l_link_2 0) selected_2 min
      queue_map_before_2 l_lowcost_next_2 l_edge_parent_next_2
      (partial_map_update_or_add queue_map_cur_2 to_node edge_weight)
      X_low_level_spec).
  {
    rewrite PreH26, PreH27.
    rewrite PreH22, PreH23.
    eapply prim_heap_scan_state_step_update; eauto; try lia.
    intros e He.
    specialize (PreH32 e He).
    lia.
  }
  Exists s_2 s_after_2 l_from_new_2 l_first_2
         l_lowcost_2 l_edge_parent_2 queue_map_before_2
         l_lowcost_next_2 l_edge_parent_next_2 queue_map_cur_2
         (partial_map_update_or_add queue_map_cur_2 to_node edge_weight)
         l_weight_new_2 l_to_new_2 l_link_2
         (Znth current_edge l_link_2 0) l_visited_2 l_lowcost_cur_2
         selected_2.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_23_1 :
  prim_forward_star_heap_entail_wit_23_1.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  assert (Hscan_loop :
    prim_heap_scan_state
      g_low_level_spec src_low_level_spec chosen s_2 s_after_2
      l_from_new_2 l_first_2 l_link_2 l_to_new_2 l_weight_new_2
      l_lowcost_2 (replace_Znth selected_2 1 l_visited_2) l_edge_parent_2
      l_lowcost_next l_edge_parent_next (Znth cur_edge l_link_2 0)
      selected_2 min queue_map_before_2 l_lowcost_next l_edge_parent_next
      queue_map_next X_low_level_spec).
  { rewrite <- PreH23. exact PreH27. }
  Exists s_2 s_after_2 l_from_new_2 l_first_2 l_link_2
         l_to_new_2 l_weight_new_2 l_lowcost_2 l_visited_2
         l_edge_parent_2 queue_map_before_2 l_lowcost_next
         l_edge_parent_next queue_map_next selected_2.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_23_2 :
  prim_forward_star_heap_entail_wit_23_2.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  assert (Hnot_cut :
    ~ is_cut_edge_to_vertex g_low_level_spec s_after_2
        (Znth current_edge l_to_new_2 0) (current_edge / 2)).
  {
    eapply prim_heap_scan_state_current_edge_not_cut_when_visited; eauto.
  }
  assert (Hscan_loop :
    prim_heap_scan_state
      g_low_level_spec src_low_level_spec chosen s_2 s_after_2
      l_from_new_2 l_first_2 l_link_2 l_to_new_2 l_weight_new_2
      l_lowcost_2 (replace_Znth selected_2 1 l_visited_2) l_edge_parent_2
      l_lowcost_cur_2 l_edge_parent_cur_2 (Znth current_edge l_link_2 0)
      selected_2 min queue_map_before_2 l_lowcost_cur_2 l_edge_parent_cur_2
      queue_map_cur_2 X_low_level_spec).
  {
    eapply (prim_heap_scan_state_step_no_update
      n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
      g_low_level_spec src_low_level_spec chosen s_2 s_after_2
      l_from_new_2 l_first_2 l_link_2 l_to_new_2 l_weight_new_2
      l_lowcost_2 (replace_Znth selected_2 1 l_visited_2) l_edge_parent_2
      l_lowcost_cur_2 l_edge_parent_cur_2 current_edge selected_2 min
      queue_map_before_2 queue_map_cur_2 X_low_level_spec).
    - exact PreH25.
    - exact PreH22.
    - exact PreH23.
    - intros e He. specialize (PreH24 e He). lia.
    - exact PreH27.
    - exact PreH6.
    - exact PreH21.
    - left. exact Hnot_cut.
  }
  Exists s_2 s_after_2 l_from_new_2 l_first_2 l_link_2
         l_to_new_2 l_weight_new_2 l_lowcost_2 l_visited_2
         l_edge_parent_2 queue_map_before_2 l_lowcost_cur_2
         l_edge_parent_cur_2 queue_map_cur_2 selected_2.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_23_3 :
  prim_forward_star_heap_entail_wit_23_3.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  assert (Hto_range :
    0 <= Znth current_edge l_to_new_2 0 < n_pre).
  {
    eapply directed_array_graph_to_range; eauto; lia.
  }
  assert (Hfalse : False) by lia.
  contradiction.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_23_4 :
  prim_forward_star_heap_entail_wit_23_4.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  assert (Hto_range :
    0 <= Znth current_edge l_to_new_2 0 < n_pre).
  {
    eapply directed_array_graph_to_range; eauto; lia.
  }
  assert (Hfalse : False) by lia.
  contradiction.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_23_5 :
  prim_forward_star_heap_entail_wit_23_5.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  assert (Hscan_loop :
    prim_heap_scan_state
      g_low_level_spec src_low_level_spec chosen s_2 s_after_2
      l_from_new_2 l_first_2 l_link_2 l_to_new_2 l_weight_new_2
      l_lowcost_2 (replace_Znth selected_2 1 l_visited_2) l_edge_parent_2
      l_lowcost_cur_2 l_edge_parent_cur_2 (Znth current_edge l_link_2 0)
      selected_2 min queue_map_before_2 l_lowcost_cur_2 l_edge_parent_cur_2
      queue_map_cur_2 X_low_level_spec).
  {
    eapply (prim_heap_scan_state_step_no_update
      n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
      g_low_level_spec src_low_level_spec chosen s_2 s_after_2
      l_from_new_2 l_first_2 l_link_2 l_to_new_2 l_weight_new_2
      l_lowcost_2 (replace_Znth selected_2 1 l_visited_2) l_edge_parent_2
      l_lowcost_cur_2 l_edge_parent_cur_2 current_edge selected_2 min
      queue_map_before_2 queue_map_cur_2 X_low_level_spec).
    - exact PreH26.
    - exact PreH23.
    - exact PreH24.
    - intros e He. specialize (PreH25 e He). lia.
    - exact PreH28.
    - exact PreH7.
    - exact PreH22.
    - right.
      set (w := Znth current_edge l_weight_new_2 0) in *.
      set (lc :=
        Znth (Znth current_edge l_to_new_2 0) l_lowcost_cur_2 0) in *.
      change (lc <= w).
      destruct (Z.compare w lc) eqn:Hcmp.
      + apply Z.compare_eq_iff in Hcmp.
        rewrite Hcmp.
        apply Z.le_refl.
      + exfalso.
        unfold Z.ge in PreH1.
        rewrite Hcmp in PreH1.
        apply PreH1; reflexivity.
      + apply Z.compare_gt_iff in Hcmp.
        apply Z.lt_le_incl.
        exact Hcmp.
  }
  Exists s_2 s_after_2 l_from_new_2 l_first_2 l_link_2
         l_to_new_2 l_weight_new_2 l_lowcost_2 l_visited_2
         l_edge_parent_2 queue_map_before_2 l_lowcost_cur_2
         l_edge_parent_cur_2 queue_map_cur_2 selected_2.
  split_pure_spatial.
  - sepcon_assoc_change.
    cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_23_6 :
  prim_forward_star_heap_entail_wit_23_6.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  pose proof (prim_heap_scan_state_current_edge_range
    g_low_level_spec src_low_level_spec chosen s_2 s_after_2
    l_from_new_2 l_first_2 l_link_2 l_to_new_2 l_weight_new_2
    l_lowcost_2 (replace_Znth selected_2 1 l_visited_2) l_edge_parent_2
    l_lowcost_cur_2 l_edge_parent_cur_2 current_edge selected_2 min
    queue_map_before_2 l_lowcost_cur_2 l_edge_parent_cur_2 queue_map_cur_2
    X_low_level_spec PreH2 PreH17) as Hrange.
  assert (Hfalse : False) by lia.
  contradiction.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_23_7 :
  prim_forward_star_heap_entail_wit_23_7.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  pose proof (prim_heap_scan_state_current_edge_range
    g_low_level_spec src_low_level_spec chosen s_2 s_after_2
    l_from_new_2 l_first_2 l_link_2 l_to_new_2 l_weight_new_2
    l_lowcost_2 (replace_Znth selected_2 1 l_visited_2) l_edge_parent_2
    l_lowcost_cur_2 l_edge_parent_cur_2 current_edge selected_2 min
    queue_map_before_2 l_lowcost_cur_2 l_edge_parent_cur_2 queue_map_cur_2
    X_low_level_spec PreH3 PreH18) as Hrange.
  pose proof (array_graph_edge_count
    n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
    g_low_level_spec PreH22) as Hcount.
  assert (Hfalse : False) by lia.
  contradiction.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_24 :
  prim_forward_star_heap_entail_wit_24.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  assert (Hloop :
    prim_heap_loop_state g_low_level_spec src_low_level_spec chosen
      s_after_2 l_lowcost_cur (replace_Znth selected_2 1 l_visited_2)
      l_edge_parent_cur queue_map_cur X_low_level_spec).
  {
    subst current_edge.
    eapply prim_heap_scan_state_finish_loop.
    - exact PreH20.
    - exact PreH22.
    - exact PreH17.
    - exact PreH18.
    - exact PreH16.
  }
  unfold store_heap at 1.
  Intros key_values data_values pos_values.
  assert (Hheap_nonempty : chosen < n_pre -> heap_size > 0).
  {
    intro Hchosen_lt.
    destruct (prim_heap_loop_state_present_if_unfinished
      n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
      g_low_level_spec src_low_level_spec chosen s_after_2
      l_lowcost_cur (replace_Znth selected_2 1 l_visited_2)
      l_edge_parent_cur queue_map_cur X_low_level_spec
      PreH20 PreH21 Hchosen_lt Hloop) as [v [key Hpresent]].
    eapply heap_representation_present_size_positive; eauto.
  }
  unfold store_heap.
  Exists l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2
         s_after_2 l_lowcost_cur selected_2 l_visited_2
         l_edge_parent_cur queue_map_cur.
  Exists key_values data_values pos_values.
  entailer!.
  sep_apply (store_int_undef_store_int (&( "cur_edge" )) current_edge).
  sep_apply (store_int_undef_store_int (&( "min" )) min).
  cancel.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_26_1 :
  prim_forward_star_heap_entail_wit_26_1.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  assert (Hchosen_eq : chosen = n_pre).
  {
    destruct (Z_lt_ge_dec chosen n_pre) as [Hlt | Hge].
    - specialize (PreH22 Hlt). lia.
    - lia.
  }
  subst chosen.
  prop_apply (IntArray.full_Zlength lowcost n_pre l_lowcost_2).
  Intros_p Hlow_len.
  assert (Hdone :
    prim_heap_done_state g_low_level_spec src_low_level_spec s_2
      l_lowcost_2 l_visited_2 l_edge_parent_2 queue_map_2
      X_low_level_spec).
  {
    eapply prim_heap_loop_state_done; eauto; lia.
  }
  Exists l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2
         s_2 l_lowcost_2 l_visited_2 l_edge_parent_2 queue_map_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_26_2 :
  prim_forward_star_heap_entail_wit_26_2.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  assert (Hchosen_eq : chosen = n_pre) by lia.
  subst chosen.
  prop_apply (IntArray.full_Zlength lowcost n_pre l_lowcost_2).
  Intros_p Hlow_len.
  assert (Hdone :
    prim_heap_done_state g_low_level_spec src_low_level_spec s_2
      l_lowcost_2 l_visited_2 l_edge_parent_2 queue_map_2
      X_low_level_spec).
  {
    eapply prim_heap_loop_state_done; eauto; lia.
  }
  Exists l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2
         s_2 l_lowcost_2 l_visited_2 l_edge_parent_2 queue_map_2.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_27 :
  prim_forward_star_heap_entail_wit_27.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  prop_apply (IntArray.full_Zlength lowcost n_pre l_lowcost_2).
  Intros_p Hlow_len.
  pose proof PreH12 as Hdone.
  unfold prim_heap_done_state in PreH12.
  destruct PreH12 as
    [Hgrow [Hvisited [Hcount [Hselected [Hlow [Hmap Hsafe]]]]]].
  assert (Hstate_full : state_vertex_count s_2 = n_pre).
  { rewrite Hcount, Hlow_len. reflexivity. }
  assert (Hparent_all :
    forall v,
      1 <= v < n_pre ->
      0 <= Znth v l_edge_parent_2 0 < 2 * m_pre).
  {
    intros v Hv.
    eapply (parent_edges_match_state_all_range
      n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
      g_low_level_spec src_low_level_spec s_2 l_edge_parent_2 v);
      eauto; subst src_low_level_spec; lia.
  }
  assert (Hparent_one :
    1 < n_pre ->
      0 <= Znth 1 l_edge_parent_2 0 < 2 * m_pre).
  { intro Hlt; apply Hparent_all; lia. }
  assert (Hprefix :
    prim_result_graph_matches_array_prefix
      n_pre 0 nil nil nil g_low_level_spec s_2.(Prim.graph_in_state)
      l_edge_parent_2 l_from_new_2 l_to_new_2 l_weight_new_2).
  {
    unfold prim_result_graph_matches_array_prefix.
    split; [lia|].
    split; [rewrite Zlength_nil; lia|].
    split; [rewrite Zlength_nil; lia|].
    split; [rewrite Zlength_nil; lia|].
    intros k Hk.
    simpl in Hk.
    contradiction.
  }
  Exists nil nil nil s_2.(Prim.graph_in_state)
         s_2 l_lowcost_2 l_visited_2 l_edge_parent_2 queue_map_2
         l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2.
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
    cancel (IntArray.full from_new (2 * m_pre) l_from_new_2).
    cancel (IntArray.full to_new (2 * m_pre) l_to_new_2).
    cancel (IntArray.full weight_new (2 * m_pre) l_weight_new_2).
    cancel (IntArray.full first n_pre l_first_2).
    cancel (IntArray.full link (2 * m_pre) l_link_2).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full visited n_pre l_visited_2).
    cancel (IntArray.full edge_parent n_pre l_edge_parent_2).
    cancel (store_heap heap_cost heap_vertex heap_pos n_pre heap_capacity queue_map_2 heap_size).
    entailer!.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; exact Hdone);
      try (dump_pre_spatial; exact Hgrow);
      try (dump_pre_spatial; exact Hvisited);
      try (dump_pre_spatial; exact Hstate_full);
      try (dump_pre_spatial; exact Hselected);
      try (dump_pre_spatial; exact Hlow);
      try (dump_pre_spatial; exact Hsafe);
      try (dump_pre_spatial; exact Hprefix);
      try (dump_pre_spatial; exact Hparent_all);
      try (dump_pre_spatial; exact Hparent_one);
      try (dump_pre_spatial; unfold prim_state_graph_matches; reflexivity);
      try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_28 :
  prim_forward_star_heap_entail_wit_28.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  pose proof (PreH30 PreH1) as [Hedge_ge Hedge_lt].
  Exists l_out_u_2 l_out_v_2 l_out_wt_2 rg_2
         s_2 l_lowcost_2 l_visited_2 l_edge_parent_2 queue_map_2
         l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2.
  sep_apply_l_atomic
    (IntArray.full_split_to_missing_i
       edge_parent out_i n_pre l_edge_parent_2 0);
    [apply derivable1s_coq_prop_r; lia |].
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; exact Hedge_ge);
      try (dump_pre_spatial; exact Hedge_lt);
      try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_29 :
  prim_forward_star_heap_entail_wit_29.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  Exists l_out_u_2 l_out_v_2 l_out_wt_2 rg_2
         s_2 l_lowcost_2 l_visited_2 queue_map_2
         l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2
         l_edge_parent.
  sep_apply_l_atomic
    (IntArray.full_split_to_missing_i
       from_new (Znth out_i l_edge_parent 0)
       (2 * m_pre) l_from_new_2 0);
    [apply derivable1s_coq_prop_r; lia |].
  sep_apply_l_atomic
    (IntArray.full_split_to_missing_i
       to_new (Znth out_i l_edge_parent 0)
       (2 * m_pre) l_to_new_2 0);
    [apply derivable1s_coq_prop_r; lia |].
  sep_apply_l_atomic
    (IntArray.full_split_to_missing_i
       weight_new (Znth out_i l_edge_parent 0)
       (2 * m_pre) l_weight_new_2 0);
    [apply derivable1s_coq_prop_r; lia |].
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; reflexivity);
      try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_30 :
  prim_forward_star_heap_entail_wit_30.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  pose proof PreH22 as Hdirected.
  unfold directed_array_graph, directed_array_graph_prefix in PreH22.
  destruct PreH22 as [_ [Hfrom_len [Hto_len [Hwt_len _]]]].
  pose proof (array_graph_edge_count
    n_pre m_pre lf_low_level_spec lt_low_level_spec lw_low_level_spec
    g_low_level_spec PreH20) as Hedge_count.
  rewrite Hedge_count in Hfrom_len, Hto_len, Hwt_len.
  pose proof PreH29 as Hlow_orig.
  destruct PreH29 as [Hlp_len _].
  assert (Hout_graph : In out_i (graph_vertices g_low_level_spec)).
  { eapply array_graph_vertex_in; eauto; lia. }
  pose proof (Hlp_len out_i Hout_graph) as [_ Hparent_out_idx].
  assert (Hde_from_range :
    0 <= edge_id < Zlength l_from_new_2).
  {
    split; [exact PreH1 |].
    replace (Zlength l_from_new_2) with (2 * m_pre) by (symmetry; exact Hfrom_len).
    exact PreH2.
  }
  assert (Hde_to_range :
    0 <= edge_id < Zlength l_to_new_2).
  {
    split; [exact PreH1 |].
    replace (Zlength l_to_new_2) with (2 * m_pre) by (symmetry; exact Hto_len).
    exact PreH2.
  }
  assert (Hde_wt_range :
    0 <= edge_id < Zlength l_weight_new_2).
  {
    split; [exact PreH1 |].
    replace (Zlength l_weight_new_2) with (2 * m_pre) by (symmetry; exact Hwt_len).
    exact PreH2.
  }
  set (de := edge_id).
  set (new_u := Znth de l_from_new_2 0).
  set (new_v := Znth de l_to_new_2 0).
  set (new_w := Znth de l_weight_new_2 0).
  assert (Hprefix_next :
    prim_result_graph_matches_array_prefix
      n_pre (mst_idx + 1)
      (l_out_u_2 ++ (new_u :: nil))
      (l_out_v_2 ++ (new_v :: nil))
      (l_out_wt_2 ++ (new_w :: nil))
      g_low_level_spec rg_2
      l_edge_parent_2 l_from_new_2 l_to_new_2 l_weight_new_2).
  {
    subst de new_u new_v new_w.
    rewrite PreH4.
    eapply prim_result_graph_matches_array_prefix_snoc__prim_loop_close
      with (m := m_pre) (from := lf_low_level_spec)
           (to := lt_low_level_spec) (wt := lw_low_level_spec)
           (src := src_low_level_spec) (s := s_2)
           (idx := mst_idx) (v := out_i); eauto; lia.
  }
  Exists (l_out_u_2 ++ (new_u :: nil))
         (l_out_v_2 ++ (new_v :: nil))
         (l_out_wt_2 ++ (new_w :: nil))
         rg_2 s_2 l_lowcost_2 l_visited_2 l_edge_parent_2 queue_map_2
         l_first_2 l_link_2 l_from_new_2 l_to_new_2 l_weight_new_2.
  split_pure_spatial.
  - subst de new_u new_v new_w.
    sepcon_assoc_change.
    cancel (IntArray.full from_arr_pre m_pre lf_low_level_spec).
    cancel (IntArray.full to_arr_pre m_pre lt_low_level_spec).
    cancel (IntArray.full weight_arr_pre m_pre lw_low_level_spec).
    cancel (IntArray.seg out_u 0 (mst_idx + 1)
      (l_out_u_2 ++ Znth edge_id l_from_new_2 0 :: nil)).
    cancel (IntArray.undef_seg out_u (mst_idx + 1) (n_pre - 1)).
    cancel (IntArray.seg out_v 0 (mst_idx + 1)
      (l_out_v_2 ++ Znth edge_id l_to_new_2 0 :: nil)).
    cancel (IntArray.undef_seg out_v (mst_idx + 1) (n_pre - 1)).
    cancel (IntArray.seg out_wt 0 (mst_idx + 1)
      (l_out_wt_2 ++ Znth edge_id l_weight_new_2 0 :: nil)).
    cancel (IntArray.undef_seg out_wt (mst_idx + 1) (n_pre - 1)).
    cancel (IntArray.full from_new (2 * m_pre) l_from_new_2).
    cancel (IntArray.full to_new (2 * m_pre) l_to_new_2).
    cancel (IntArray.full weight_new (2 * m_pre) l_weight_new_2).
    cancel (IntArray.full first n_pre l_first_2).
    cancel (IntArray.full link (2 * m_pre) l_link_2).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full visited n_pre l_visited_2).
    cancel (IntArray.full edge_parent n_pre l_edge_parent_2).
    cancel (store_heap heap_cost heap_vertex heap_pos n_pre heap_capacity queue_map_2 heap_size).
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; exact Hdirected);
      try (dump_pre_spatial; exact Hlow_orig);
      try (dump_pre_spatial; exact Hprefix_next);
      try (dump_pre_spatial; lia);
      try solve [
        apply derivable1s_coq_prop_r;
        intro Hnext;
        apply PreH32;
        lia
      ].
Qed.

Lemma proof_of_prim_forward_star_heap_entail_wit_31 :
  prim_forward_star_heap_entail_wit_31.
Proof.
  left.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  assert (Hidx_full : mst_idx = n_pre - 1) by lia.
  assert (Hsafe_ret :
    safeExec (prim_state_graph_matches rg_2) (return tt) X_low_level_spec).
  {
    eapply safeExec_conseq; [exact PreH31 |].
    intros st Hst.
    unfold prim_state_is in Hst.
    subst st.
    exact PreH27.
  }
  assert (Hresult :
    prim_result_graph_matches_array
      n_pre l_out_u l_out_v l_out_wt g_low_level_spec rg_2).
  {
    rewrite Hidx_full in PreH28.
    eapply prim_result_graph_matches_array_of_full_prefix; eauto.
  }
  Exists l_link_2 l_first_2 l_weight_new_2 l_to_new_2 l_from_new_2
         s_2 l_lowcost_2 l_visited_2 l_edge_parent_2 queue_map_2
         l_out_u l_out_v l_out_wt rg_2.
  split_pure_spatial.
  - rewrite Hidx_full.
    rewrite IntArray.undef_seg_empty.
    rewrite IntArray.undef_seg_empty.
    rewrite IntArray.undef_seg_empty.
    sep_apply_l_atomic (IntArray.seg_to_full out_u 0 (n_pre - 1) l_out_u).
    sep_apply_l_atomic (IntArray.seg_to_full out_v 0 (n_pre - 1) l_out_v).
    sep_apply_l_atomic (IntArray.seg_to_full out_wt 0 (n_pre - 1) l_out_wt).
    replace (out_u + 0 * sizeof (INT)) with out_u by lia.
    replace (out_v + 0 * sizeof (INT)) with out_v by lia.
    replace (out_wt + 0 * sizeof (INT)) with out_wt by lia.
    replace (n_pre - 1 - 0) with (n_pre - 1) by lia.
    cancel (IntArray.full out_u (n_pre - 1) l_out_u).
    cancel (IntArray.full out_v (n_pre - 1) l_out_v).
    cancel (IntArray.full out_wt (n_pre - 1) l_out_wt).
    cancel (IntArray.full from_arr_pre m_pre lf_low_level_spec).
    cancel (IntArray.full to_arr_pre m_pre lt_low_level_spec).
    cancel (IntArray.full weight_arr_pre m_pre lw_low_level_spec).
    sep_apply store_int_undef_store_int.
    sep_apply store_int_undef_store_int.
    sep_apply store_ptr_undef_store_ptr.
    sep_apply store_ptr_undef_store_ptr.
    sep_apply store_ptr_undef_store_ptr.
    sep_apply store_int_undef_store_int.
    sep_apply store_int_undef_store_int.
    cancel (IntArray.full from_new (2 * m_pre) l_from_new_2).
    cancel (IntArray.full to_new (2 * m_pre) l_to_new_2).
    cancel (IntArray.full weight_new (2 * m_pre) l_weight_new_2).
    cancel (IntArray.full first n_pre l_first_2).
    cancel (IntArray.full link (2 * m_pre) l_link_2).
    cancel (IntArray.full lowcost n_pre l_lowcost_2).
    cancel (IntArray.full visited n_pre l_visited_2).
    cancel (IntArray.full edge_parent n_pre l_edge_parent_2).
    cancel (store_heap heap_cost heap_vertex heap_pos n_pre heap_capacity queue_map_2 heap_size).
    cancel.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; exact Hsafe_ret);
      try (dump_pre_spatial; exact Hresult);
      try (dump_pre_spatial; lia).
Qed.

Lemma proof_of_prim_forward_star_heap_return_wit_1 :
  prim_forward_star_heap_return_wit_1.
Proof.
  right.
  LLM_pre_process ltac:(lia || nia || int_auto || auto).
  Exists heap_cost heap_vertex heap_pos queue_map heap_size.
  Exists edge_parent l_edge_parent.
  Exists visited l_visited.
  Exists lowcost l_lowcost.
  Exists link l_link.
  Exists first l_first.
  Exists weight_new l_weight_new.
  Exists to_new l_to_new.
  Exists from_new l_from_new.
  Exists rg_2.
  rewrite PreH4.
  entailer!.
Qed.

Lemma proof_of_prim_forward_star_heap_partial_solve_wit_38_pure :
  prim_forward_star_heap_partial_solve_wit_38_pure.
Proof.
  right.
  LLM_pre_process ltac:(lia || nia || int_auto || auto);
    try subst; try entailer!.
Qed.

Lemma proof_of_prim_forward_star_heap_partial_solve_wit_39_pure :
  prim_forward_star_heap_partial_solve_wit_39_pure.
Proof.
  right.
  LLM_pre_process ltac:(lia || nia || int_auto || auto);
    try subst; try entailer!.
Qed.

Lemma proof_of_prim_forward_star_heap_partial_solve_wit_46_pure :
  prim_forward_star_heap_partial_solve_wit_46_pure.
Proof.
  right.
  LLM_pre_process ltac:(lia || nia || int_auto || auto);
    try subst; try entailer!.
Qed.

Lemma proof_of_prim_forward_star_heap_derive_high_level_spec_by_low_level_spec :
  prim_forward_star_heap_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists lf_high_level_spec lt_high_level_spec lw_high_level_spec
         g_high_level_spec src_high_level_spec
         (result_state (initStPred g_high_level_spec src_high_level_spec)
            (Prim2 g_high_level_spec)).
  repeat (split_pure_spatial || split_pures);
    try (dump_pre_spatial; assumption);
    try (dump_pre_spatial; lia);
    try (dump_pre_spatial;
      apply safeExec_result_state;
      exists (initSt g_high_level_spec src_high_level_spec);
      reflexivity).
  cancel (IntArray.full from_arr_pre m_pre lf_high_level_spec).
  cancel (IntArray.full to_arr_pre m_pre lt_high_level_spec).
  cancel (IntArray.full weight_arr_pre m_pre lw_high_level_spec).
  apply derivable1_wand_sepcon_adjoint.
  Intros rheapc rheapv rheappos rqmap rsize.
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
  Exists rheapc rheapv rheappos rqmap rsize.
  Exists redge ledge.
  Exists rvis lvis.
  Exists rlow llow.
  Exists rlink llink.
  Exists rfirst lfirst.
  Exists rweight lweight.
  Exists rto lto.
  Exists rfrom lfrom.
  Exists retwt retv.
  Exists retu lru lrv lrwt rg ret.
  split_pure_spatial.
  - sepcon_assoc_change; cancel.
  - split_pures;
      try (dump_pre_spatial; assumption);
      try (dump_pre_spatial; lia).
    apply derivable1s_coq_prop_r.
    match goal with
    | Hsafe : safeExec (prim_state_graph_matches ?rg0) (return tt) ?X,
      Henv : PrimEnv ?g0 ?src0 |- return_is_mst ?g0 ?rg0 =>
        unfold safeExec, safe in Hsafe;
        destruct Hsafe as [sigma [Hgraph Hsafe]];
        rewrite wp_ret in Hsafe;
        sets_unfold in Hsafe;
        unfold result_state in Hsafe;
        destruct Hsafe as [s0 [Hinit Hrun]];
        pose proof (Prim2_correct_concrete g0 src0 Henv) as Hhoare;
        unfold Hoare in Hhoare;
        specialize (Hhoare s0 tt sigma Hinit Hrun);
        unfold prim_state_graph_matches in Hgraph;
        rewrite <- Hgraph;
        exact Hhoare
    end.
Qed.
