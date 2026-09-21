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
From SimpleC.EE.LLM_bench.Algorithms.super_piano Require Import super_piano_goal.
From SimpleC.EE.LLM_bench.Algorithms.super_piano Require Import super_piano_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_lib.
Local Open Scope sac.

Require Import AUXLib.MonotonicList.

Ltac piano_cancel :=
  elim_emp; sepcon_right_assoc;
  repeat match goal with
  | |- ?P ** _ |-- _ => progress (cancel P)
  | |- ?P |-- ?P => apply derivable1_refl
  end; try cancel.

Ltac piano_split_pures :=
  repeat match goal with |- _ |-- ?A && ?B =>
    _assert_pure A; _assert_pure B; apply _derivable1_andp_intros end.

Ltac piano_input_bounds :=
  match goal with Hlo : Forall (Z.le (-1000)) ?l, Hhi : Forall (Z.ge 1000) ?l,
    Hlen : Zlength ?l = ?n |- _ =>
    assert (InputBounds : forall idx, 0 <= idx < n -> -1000 <= Znth idx l 0 <= 1000) by
      (intros idx Hi; pose proof (proj1 (Forall_Znth _ 0 l) Hlo idx ltac:(lia));
       pose proof (proj1 (Forall_Znth _ 0 l) Hhi idx ltac:(lia)); lia)
  end.

Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib.
Ltac piano_normalize_nodes :=
  repeat match goal with H : NodeArrays ?ns ?vs ?ss ?ls ?hs ?bs |- _ =>
    is_var ns; progress rewrite (piano_nodes_eq ns vs ss ls hs bs H) in * end.
Ltac piano_current_length :=
  match goal with H : NodeArrays ?ns ?vs ?ss ?ls ?hs ?bs |- ?P |-- _ =>
    match P with context [IntArray.full ?ptr ?cap vs] =>
      let Hv := fresh "Hvalues_length" in
      prop_apply (IntArray.full_Zlength ptr cap vs); Intros_p Hv;
      let Hn := fresh "Hnodes_length" in
      pose proof (piano_arrays_length ns vs ss ls hs bs H) as Hn;
      unfold PianoSwap in Hn; rewrite ?Zlength_replace_Znth in Hn
    end
  end.
Ltac piano_read_nodes :=
  repeat match goal with H : NodeArrays ?ns ?vs ?ss ?ls ?hs ?bs |- _ =>
    match goal with Hr : Znth ?i vs 0 < _ |- _ =>
      let Hv := fresh "Hread" in
      pose proof (proj1 (piano_arrays_read ns vs ss ls hs bs i H)) as Hv;
      progress rewrite Hv in Hr
    | Hr : _ < Znth ?i vs 0 |- _ =>
      let Hv := fresh "Hread" in
      pose proof (proj1 (piano_arrays_read ns vs ss ls hs bs i H)) as Hv;
      progress rewrite Hv in Hr
    | Hr : Znth ?i vs 0 >= _ |- _ =>
      let Hv := fresh "Hread" in
      pose proof (proj1 (piano_arrays_read ns vs ss ls hs bs i H)) as Hv;
      progress rewrite Hv in Hr
    | Hr : _ >= Znth ?i vs 0 |- _ =>
      let Hv := fresh "Hread" in
      pose proof (proj1 (piano_arrays_read ns vs ss ls hs bs i H)) as Hv;
      progress rewrite Hv in Hr
    end
  end.




Lemma proof_of_build_prefix_safety_wit_6 : build_prefix_safety_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  try piano_input_bounds.
  piano_normalize_nodes.
  assert (Hpref_bound : (-1000) * i <= Znth i pref 0 <= 1000 * i).
  {
    eapply PrefixArrayPrefix_entry_abs_bound; [exact PreH7 | | lia].
    intros idx Hidx.
    apply InputBounds.
    lia.
  }
  assert (Hl_bound : -1000 <= Znth i l 0 <= 1000) by (apply InputBounds; lia).
  replace (i - 0) with i by lia.
  split_pures.
  all: dump_pre_spatial; lia.
Qed.

Lemma proof_of_build_prefix_entail_wit_1 : build_prefix_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (0 :: nil).
  split_pure_spatial.
  - sep_apply (IntArray.seg_single pre_pre 0 0).
    replace (0 + 1) with 1 by lia. piano_cancel.
  - piano_split_pures; dump_pre_spatial; try assumption; try lia.
    unfold PrefixArrayPrefix. repeat split; cbn; try lia.
Qed.

Lemma proof_of_build_prefix_entail_wit_2 : build_prefix_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  try piano_input_bounds.
  piano_normalize_nodes.
  Exists (app pref_2 (cons (((Znth (i - 0) pref_2 0) + (Znth i l 0))) nil)).
  split_pure_spatial.
  - piano_cancel.
  - split_pures.
    all: try (dump_pre_spatial; try assumption; try lia; try (simpl; reflexivity)).
    match goal with
    | Hpref : PrefixArrayPrefix l pref_2 i |- _ =>
        unfold PrefixArrayPrefix in Hpref |- *;
        destruct Hpref as [Hpref_len [Hpref_zero Hpref_step]]
    end.
    repeat split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
    + rewrite app_Znth1 by (rewrite Hpref_len; lia).
      exact Hpref_zero.
    + intros j Hj.
      assert (Hj_cases : j < i \/ j = i) by lia.
      destruct Hj_cases as [Hj_lt | Hj_eq].
      * rewrite app_Znth1 by (rewrite Hpref_len; lia).
        rewrite app_Znth1 by (rewrite Hpref_len; lia).
        apply Hpref_step; lia.
      * subst j.
        rewrite app_Znth2 by (rewrite Hpref_len; lia).
        rewrite Hpref_len.
        rewrite app_Znth1 by (rewrite Hpref_len; lia).
        replace (i + 1 - (i + 1)) with 0 by lia.
        replace (i - 0) with i by lia.
        simpl.
        reflexivity.
Qed.

Lemma proof_of_build_prefix_return_wit_1 : build_prefix_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  try piano_input_bounds.
  piano_normalize_nodes.
  assert (Hi_eq : i = n_pre) by lia.
  Exists pref.
  subst i.
  split_pure_spatial.
  - rewrite (IntArray.undef_seg_empty pre_pre (n_pre + 1)).
    cancel (IntArray.full arr_pre n_pre l).
    sep_apply (IntArray.seg_to_full pre_pre 0 (n_pre + 1) pref).
    replace (pre_pre + 0 * sizeof(INT)) with pre_pre by lia.
    replace (n_pre + 1 - 0) with (n_pre + 1) by lia.
    cancel.
  - dump_pre_spatial. apply PrefixSums_recurrence.
    replace (Zlength l) with n_pre by lia. assumption.
Qed.

Lemma proof_of_build_sparse_argmax_entail_wit_3 : build_sparse_argmax_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = len_pre * 17) by lia. subst i.
  Exists table_2.
  split_pure_spatial.
  - unfold IntArray.full.
    rewrite (IntArray.undef_seg_empty st_pre (len_pre * 17)).
    cancel (IntArray.seg pre_pre 0 len_pre ps).
    cancel (IntArray.seg st_pre 0 (len_pre * 17) table_2).
    cancel.
  - split_pures; dump_pre_spatial; try lia; apply piano_sparse_base_start.
Qed.

Lemma proof_of_build_sparse_argmax_entail_wit_4 : build_sparse_argmax_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength st_pre (len_pre * 17) (replace_Znth (i * 17) i table_2)).
  Intros_p Hlen. rewrite Zlength_replace_Znth in Hlen.
  Exists (replace_Znth (i * 17) i table_2).
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    eapply piano_sparse_base_step; eauto; unfold ST_LEVELS; lia.
Qed.

Lemma proof_of_build_sparse_argmax_entail_wit_5 : build_sparse_argmax_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = len_pre) by lia. subst i.
  Exists table_2.
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    all: try reflexivity.
    eapply piano_sparse_base_complete; eassumption.
Qed.

Lemma proof_of_build_sparse_argmax_entail_wit_7 : build_sparse_argmax_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (piano_sparse_read ps table len_pre level i half width
    ltac:(unfold ST_LEVELS; lia) PreH6 PreH7 ltac:(lia) PreH1 PreH13) as [Ha Hb].
  unfold ST_LEVELS in Ha, Hb.
  apply piano_argmax_view in Ha, Hb. destruct Ha as [Ha _], Hb as [Hb _].
  unfold ST_LEVELS in Ha, Hb.
  Exists table.
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_build_sparse_argmax_entail_wit_8_1 : build_sparse_argmax_entail_wit_8_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength st_pre (len_pre * 17)
    (replace_Znth (i * 17 + level) a table_2)).
  Intros_p Hlen. rewrite Zlength_replace_Znth in Hlen.
  pose proof (piano_sparse_read ps table_2 len_pre level i half width
    ltac:(unfold ST_LEVELS; lia) PreH6 PreH7 ltac:(lia) PreH12 PreH19) as [Ha Hb].
  unfold ST_LEVELS in Ha, Hb.
  rewrite <- PreH13 in Ha. rewrite <- PreH14 in Hb.
  assert (Hbest : RangeArgmax ps i (i + Power2 level - 1) a).
  { rewrite <- PreH7. eapply piano_argmax_left with (a_hi := i + half - 1) (b_lo := i + half);
      eauto; lia. }
  Exists (replace_Znth (i * 17 + level) a table_2).
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    eapply piano_sparse_write; eauto; unfold ST_LEVELS; lia.
Qed.

Lemma proof_of_build_sparse_argmax_entail_wit_8_2 : build_sparse_argmax_entail_wit_8_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength st_pre (len_pre * 17)
    (replace_Znth (i * 17 + level) c table_2)).
  Intros_p Hlen. rewrite Zlength_replace_Znth in Hlen.
  pose proof (piano_sparse_read ps table_2 len_pre level i half width
    ltac:(unfold ST_LEVELS; lia) PreH6 PreH7 ltac:(lia) PreH12 PreH19) as [Ha Hb].
  unfold ST_LEVELS in Ha, Hb.
  rewrite <- PreH13 in Ha. rewrite <- PreH14 in Hb.
  assert (Hbest : RangeArgmax ps i (i + Power2 level - 1) c).
  { rewrite <- PreH7. eapply piano_argmax_right with (a_hi := i + half - 1) (b_lo := i + half);
      eauto; lia. }
  Exists (replace_Znth (i * 17 + level) c table_2).
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    eapply piano_sparse_write; eauto; unfold ST_LEVELS; lia.
Qed.

Lemma proof_of_build_sparse_argmax_entail_wit_9 : build_sparse_argmax_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Power2_step level ltac:(lia)) as Hpow.
  pose proof (piano_power_bound level ltac:(lia)) as Hbound.
  Exists table_2.
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    all: try (replace (level + 1 - 1) with level by lia; lia).
    eapply piano_sparse_level_complete; eauto; unfold ST_LEVELS; lia.
Qed.

Lemma proof_of_build_sparse_argmax_return_wit_1 : build_sparse_argmax_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (level = ST_LEVELS) by (unfold ST_LEVELS; lia). subst level.
  Exists table_2.
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    apply piano_sparse_complete; assumption.
Qed.

Lemma proof_of_query_argmax_entail_wit_1 : query_argmax_entail_wit_1.
Proof. LLM_pre_process ltac:(lia || nia || int_auto). Qed.

Lemma proof_of_query_argmax_entail_wit_2 : query_argmax_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (piano_query_next_level len_pre lo_pre hi_pre level width
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PreH9 PreH1) as Hnext.
  pose proof (Power2_step level ltac:(lia)) as Hpow.
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    all: unfold ST_LEVELS in *; lia.
Qed.

Lemma proof_of_query_argmax_entail_wit_3 : query_argmax_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH12 lo_pre level ltac:(lia) ltac:(unfold ST_LEVELS; lia) ltac:(lia)) as Ha.
  pose proof (PreH12 (hi_pre - width + 1) level ltac:(lia) ltac:(unfold ST_LEVELS; lia) ltac:(lia)) as Hb.
  apply piano_argmax_view in Ha, Hb. destruct Ha as [Ha _], Hb as [Hb _].
  unfold ST_LEVELS in Ha, Hb.
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_query_argmax_return_wit_1 : query_argmax_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (piano_sparse_query ps st_slots len_pre lo_pre hi_pre level width
    ltac:(lia) ltac:(lia) ltac:(unfold ST_LEVELS; lia) PreH9
    ltac:(lia) ltac:(lia) ltac:(lia) PreH19) as Hresult.
  unfold ST_LEVELS in Hresult.
  rewrite <- PreH13, <- PreH14 in Hresult.
  destruct (Z.geb_spec (Znth a ps 0) (Znth c ps 0)); try lia.
  pose proof (proj1 (piano_argmax_view _ _ _ _) Hresult) as [Hbounds _].
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_query_argmax_return_wit_2 : query_argmax_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (piano_sparse_query ps st_slots len_pre lo_pre hi_pre level width
    ltac:(lia) ltac:(lia) ltac:(unfold ST_LEVELS; lia) PreH9
    ltac:(lia) ltac:(lia) ltac:(lia) PreH19) as Hresult.
  unfold ST_LEVELS in Hresult.
  rewrite <- PreH13, <- PreH14 in Hresult.
  destruct (Z.geb_spec (Znth a ps 0) (Znth c ps 0)); try lia.
  pose proof (proj1 (piano_argmax_view _ _ _ _) Hresult) as [Hbounds _].
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_piano_set_node_return_wit_1_split_goal_1 : piano_set_node_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply piano_arrays_set; eassumption.
Qed.

Lemma proof_of_piano_set_node_return_wit_1 : piano_set_node_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_piano_set_node_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_piano_swap_node_return_wit_1_split_goal_1 : piano_swap_node_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply piano_arrays_swap; eassumption.
Qed.

Lemma proof_of_piano_swap_node_return_wit_1 : piano_swap_node_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_piano_swap_node_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_frontier_top_value_return_wit_1_split_goal_1 : frontier_top_value_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : NodeArrays ?slots ?vals ?starts ?los ?his ?bests |- _ =>
    pose proof (piano_arrays_read slots vals starts los his bests 0 H) as (Hv & Hs & Hl & Hh & Hb)
  end.
  unfold heap_top_value, heap_top_start, heap_top_lo, heap_top_hi, heap_top_best, heap_top_node.
  assumption.
Qed.

Lemma proof_of_frontier_top_value_return_wit_1 : frontier_top_value_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_frontier_top_value_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_frontier_top_start_return_wit_1_split_goal_1 : frontier_top_start_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : NodeArrays ?slots ?vals ?starts ?los ?his ?bests |- _ =>
    pose proof (piano_arrays_read slots vals starts los his bests 0 H) as (Hv & Hs & Hl & Hh & Hb)
  end.
  unfold heap_top_value, heap_top_start, heap_top_lo, heap_top_hi, heap_top_best, heap_top_node.
  assumption.
Qed.

Lemma proof_of_frontier_top_start_return_wit_1 : frontier_top_start_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_frontier_top_start_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_frontier_top_lo_return_wit_1_split_goal_1 : frontier_top_lo_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : NodeArrays ?slots ?vals ?starts ?los ?his ?bests |- _ =>
    pose proof (piano_arrays_read slots vals starts los his bests 0 H) as (Hv & Hs & Hl & Hh & Hb)
  end.
  unfold heap_top_value, heap_top_start, heap_top_lo, heap_top_hi, heap_top_best, heap_top_node.
  assumption.
Qed.

Lemma proof_of_frontier_top_lo_return_wit_1 : frontier_top_lo_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_frontier_top_lo_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_frontier_top_hi_return_wit_1_split_goal_1 : frontier_top_hi_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : NodeArrays ?slots ?vals ?starts ?los ?his ?bests |- _ =>
    pose proof (piano_arrays_read slots vals starts los his bests 0 H) as (Hv & Hs & Hl & Hh & Hb)
  end.
  unfold heap_top_value, heap_top_start, heap_top_lo, heap_top_hi, heap_top_best, heap_top_node.
  assumption.
Qed.

Lemma proof_of_frontier_top_hi_return_wit_1 : frontier_top_hi_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_frontier_top_hi_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_frontier_top_best_return_wit_1_split_goal_1 : frontier_top_best_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : NodeArrays ?slots ?vals ?starts ?los ?his ?bests |- _ =>
    pose proof (piano_arrays_read slots vals starts los his bests 0 H) as (Hv & Hs & Hl & Hh & Hb)
  end.
  unfold heap_top_value, heap_top_start, heap_top_lo, heap_top_hi, heap_top_best, heap_top_node.
  assumption.
Qed.

Lemma proof_of_frontier_top_best_return_wit_1 : frontier_top_best_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_frontier_top_best_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_frontier_pop_only_entail_wit_1 : frontier_pop_only_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (piano_arrays_node (PianoNodes vals starts los his bests)
    vals starts los his bests (size_pre - 1) PreH7) in PreH1.
  Exists vals_out starts_out los_out his_out bests_out
    (replace_Znth 0 (Znth (size_pre - 1) (PianoNodes vals starts los his bests) default_node)
      (PianoNodes vals starts los his bests)).
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    apply piano_pop_start; auto; lia.
Qed.

Lemma proof_of_frontier_pop_only_entail_wit_2_1 : frontier_pop_only_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes. piano_current_length. piano_read_nodes.
  Exists vals_cur_2 starts_cur_2 los_cur_2 his_cur_2 bests_cur_2 current_2.
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    replace (index * 2 + 1 + 1) with (index * 2 + 2) in * by lia.
    apply piano_selected_right; auto; try lia.

Qed.

Lemma proof_of_frontier_pop_only_entail_wit_2_2 : frontier_pop_only_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes. piano_current_length. piano_read_nodes.
  Exists vals_cur_2 starts_cur_2 los_cur_2 his_cur_2 bests_cur_2 current_2.
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    replace (index * 2 + 1 + 1) with (index * 2 + 2) in * by lia.
    apply piano_selected_left; auto; try lia.
    all: first [left; lia | right; assumption].
Qed.

Lemma proof_of_frontier_pop_only_entail_wit_2_3 : frontier_pop_only_entail_wit_2_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes. piano_current_length. piano_read_nodes.
  Exists vals_cur_2 starts_cur_2 los_cur_2 his_cur_2 bests_cur_2 current_2.
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    replace (index * 2 + 1 + 1) with (index * 2 + 2) in * by lia.
    apply piano_selected_left; auto; try lia.
    all: first [left; lia | right; assumption].
Qed.

Lemma proof_of_frontier_pop_only_entail_wit_3 : frontier_pop_only_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes. piano_current_length. piano_read_nodes.
  Exists vals_out starts_out los_out his_out bests_out (PianoSwap current_2 index selected).
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    apply piano_pop_swap; auto; lia.
Qed.

Lemma proof_of_frontier_pop_only_return_wit_1 : frontier_pop_only_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (size_pre = 1) by lia. subst size_pre.
  pose proof (piano_pop_singleton (PianoNodes vals starts los his bests) ltac:(lia)) as [Hheap Hpop].
  Exists vals starts los his bests (PianoNodes vals starts los his bests).
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_frontier_pop_only_return_wit_2 : frontier_pop_only_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes. piano_current_length. piano_read_nodes.
  assert (Hstop : index * 2 + 1 >= size_pre - 1 \/ exists sel,
    0 <= sel < size_pre - 1 /\ PianoHeapSelected current (size_pre - 1) index sel /\
    node_value (Znth sel current default_node) <= node_value (Znth index current default_node)).
  { left; lia. }
  pose proof (piano_pop_finish (PianoNodes vals starts los his bests) current size_pre index
    ltac:(lia) ltac:(lia) ltac:(eassumption) Hstop) as [Hheap Hpop].
  Exists vals_cur starts_cur los_cur his_cur bests_cur current.
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    all: first [exact Hpop | exact (eq_trans (eq_sym Hnodes_length) Hvalues_length)].
Qed.

Lemma proof_of_frontier_pop_only_return_wit_3 : frontier_pop_only_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes. piano_current_length. piano_read_nodes.
  assert (Hstop : index * 2 + 1 >= size_pre - 1 \/ exists sel,
    0 <= sel < size_pre - 1 /\ PianoHeapSelected current (size_pre - 1) index sel /\
    node_value (Znth sel current default_node) <= node_value (Znth index current default_node)).
  { right; exists selected; split; [lia|]. split; [assumption|]. apply Z.ge_le; exact PreH1. }
  pose proof (piano_pop_finish (PianoNodes vals starts los his bests) current size_pre index
    ltac:(lia) ltac:(lia) ltac:(eassumption) Hstop) as [Hheap Hpop].
  Exists vals_cur starts_cur los_cur his_cur bests_cur current.
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    all: first [exact Hpop | exact (eq_trans (eq_sym Hnodes_length) Hvalues_length)].
Qed.

Lemma proof_of_frontier_pop_only_partial_solve_wit_11_pure : frontier_pop_only_partial_solve_wit_11_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes.
  piano_split_pures; dump_pre_spatial; try assumption; try congruence; try (solve [etransitivity; eassumption]); lia.
Qed.

Lemma proof_of_frontier_push_entail_wit_1 : frontier_push_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (replace_Znth size_pre (mkNode value_pre start_pre lo_pre hi_pre best_pre)
    (PianoNodes vals starts los his bests)) vals_out starts_out los_out his_out bests_out.
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    apply piano_push_start; auto; lia.
Qed.

Lemma proof_of_frontier_push_entail_wit_2 : frontier_push_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (heap_parent_positive_bounds__push_sift_up child size_pre ltac:(lia) ltac:(lia)) as Hp.
  unfold heap_parent in Hp.
  Exists current_2 vals_cur_2 starts_cur_2 los_cur_2 his_cur_2 bests_cur_2.
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
Qed.

Lemma proof_of_frontier_push_entail_wit_3 : frontier_push_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes. piano_current_length. piano_read_nodes.
  assert (Hparent : parent = heap_parent child) by (unfold heap_parent; assumption).
  Exists (PianoSwap current_2 parent child) vals_out starts_out los_out his_out bests_out.
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    rewrite Hparent. apply piano_push_swap; auto; try lia.
    rewrite <- Hparent. assumption.
Qed.

Lemma proof_of_frontier_push_return_wit_1 : frontier_push_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes. piano_current_length. piano_read_nodes.
  assert (Hstop : child = 0 \/ node_value (Znth child current default_node) <=
    node_value (Znth (heap_parent child) current default_node)).
  { left; lia. }
  pose proof (piano_push_finish (PianoNodes vals starts los his bests) current size_pre child
    (mkNode value_pre start_pre lo_pre hi_pre best_pre) ltac:(lia) ltac:(lia) ltac:(eassumption) Hstop) as [Hheap Hperm].
  Exists vals_cur starts_cur los_cur his_cur bests_cur current.
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    all: try (rewrite <- Hnodes_length; exact Hvalues_length).
    all: first [exact Hperm | exact (eq_trans (eq_sym Hnodes_length) Hvalues_length)].
Qed.

Lemma proof_of_frontier_push_return_wit_2 : frontier_push_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes. piano_current_length. piano_read_nodes.
  assert (Hstop : child = 0 \/ node_value (Znth child current default_node) <=
    node_value (Znth (heap_parent child) current default_node)).
  { right. unfold heap_parent. rewrite <- PreH8. apply Z.ge_le. exact PreH1. }
  pose proof (piano_push_finish (PianoNodes vals starts los his bests) current size_pre child
    (mkNode value_pre start_pre lo_pre hi_pre best_pre) ltac:(lia) ltac:(lia) ltac:(eassumption) Hstop) as [Hheap Hperm].
  Exists vals_cur starts_cur los_cur his_cur bests_cur current.
  split_pure_spatial.
  - piano_cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    all: try (rewrite <- Hnodes_length; exact Hvalues_length).
    all: first [exact Hperm | exact (eq_trans (eq_sym Hnodes_length) Hvalues_length)].
Qed.

Lemma proof_of_frontier_push_partial_solve_wit_4_pure : frontier_push_partial_solve_wit_4_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes.
  piano_split_pures; dump_pre_spatial; try assumption; try congruence; try (solve [etransitivity; eassumption]); lia.
Qed.

Lemma proof_of_build_initial_frontier_safety_wit_23 : build_initial_frontier_safety_wit_23.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength pre_pre (n_pre + 1) ps). Intros_p Hlen.
  assert (Hb : forall j, 0 <= j <= n_pre -> -100000000 <= Znth j ps 0 <= 100000000).
  { intros j Hj.
    pose proof (proj1 (Forall_Znth _ 0 ps) PreH18 j ltac:(lia)).
    pose proof (proj1 (Forall_Znth _ 0 ps) PreH19 j ltac:(lia)). lia. }
  pose proof (Hb retval ltac:(lia)). pose proof (Hb (start - 1) ltac:(lia)).
  piano_split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_build_initial_frontier_safety_wit_26 : build_initial_frontier_safety_wit_26.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength pre_pre (n_pre + 1) ps). Intros_p Hlen.
  assert (Hb : forall j, 0 <= j <= n_pre -> -100000000 <= Znth j ps 0 <= 100000000).
  { intros j Hj.
    pose proof (proj1 (Forall_Znth _ 0 ps) PreH18 j ltac:(lia)).
    pose proof (proj1 (Forall_Znth _ 0 ps) PreH19 j ltac:(lia)). lia. }
  pose proof (Hb retval ltac:(lia)). pose proof (Hb (start - 1) ltac:(lia)).
  piano_split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_build_initial_frontier_entail_wit_3 : build_initial_frontier_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = cap_pre) by lia. subst i.
  prop_apply (IntArray.seg_Zlength heap_value_pre 0 cap_pre vals_2). Intros_p H_vals.
  prop_apply (IntArray.seg_Zlength heap_start_pre 0 cap_pre starts_2). Intros_p H_starts.
  prop_apply (IntArray.seg_Zlength heap_lo_pre 0 cap_pre los_2). Intros_p H_los.
  prop_apply (IntArray.seg_Zlength heap_hi_pre 0 cap_pre his_2). Intros_p H_his.
  prop_apply (IntArray.seg_Zlength heap_best_pre 0 cap_pre bests_2). Intros_p H_bests.
  assert (Hnodes : NodeArrays (PianoNodes vals_2 starts_2 los_2 his_2 bests_2)
    vals_2 starts_2 los_2 his_2 bests_2) by (apply piano_nodes_wf; lia).
  pose proof (piano_arrays_length _ _ _ _ _ _ Hnodes) as Hnodeslen.
  Exists vals_2 starts_2 los_2 his_2 bests_2 (PianoNodes vals_2 starts_2 los_2 his_2 bests_2).
  split_pure_spatial.
  - rewrite !IntArray.undef_seg_empty.
    sep_apply (IntArray.seg_to_full heap_value_pre 0 cap_pre vals_2).
    sep_apply (IntArray.seg_to_full heap_start_pre 0 cap_pre starts_2).
    sep_apply (IntArray.seg_to_full heap_lo_pre 0 cap_pre los_2).
    sep_apply (IntArray.seg_to_full heap_hi_pre 0 cap_pre his_2).
    sep_apply (IntArray.seg_to_full heap_best_pre 0 cap_pre bests_2).
    replace (cap_pre - 0) with cap_pre by lia.
    replace (heap_value_pre + 0 * sizeof(INT)) with heap_value_pre by lia.
    replace (heap_start_pre + 0 * sizeof(INT)) with heap_start_pre by lia.
    replace (heap_lo_pre + 0 * sizeof(INT)) with heap_lo_pre by lia.
    replace (heap_hi_pre + 0 * sizeof(INT)) with heap_hi_pre by lia.
    replace (heap_best_pre + 0 * sizeof(INT)) with heap_best_pre by lia.
    piano_cancel.
  - piano_split_pures; dump_pre_spatial; auto; try (timeout 2 lia).
    + rewrite Zsublist_nil by lia; apply piano_initial_empty.
    + rewrite Z.sub_0_r in H_vals. exact (eq_trans (eq_sym Hnodeslen) H_vals).
    + apply piano_heap_from_order; [pose proof (Zlength_nonneg (PianoNodes vals_2 starts_2 los_2 his_2 bests_2)); lia|].
      intros child H; lia.
Qed.

Lemma proof_of_build_initial_frontier_entail_wit_4_1 : build_initial_frontier_entail_wit_4_1.
Proof.
  unfold build_initial_frontier_entail_wit_4_1; left; intros.
  prop_apply (IntArray.full_Zlength pre_pre (n_pre + 1) ps). Intros_p Hpslen.
  assert (Hnode : ValidNodeFields ps n_pre L_pre R_pre
    (Znth retval ps 0 - Znth (start-1) ps 0) start (start+L_pre-1) (n_pre) retval).
  { eapply piano_initial_node; try eassumption; try reflexivity; try lia.
    all: rewrite Z.min_l; lia. }
  piano_normalize_nodes.
  unfold FrontierPushFields, FrontierPushPrefix in PreH4. destruct PreH4 as [_ Hperm].
  Exists vals_out starts_out los_out his_out bests_out slots_out.
  split_pure_spatial.
  - piano_cancel.
  - piano_split_pures; dump_pre_spatial; try assumption; try lia.
    eapply piano_initial_step with (nodes := sublist 0 size slots_2)
      (nd := mkNode (Znth retval ps 0 - Znth (start-1) ps 0) start (start+L_pre-1) (n_pre) retval);
      eauto; cbn; try lia.
    all: rewrite Z.min_l; lia.
Qed.

Lemma proof_of_build_initial_frontier_entail_wit_4_2 : build_initial_frontier_entail_wit_4_2.
Proof.
  unfold build_initial_frontier_entail_wit_4_2; left; intros.
  prop_apply (IntArray.full_Zlength pre_pre (n_pre + 1) ps). Intros_p Hpslen.
  assert (Hnode : ValidNodeFields ps n_pre L_pre R_pre
    (Znth retval ps 0 - Znth (start-1) ps 0) start (start+L_pre-1) (start+R_pre-1) retval).
  { eapply piano_initial_node; try eassumption; try reflexivity; try lia.
    all: rewrite Z.min_r; lia. }
  piano_normalize_nodes.
  unfold FrontierPushFields, FrontierPushPrefix in PreH4. destruct PreH4 as [_ Hperm].
  Exists vals_out starts_out los_out his_out bests_out slots_out.
  split_pure_spatial.
  - piano_cancel.
  - piano_split_pures; dump_pre_spatial; try assumption; try lia.
    eapply piano_initial_step with (nodes := sublist 0 size slots_2)
      (nd := mkNode (Znth retval ps 0 - Znth (start-1) ps 0) start (start+L_pre-1) (start+R_pre-1) retval);
      eauto; cbn; try lia.
    all: rewrite Z.min_r; lia.
Qed.

Lemma proof_of_build_initial_frontier_return_wit_1 : build_initial_frontier_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (start = n_pre - L_pre + 2) by lia.
  Exists vals_2 starts_2 los_2 his_2 bests_2 slots_2.
  split_pure_spatial.
  - piano_cancel.
  - piano_split_pures; dump_pre_spatial; auto; try (timeout 2 lia).
    apply piano_initial_complete; try lia. subst start; assumption.
Qed.

Lemma proof_of_build_initial_frontier_partial_solve_wit_12_pure : build_initial_frontier_partial_solve_wit_12_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes.
  piano_split_pures; dump_pre_spatial; try assumption; try congruence; try (solve [etransitivity; eassumption]); lia.
Qed.

Lemma proof_of_build_initial_frontier_partial_solve_wit_13_pure : build_initial_frontier_partial_solve_wit_13_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes.
  piano_split_pures; dump_pre_spatial; try assumption; try congruence; try (solve [etransitivity; eassumption]); lia.
Qed.

Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg.

Lemma proof_of_superPiano_safety_wit_50 : superPiano_safety_wit_50.
Proof.
  LLM_pre_process ltac:(int_auto).
  try piano_input_bounds.
  piano_normalize_nodes.
  assert (Hvalue_int : -2147483648 <= value <= 2147483647).
  {
    match goal with
    | Hvalid : ValidNodeFields ps n_pre L_pre R_pre value start lo hi best |- _ =>
        unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid; cbn in Hvalid;
        destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ [_ [Hvalue _]]]]]]]]];
        rewrite Hvalue
    end.
    eapply PrefixSums_diff_int_bounds; eauto; lia.
  }
  pose proof
    (frontier_total_int64_bound
       l ps n_pre L_pre R_pre chosen t total (sublist 0 hsize pop_slots)
       PreH19 PreH18 PreH11 InputBounds PreH29) as Htotal_bound.
  piano_split_pures.
  all: dump_pre_spatial; lia.
Qed.

Lemma proof_of_superPiano_safety_wit_65 : superPiano_safety_wit_65.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat match goal with H : ?r = Znth _ _ _ |- _ => is_var r; subst r end.
  try piano_input_bounds.
  piano_normalize_nodes.
  match goal with |- _ |-- ?P => lazymatch P with context [Znth ?i ?ps 0 - Znth ?j ?ps 0] =>
    assert (Hdiff : -2147483648 <= Znth i ps 0 - Znth j ps 0 <= 2147483647) by
      (eapply PrefixSums_diff_int_bounds; eauto; lia)
  end end.
  piano_split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_superPiano_safety_wit_91 : superPiano_safety_wit_91.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat match goal with H : ?r = Znth _ _ _ |- _ => is_var r; subst r end.
  try piano_input_bounds.
  piano_normalize_nodes.
  match goal with |- _ |-- ?P => lazymatch P with context [Znth ?i ?ps 0 - Znth ?j ?ps 0] =>
    assert (Hdiff : -2147483648 <= Znth i ps 0 - Znth j ps 0 <= 2147483647) by
      (eapply PrefixSums_diff_int_bounds; eauto; lia)
  end end.
  piano_split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_superPiano_safety_wit_100 : superPiano_safety_wit_100.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat match goal with H : ?r = Znth _ _ _ |- _ => is_var r; subst r end.
  try piano_input_bounds.
  piano_normalize_nodes.
  match goal with |- _ |-- ?P => lazymatch P with context [Znth ?i ?ps 0 - Znth ?j ?ps 0] =>
    assert (Hdiff : -2147483648 <= Znth i ps 0 - Znth j ps 0 <= 2147483647) by
      (eapply PrefixSums_diff_int_bounds; eauto; lia)
  end end.
  piano_split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_superPiano_entail_wit_1 : superPiano_entail_wit_1.
Proof.
  left. intros. Exists ans_2 ps_2. split_pure_spatial.
  - assert (Hprefix_bound : 0 <= n_pre + 1 <= 100001) by lia.
    assert (Hsparse_bound : 0 <= (n_pre + 1) * 17 <= 1700017) by lia.
    assert (Hheap_bound : 0 <= n_pre + k_pre + 1 <= 200000) by lia.
    remember 100001 as prefix_capacity eqn:Hprefix_capacity in *.
    remember 1700017 as sparse_capacity eqn:Hsparse_capacity in *.
    remember 200000 as heap_capacity eqn:Hheap_capacity in *.
    clear Hprefix_capacity Hsparse_capacity Hheap_capacity.
    simpl. rewrite !Z.add_0_r.
    sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&( "prefix" )) (n_pre+1) prefix_capacity ltac:(lia)).
    sep_apply_l_atomic (IntArray.undef_seg_to_undef_full (&( "prefix" )) 0 (n_pre+1)).
    sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&( "st" )) ((n_pre+1)*17) sparse_capacity ltac:(lia)).
    sep_apply_l_atomic (IntArray.undef_seg_to_undef_full (&( "st" )) 0 ((n_pre+1)*17)).
    sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&( "heap_value" )) (n_pre+k_pre+1) heap_capacity ltac:(lia)).
    sep_apply_l_atomic (IntArray.undef_seg_to_undef_full (&( "heap_value" )) 0 (n_pre+k_pre+1)).
    sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&( "heap_start" )) (n_pre+k_pre+1) heap_capacity ltac:(lia)).
    sep_apply_l_atomic (IntArray.undef_seg_to_undef_full (&( "heap_start" )) 0 (n_pre+k_pre+1)).
    sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&( "heap_lo" )) (n_pre+k_pre+1) heap_capacity ltac:(lia)).
    sep_apply_l_atomic (IntArray.undef_seg_to_undef_full (&( "heap_lo" )) 0 (n_pre+k_pre+1)).
    sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&( "heap_hi" )) (n_pre+k_pre+1) heap_capacity ltac:(lia)).
    sep_apply_l_atomic (IntArray.undef_seg_to_undef_full (&( "heap_hi" )) 0 (n_pre+k_pre+1)).
    sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&( "heap_best" )) (n_pre+k_pre+1) heap_capacity ltac:(lia)).
    sep_apply_l_atomic (IntArray.undef_seg_to_undef_full (&( "heap_best" )) 0 (n_pre+k_pre+1)).
    simpl. rewrite !Z.add_0_r, !Z.sub_0_r. piano_cancel.
  - entailer!.
Qed.

Lemma proof_of_superPiano_entail_wit_2 : superPiano_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  try piano_input_bounds.
  piano_normalize_nodes.
  assert (Hps_eq : ps_3 = ps_2).
  {
    eapply PrefixSums_functional; eauto.
  }
  subst ps_3.
  Exists ans_2; Exists (zeros ((n_pre + 1) * ST_LEVELS)); Exists ps_2.
  split_pure_spatial.
  - piano_cancel.
  - piano_split_pures.
    all: try (dump_pre_spatial; try assumption; try (timeout 2 lia)).
    + rewrite Zlength_correct.
      unfold zeros.
      rewrite repeat_length.
      unfold ST_LEVELS.
      rewrite Z2Nat.id by lia.
      lia.
Qed.

Lemma proof_of_superPiano_entail_wit_3 : superPiano_entail_wit_3.
Proof.
  unfold superPiano_entail_wit_3; left; intros.
  unfold InitialFrontierState in PreH5.
  Exists (@nil Z) vals_2 starts_2 los_2 his_2 bests_2 slots_2 ans_2 table ps_2.
  split_pure_spatial.
  - piano_cancel.
  - piano_split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_superPiano_entail_wit_4 : superPiano_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  try piano_input_bounds.
  piano_normalize_nodes.
  assert (Hhsize_pos : 0 < hsize) by (apply PreH38; exact PreH16).
  assert (Hslots_len : hsize <= Zlength slots_2).
  { rewrite PreH29. exact PreH34. }
  pose proof
    (frontier_state_top_node_valid
      ps_2 n_pre L_pre R_pre chosen_2 t total slots_2 hsize
      Hhsize_pos Hslots_len PreH36)
    as Htop_valid.
  assert (
    ValidNodeFields ps_2 n_pre L_pre R_pre
      (heap_top_value slots_2) (heap_top_start slots_2)
      (heap_top_lo slots_2) (heap_top_hi slots_2) (heap_top_best slots_2))
    by exact Htop_valid.
  assert (Hvalid_ret :
    ValidNodeFields ps_2 n_pre L_pre R_pre retval retval_2 retval_3 retval_4 retval_5).
  {
    rewrite PreH10, PreH7, PreH4, PreH1, PreH13.
    exact Htop_valid.
  }
  pose proof Hvalid_ret as Hvalid_ret'.
  unfold ValidNodeFields in Hvalid_ret'; rewrite ValidNode_unfold in Hvalid_ret'; cbn in Hvalid_ret'.
  destruct Hvalid_ret' as
    [_ [Hret_start1 [Hret_startn [Hret_startlo [_ [Hret_hi [Hret_lo_best [Hret_best_hi _]]]]]]]].
  assert (Hret_hi_n : retval_4 <= n_pre) by
    (eapply Z.le_trans; [exact Hret_hi | apply Z.le_min_l]).
  Exists chosen_2; Exists vals_2; Exists starts_2; Exists los_2; Exists his_2.
  Exists bests_2; Exists ans_2; Exists st_slots_2; Exists ps_2; Exists slots_2.
  split_pure_spatial.
  - piano_cancel.
  - piano_split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_superPiano_entail_wit_5 : superPiano_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat match goal with H : ?r = Znth _ _ _ |- _ => is_var r; subst r end.
  try piano_input_bounds.
  piano_normalize_nodes.
  Exists chosen_2 vals_out starts_out los_out his_out bests_out slots_out ans_2 query_st_slots query_ps.
  split_pure_spatial.
  - piano_cancel.
  - piano_split_pures.
    all: try (dump_pre_spatial; try assumption; try (timeout 2 lia)).
    all: try (eapply frontier_pop_to_split_both_children; eauto; lia).
    all: try (eapply valid_node_fields_left_child; eauto; lia).
    all: try (eapply valid_node_fields_right_child; eauto; lia).
Qed.

Lemma proof_of_superPiano_entail_wit_6 : superPiano_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat match goal with H : ?r = Znth _ _ _ |- _ => is_var r; subst r end.
  try piano_input_bounds.
  piano_normalize_nodes.
  Exists chosen_2 vals_out starts_out los_out his_out bests_out slots_out ans_2 query_st_slots query_ps.
  split_pure_spatial.
  - piano_cancel.
  - piano_split_pures.
    all: try (dump_pre_spatial; try assumption; try (timeout 2 lia)).
    all: try (eapply frontier_pop_to_split_left_only; eauto; lia).
    all: try (eapply valid_node_fields_left_child; eauto; lia).
    all: try (eapply valid_node_fields_right_child; eauto; lia).
Qed.

Lemma proof_of_superPiano_entail_wit_7 : superPiano_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  try piano_input_bounds.
  piano_normalize_nodes.
  Exists chosen_2; Exists vals_out; Exists starts_out; Exists los_out; Exists his_out.
  Exists bests_out; Exists slots_out; Exists ans_2; Exists query_st_slots; Exists query_ps.
  split_pure_spatial.
  - piano_cancel.
  - piano_split_pures.
    all: try (dump_pre_spatial; try assumption; try (timeout 2 lia)).
    all: try (eapply frontier_pop_to_split_singleton; eauto; lia).
Qed.

Lemma proof_of_superPiano_entail_wit_11 : superPiano_entail_wit_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  try piano_input_bounds.
  piano_normalize_nodes.
  Exists chosen_2; Exists vals_out; Exists starts_out; Exists los_out; Exists his_out.
  Exists bests_out; Exists slots_out; Exists ans_2; Exists st_slots_2; Exists push_ps.
  split_pure_spatial.
  - piano_cancel.
  - piano_split_pures.
    all: dump_pre_spatial; try assumption; try (timeout 2 lia).
    + match goal with
      | Hpush : FrontierPushFields _ _ _ _ _ _ _ _ |- _ =>
          unfold FrontierPushFields in Hpush;
          eapply frontier_split_push_left_keeps_right_pending; eauto
      end.
Qed.

Lemma proof_of_superPiano_entail_wit_12 : superPiano_entail_wit_12.
Proof.
  LLM_pre_process ltac:(int_auto).
  repeat match goal with H : ?r = Znth _ _ _ |- _ => is_var r; subst r end.
  try piano_input_bounds.
  piano_normalize_nodes.
  Exists chosen_2 vals_out starts_out los_out his_out bests_out slots_out ans_2 query_st_slots query_ps.
  split_pure_spatial.
  - piano_cancel.
  - piano_split_pures.
    all: try (dump_pre_spatial; try assumption; try (timeout 2 lia)).
    all: try (eapply frontier_pop_to_split_right_only; eauto; lia).
    all: try (eapply valid_node_fields_left_child; eauto; lia).
    all: try (eapply valid_node_fields_right_child; eauto; lia).
Qed.

Lemma proof_of_superPiano_entail_wit_13_1 : superPiano_entail_wit_13_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  try piano_input_bounds.
  piano_normalize_nodes.
  pose proof PreH26 as Hsplit_copy.
  assert (Hright_int : -2147483648 <= right_value <= 2147483647).
  {
    eapply (ValidNodeFields_value_int_bound l right_ps n_pre L_pre R_pre
      right_value start (best + 1) hi right_best); eauto; lia.
  }
  assert (Hleft_int : -2147483648 <= left_value <= 2147483647).
  {
    eapply (ValidNodeFields_value_int_bound l right_ps n_pre L_pre R_pre
      left_value start lo (best - 1) left_best); eauto; lia.
  }
  pose proof PreH51 as Hleft_fields.
  unfold ValidNodeFields in Hleft_fields; rewrite ValidNode_unfold in Hleft_fields; cbn in Hleft_fields.
  destruct Hleft_fields as [_ [_ [_ [Hleft_startlo _]]]].
  pose proof PreH52 as Hvalid.
  unfold ValidNodeFields in Hvalid; rewrite ValidNode_unfold in Hvalid; cbn in Hvalid.
  destruct Hvalid as [_ [_ [_ [Hstartlo [_ [Hhimin _]]]]]].
  Exists chosen_2; Exists vals_out; Exists starts_out; Exists los_out; Exists his_out.
  Exists bests_out; Exists slots_out; Exists ans_2; Exists st_slots_2; Exists right_ps.
  split_pure_spatial.
  - piano_cancel.
  - piano_split_pures.
    all: dump_pre_spatial; try assumption; try (timeout 2 lia).
    + unfold FrontierPushFields in PreH4.
      eapply (frontier_split_push_single_pending_forms_frontier
        right_ps n_pre L_pre R_pre
        (ChordCode n_pre start best :: chosen_2)
        (t + 1) total right_slots hsize
        (mkNode right_value start (best + 1) hi right_best)
        slots_out).
      * exact PreH4.
      * exact Hsplit_copy.
Qed.

Lemma proof_of_superPiano_entail_wit_13_2 : superPiano_entail_wit_13_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  try piano_input_bounds.
  piano_normalize_nodes.
  assert (Hleft_int : -2147483648 <= left_value <= 2147483647).
  {
    rewrite PreH21; lia.
  }
  assert (Hright_int : -2147483648 <= right_value <= 2147483647).
  {
    eapply (ValidNodeFields_value_int_bound l right_ps n_pre L_pre R_pre
      right_value start (best + 1) hi right_best); eauto; lia.
  }
  assert (Hstart_lo : start + L_pre - 1 <= lo).
  {
    unfold ValidNodeFields in PreH45; rewrite ValidNode_unfold in PreH45; cbn in PreH45.
    lia.
  }
  pose proof PreH45 as Hvalid_fields.
  unfold ValidNodeFields in Hvalid_fields; rewrite ValidNode_unfold in Hvalid_fields; cbn in Hvalid_fields.
  destruct Hvalid_fields as
    [Hps_len [Hstart_ge [Hstart_le [Hstart_lo_field [Hlo_hi [Hhi_min
      [Hlo_best [Hbest_hi [Hvalue_field Hmax_field]]]]]]]]].
  Exists chosen_2; Exists vals_out; Exists starts_out; Exists los_out; Exists his_out.
  Exists bests_out; Exists slots_out; Exists ans_2; Exists st_slots_2; Exists right_ps.
  split_pure_spatial.
  - piano_cancel.
  - piano_split_pures.
    all: dump_pre_spatial; try assumption; try (timeout 2 lia).
    + unfold FrontierPushFields in PreH4.
      eapply (frontier_split_push_single_pending_forms_frontier
        right_ps n_pre L_pre R_pre
        (ChordCode n_pre start best :: chosen_2)
        (t + 1) total right_slots hsize
        (mkNode right_value start (best + 1) hi right_best)
        slots_out).
      * exact PreH4.
      * exact PreH28.
Qed.

Lemma proof_of_superPiano_entail_wit_13_3 : superPiano_entail_wit_13_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  try piano_input_bounds.
  piano_normalize_nodes.
  assert (Hright_int : -2147483648 <= right_value <= 2147483647).
  {
    rewrite PreH20; lia.
  }
  assert (Hleft_int : -2147483648 <= left_value <= 2147483647).
  {
    rewrite PreH18; lia.
  }
  assert (Hstart_lo : start + L_pre - 1 <= lo).
  {
    unfold ValidNodeFields in PreH34; rewrite ValidNode_unfold in PreH34; cbn in PreH34.
    lia.
  }
  pose proof PreH34 as Hvalid_fields.
  unfold ValidNodeFields in Hvalid_fields; rewrite ValidNode_unfold in Hvalid_fields; cbn in Hvalid_fields.
  destruct Hvalid_fields as
    [Hps_len [Hstart_ge [Hstart_le [Hstart_lo_field [Hlo_hi [Hhi_min
      [Hlo_best [Hbest_hi [Hvalue_field Hmax_field]]]]]]]]].
  Exists chosen_2; Exists vals_2; Exists starts_2; Exists los_2; Exists his_2.
  Exists bests_2; Exists slots_2; Exists ans_2; Exists st_slots_2; Exists ps_2.
  split_pure_spatial.
  - piano_cancel.
  - piano_split_pures.
    all: dump_pre_spatial; try assumption; try (timeout 2 lia).
Qed.

Lemma proof_of_superPiano_entail_wit_13_4 : superPiano_entail_wit_13_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  try piano_input_bounds.
  piano_normalize_nodes.
  assert (Hright_int : -2147483648 <= right_value <= 2147483647).
  {
    rewrite PreH46; lia.
  }
  assert (Hleft_int : -2147483648 <= left_value <= 2147483647).
  {
    eapply (ValidNodeFields_value_int_bound l push_ps n_pre L_pre R_pre
      left_value start lo (best - 1) left_best); eauto; lia.
  }
  assert (Hstart_lo : start + L_pre - 1 <= lo).
  {
    unfold ValidNodeFields in PreH47; rewrite ValidNode_unfold in PreH47; cbn in PreH47.
    lia.
  }
  pose proof PreH47 as Hvalid_fields.
  unfold ValidNodeFields in Hvalid_fields; rewrite ValidNode_unfold in Hvalid_fields; cbn in Hvalid_fields.
  destruct Hvalid_fields as
    [Hps_len [Hstart_ge [Hstart_le [Hstart_lo_field [Hlo_hi [Hhi_min
      [Hlo_best [Hbest_hi [Hvalue_field Hmax_field]]]]]]]]].
  Exists chosen_2; Exists vals_out; Exists starts_out; Exists los_out; Exists his_out.
  Exists bests_out; Exists slots_out; Exists ans_2; Exists st_slots_2; Exists push_ps.
  split_pure_spatial.
  - piano_cancel.
  - piano_split_pures.
    all: dump_pre_spatial; try assumption; try (timeout 2 lia).
    + unfold FrontierPushFields in PreH5.
      eapply (frontier_split_push_single_pending_forms_frontier
        push_ps n_pre L_pre R_pre
        (ChordCode n_pre start best :: chosen_2)
        (t + 1) total push_slots hsize
        (mkNode left_value start lo (best - 1) left_best)
        slots_out).
      * exact PreH5.
      * exact PreH27.
Qed.

Lemma proof_of_superPiano_entail_wit_14 : superPiano_entail_wit_14.
Proof.
  LLM_pre_process ltac:(int_auto).
  try piano_input_bounds.
  piano_normalize_nodes.
  Exists (ChordCode n_pre start best :: chosen_2).
  Exists vals_2; Exists starts_2; Exists los_2; Exists his_2; Exists bests_2.
  Exists slots_2; Exists ans_2; Exists st_slots_2; Exists ps_2.
  split_pure_spatial.
  - piano_cancel.
  - piano_split_pures.
    all: dump_pre_spatial; try assumption; try (timeout 2 lia).
    + intros Hmore.
      assert (Hcap : hsize <= Zlength slots_2).
      { rewrite PreH13; lia. }
      exact (frontier_state_nonempty_if_more_choices_remain
        ps_2 n_pre L_pre R_pre k_pre ans_2
        (ChordCode n_pre start best :: chosen_2) (t + 1) total slots_2 hsize
        PreH12 PreH32 PreH29 Hcap Hmore).
Qed.

Lemma proof_of_superPiano_entail_wit_15 : superPiano_entail_wit_15.
Proof.
  left. intros. Exists ps_2. split_pure_spatial.
  - assert (Hprefix_bound : 0 <= n_pre + 1 <= 100001) by lia.
    assert (Hsparse_bound : 0 <= (n_pre + 1) * 17 <= 1700017) by lia.
    assert (Hheap_bound : 0 <= n_pre + k_pre + 1 <= 200000) by lia.
    remember 100001 as prefix_capacity eqn:Hprefix_capacity in *.
    remember 1700017 as sparse_capacity eqn:Hsparse_capacity in *.
    remember 200000 as heap_capacity eqn:Hheap_capacity in *.
    clear Hprefix_capacity Hsparse_capacity Hheap_capacity.
    simpl. rewrite !Z.add_0_r.
    sep_apply_l_atomic (IntArray.full_to_undef_full (&( "prefix" )) (n_pre+1) ps_2).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&( "prefix" )) (n_pre+1)).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&( "prefix" )) 0 (n_pre+1) prefix_capacity ltac:(lia)).
    sep_apply_l_atomic (IntArray.full_to_undef_full (&( "st" )) ((n_pre+1)*17) st_slots).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&( "st" )) ((n_pre+1)*17)).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&( "st" )) 0 ((n_pre+1)*17) sparse_capacity ltac:(lia)).
    sep_apply_l_atomic (IntArray.full_to_undef_full (&( "heap_value" )) heap_cap vals).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&( "heap_value" )) heap_cap).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&( "heap_value" )) 0 heap_cap heap_capacity ltac:(lia)).
    sep_apply_l_atomic (IntArray.full_to_undef_full (&( "heap_start" )) heap_cap starts).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&( "heap_start" )) heap_cap).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&( "heap_start" )) 0 heap_cap heap_capacity ltac:(lia)).
    sep_apply_l_atomic (IntArray.full_to_undef_full (&( "heap_lo" )) heap_cap los).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&( "heap_lo" )) heap_cap).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&( "heap_lo" )) 0 heap_cap heap_capacity ltac:(lia)).
    sep_apply_l_atomic (IntArray.full_to_undef_full (&( "heap_hi" )) heap_cap his).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&( "heap_hi" )) heap_cap).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&( "heap_hi" )) 0 heap_cap heap_capacity ltac:(lia)).
    sep_apply_l_atomic (IntArray.full_to_undef_full (&( "heap_best" )) heap_cap bests).
    sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&( "heap_best" )) heap_cap).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&( "heap_best" )) 0 heap_cap heap_capacity ltac:(lia)).
    simpl. rewrite !Z.add_0_r, !Z.sub_0_r. piano_cancel.
  - piano_split_pures; dump_pre_spatial; try assumption; try lia.
    assert (t = k_pre) by lia. subst t.
    eapply frontier_state_complete_implies_answer. eassumption.
Qed.

Lemma proof_of_superPiano_return_wit_1 : superPiano_return_wit_1.
Proof. right. intros. Exists ps_2. entailer!. Qed.

Lemma proof_of_superPiano_partial_solve_wit_1_pure : superPiano_partial_solve_wit_1_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  try piano_input_bounds.
  piano_normalize_nodes.
  Exists ps_2.
  piano_split_pures.
  all: dump_pre_spatial; try assumption; try (timeout 2 lia).
Qed.

Lemma proof_of_superPiano_partial_solve_wit_3_pure : superPiano_partial_solve_wit_3_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes.
  match goal with H : PrefixSums l ?ps |- _ =>
    pose proof (piano_prefix_bounds l ps n_pre ltac:(eassumption) ltac:(eassumption)
      ltac:(lia) ltac:(eassumption) ltac:(eassumption)) as [Hpslo Hpshi];
    pose proof (proj1 H) as Hpslen
  end.
  piano_split_pures; dump_pre_spatial; try assumption; try congruence;
    try (solve [etransitivity; eassumption]); lia.
Qed.

Lemma proof_of_superPiano_partial_solve_wit_4_pure : superPiano_partial_solve_wit_4_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes.
  try match goal with H : ?done < ?limit -> 0 < ?size |- _ =>
    assert (Hnonempty : 0 < size) by (apply H; lia) end.
  piano_split_pures; dump_pre_spatial; try assumption; try congruence; try (solve [etransitivity; eassumption]); lia.
Qed.

Lemma proof_of_superPiano_partial_solve_wit_5_pure : superPiano_partial_solve_wit_5_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes.
  try match goal with H : ?done < ?limit -> 0 < ?size |- _ =>
    assert (Hnonempty : 0 < size) by (apply H; lia) end.
  piano_split_pures; dump_pre_spatial; try assumption; try congruence; try (solve [etransitivity; eassumption]); lia.
Qed.

Lemma proof_of_superPiano_partial_solve_wit_6_pure : superPiano_partial_solve_wit_6_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes.
  try match goal with H : ?done < ?limit -> 0 < ?size |- _ =>
    assert (Hnonempty : 0 < size) by (apply H; lia) end.
  piano_split_pures; dump_pre_spatial; try assumption; try congruence; try (solve [etransitivity; eassumption]); lia.
Qed.

Lemma proof_of_superPiano_partial_solve_wit_7_pure : superPiano_partial_solve_wit_7_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes.
  try match goal with H : ?done < ?limit -> 0 < ?size |- _ =>
    assert (Hnonempty : 0 < size) by (apply H; lia) end.
  piano_split_pures; dump_pre_spatial; try assumption; try congruence; try (solve [etransitivity; eassumption]); lia.
Qed.

Lemma proof_of_superPiano_partial_solve_wit_8_pure : superPiano_partial_solve_wit_8_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes.
  try match goal with H : ?done < ?limit -> 0 < ?size |- _ =>
    assert (Hnonempty : 0 < size) by (apply H; lia) end.
  piano_split_pures; dump_pre_spatial; try assumption; try congruence; try (solve [etransitivity; eassumption]); lia.
Qed.

Lemma proof_of_superPiano_partial_solve_wit_9_pure : superPiano_partial_solve_wit_9_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes.
  try match goal with H : ?done < ?limit -> 0 < ?size |- _ =>
    assert (Hnonempty : 0 < size) by (apply H; lia) end.
  piano_split_pures; dump_pre_spatial; try assumption; try congruence; try (solve [etransitivity; eassumption]); lia.
Qed.

Lemma proof_of_superPiano_partial_solve_wit_19_pure : superPiano_partial_solve_wit_19_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes.
  try match goal with H : ?done < ?limit -> 0 < ?size |- _ =>
    assert (Hnonempty : 0 < size) by (apply H; lia) end.
  piano_split_pures; dump_pre_spatial; try assumption; try congruence; try (solve [etransitivity; eassumption]); lia.
Qed.

Lemma proof_of_superPiano_partial_solve_wit_20_pure : superPiano_partial_solve_wit_20_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes.
  try match goal with H : ?done < ?limit -> 0 < ?size |- _ =>
    assert (Hnonempty : 0 < size) by (apply H; lia) end.
  piano_split_pures; dump_pre_spatial; try assumption; try congruence; try (solve [etransitivity; eassumption]); lia.
Qed.

Lemma proof_of_superPiano_partial_solve_wit_21_pure : superPiano_partial_solve_wit_21_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes.
  try match goal with H : ?done < ?limit -> 0 < ?size |- _ =>
    assert (Hnonempty : 0 < size) by (apply H; lia) end.
  piano_split_pures; dump_pre_spatial; try assumption; try congruence; try (solve [etransitivity; eassumption]); lia.
Qed.

Lemma proof_of_superPiano_partial_solve_wit_22_pure : superPiano_partial_solve_wit_22_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  piano_normalize_nodes.
  try match goal with H : ?done < ?limit -> 0 < ?size |- _ =>
    assert (Hnonempty : 0 < size) by (apply H; lia) end.
  piano_split_pures; dump_pre_spatial; try assumption; try congruence; try (solve [etransitivity; eassumption]); lia.
Qed.
