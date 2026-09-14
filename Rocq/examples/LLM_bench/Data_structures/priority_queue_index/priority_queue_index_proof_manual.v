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
From SimpleC.EE.LLM_bench.Data_structures.priority_queue_index Require Import priority_queue_index_goal.
From SimpleC.EE.LLM_bench.Data_structures.priority_queue_index Require Import priority_queue_index_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue_index.priority_queue_index_lib.
Local Open Scope sac.

Local Ltac finish_entail :=
  split_pure_spatial;
  [ repeat cancel
  | split_pures;
    dump_pre_spatial;
    try lia;
    try int_auto;
    try assumption;
    try reflexivity ].

Lemma proof_of_push_entail_wit_1 : push_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_heap.
  Intros key_base.
  Intros data_base.
  unfold heap_tail.
  destruct (Z_lt_dec n_pre heap_capacity) as [_ | Hnot].
  2:{ lia. }
  unfold heap_spare.
  Exists key_base data_base.
  finish_entail.
Qed.

Lemma proof_of_push_entail_wit_2 : push_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists key_base_2 data_base_2 (key_base_2 ++ (key_x_pre :: nil)).
  finish_entail.
  unfold KeyWriteState.
  split; [exact PreH3 | reflexivity].
Qed.

Lemma proof_of_push_entail_wit_3_split_goal_1 :
  push_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold KeyWriteState in PreH3.
  destruct PreH3 as [Hrep Hkey_written].
  subst key_written_2.
  eapply
    (push_appended_loop_state__push_initialization
      S_before key_base data_base n_pre data_x_pre key_x_pre).
  exact Hrep.
Qed.

Lemma proof_of_push_entail_wit_3_split_goal_2 :
  push_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold KeyWriteState in PreH3.
  destruct PreH3 as [Hrep Hkey_written].
  subst key_written_2.
  eapply
    (push_appended_source__push_initialization
      S_before key_base data_base n_pre data_x_pre key_x_pre).
  exact Hrep.
Qed.

Lemma proof_of_push_entail_wit_3 : push_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_push_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_push_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_push_entail_wit_4 : push_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists key_written_2 data_written_2 key_written_2 data_written_2.
  finish_entail.
Qed.

Lemma proof_of_push_entail_wit_5 : push_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (heap_parent_positive_bounds__push_sift_up
      child n_pre ltac:(lia) ltac:(lia))
    as [Hparent_nonnegative [Hparent_lt Hparent_bound]].
  Exists key_current_2 data_current_2 key_written_2 data_written_2.
  finish_entail;
  unfold heap_parent in
    Hparent_nonnegative, Hparent_lt, Hparent_bound;
  auto.
Qed.

Lemma proof_of_push_entail_wit_6_split_goal_1 :
  push_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  eapply push_break_establishes_result__push_sift_up; eauto.
Qed.

Lemma proof_of_push_entail_wit_6 : push_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_push_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_push_entail_wit_7 : push_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (push_swap_advances_loop__push_sift_up
      key_written_2 data_written_2 key_current data_current
      n_pre child parent data_x_pre key_x_pre
      PreH11 PreH4 PreH9 PreH1)
    as (Hkey_child & Hdata_child & Hloop).
  Exists key_written_2 data_written_2
    (replace_Znth child (Znth parent data_current 0)
      (replace_Znth parent (Znth child data_current 0) data_current))
    (replace_Znth child (Znth parent key_current 0)
      (replace_Znth parent (Znth child key_current 0) key_current)).
  finish_entail.
Qed.

Lemma proof_of_push_entail_wit_8 : push_entail_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists key_current_2 data_current_2 key_written_2 data_written_2.
  finish_entail.
Qed.

Lemma proof_of_push_entail_wit_9_1_split_goal_1 :
  push_entail_wit_9_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hchild_zero : child = 0) by lia.
  subst child.
  eapply push_zero_exit_result__push_finalization; eauto.
Qed.

Lemma proof_of_push_entail_wit_9_1 : push_entail_wit_9_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_push_entail_wit_9_1_split_goal_1.
Qed.

Lemma proof_of_push_entail_wit_10_split_goal_spatial :
  push_entail_wit_10_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (push_result_representation__push_finalization
      S_before key_result data_result n_pre data_x_pre key_x_pre
      PreH2 PreH6) as Hrepresentation.
  unfold store_heap.
  Exists key_result data_result.
  sep_apply_l_atomic
    (undef_seg_to_heap_tail key_pre (n_pre + 1) ltac:(lia)).
  sep_apply_l_atomic
    (undef_seg_to_heap_tail data_pre (n_pre + 1) ltac:(lia)).
  finish_entail.
Qed.

Lemma proof_of_push_entail_wit_10 : push_entail_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_push_entail_wit_10_split_goal_spatial.
Qed.

Lemma proof_of_build_entail_wit_1 : build_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct (Z.eq_dec n_pre 0) as [Hzero | Hpositive].
  - subst n_pre.
    Left.
    finish_entail.
  - Right.
    assert (Hone : 1 <= n_pre) by lia.
    pose proof
      (build_initial_prefix__build_progress
        key_input data_input n_pre PreH3 PreH4 Hone)
      as [Hprefix Hrepresentation].
    sep_apply
      (IntArray.full_split_to_seg
        key_pre 1 n_pre key_input);
      try lia.
    sep_apply
      (IntArray.full_split_to_seg
        data_pre 1 n_pre data_input);
      try lia.
    Exists
      (sublist 0 1 key_input)
      (sublist 0 1 data_input)
      (list_to_multiset
        (heap_item (Znth 0 key_input 0) (Znth 0 data_input 0) :: nil)).
    sep_apply
      (IntArray.seg_to_full
        key_pre 0 1 (sublist 0 1 key_input)).
    sep_apply
      (IntArray.seg_to_full
        data_pre 0 1 (sublist 0 1 data_input)).
    finish_entail.
    all:
      try (replace (key_pre + 0 * sizeof(INT)) with key_pre by lia);
      try (replace (data_pre + 0 * sizeof(INT)) with data_pre by lia);
      try (replace (1 - 0) with 1 by lia);
      cancel.
Qed.

Lemma proof_of_build_entail_wit_2 : build_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hdata_x :
    Znth (i - i) (sublist i n_pre data_input) 0 =
    Znth i data_input 0).
  {
    rewrite Znth_sublist by lia.
    f_equal; lia.
  }
  assert (Hkey_x :
    Znth (i - i) (sublist i n_pre key_input) 0 =
    Znth i key_input 0).
  {
    rewrite Znth_sublist by lia.
    f_equal; lia.
  }
  rewrite Hdata_x, Hkey_x.
  pose proof PreH9 as Hrep_lengths.
  destruct Hrep_lengths as
    [_ [_ [_ [Hkey_prefix_len [Hdata_prefix_len _]]]]].
  Exists
    (key_prefix ++ (Znth i key_input 0 :: nil))
    (data_prefix ++ (Znth i data_input 0 :: nil))
    key_prefix data_prefix S_prefix_2.
  sep_apply
    (build_append_next_cell__build_progress
      key_pre i n_pre key_prefix key_input);
    try lia.
  sep_apply
    (build_append_next_cell__build_progress
      data_pre i n_pre data_prefix data_input);
    try lia.
  finish_entail;
    try (eapply push_appended_source__push_initialization; eauto);
    try (eapply push_appended_loop_state__push_initialization; eauto).
Qed.

Lemma proof_of_build_entail_wit_3 : build_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists key_written_2 data_written_2
    key_written_2 data_written_2 S_prefix_2.
  finish_entail.
Qed.

Lemma proof_of_build_entail_wit_4 : build_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (heap_parent_positive_bounds__push_sift_up
      child i ltac:(lia) ltac:(lia))
    as [Hparent_nonnegative [Hparent_lt Hparent_bound]].
  Exists key_current_2 data_current_2
    key_written_2 data_written_2 S_prefix_2.
  finish_entail;
  unfold heap_parent in
    Hparent_nonnegative, Hparent_lt, Hparent_bound;
  auto.
Qed.

Lemma proof_of_build_entail_wit_5 : build_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists data_current_2 key_written_2
    data_written_2 S_prefix_2 key_current_2.
  finish_entail;
    try (eapply push_break_establishes_result__push_sift_up; eauto).
Qed.

Lemma proof_of_build_entail_wit_6 : build_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (push_swap_advances_loop__push_sift_up
      key_written_2 data_written_2 key_current data_current
      i child parent data_x key_x
      PreH18 PreH8 PreH13 PreH1)
    as (Hkey_child & Hdata_child & Hloop).
  Exists key_written_2 data_written_2 S_prefix_2
    (replace_Znth child (Znth parent data_current 0)
      (replace_Znth parent (Znth child data_current 0) data_current))
    (replace_Znth child (Znth parent key_current 0)
      (replace_Znth parent (Znth child key_current 0) key_current)).
  finish_entail.
Qed.

Lemma proof_of_build_entail_wit_7 : build_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists key_current_2 data_current_2
    key_written_2 data_written_2 S_prefix_2.
  finish_entail.
Qed.

Lemma proof_of_build_entail_wit_8_1 : build_entail_wit_8_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hchild_zero : child = 0) by lia.
  subst child.
  pose proof
    (push_zero_exit_result__push_finalization
      S_prefix_2 key_written_2 data_written_2
      key_current data_current i data_x key_x
      PreH13 PreH14)
    as Hresult.
  Exists key_current data_current
    key_written_2 data_written_2 S_prefix_2.
  finish_entail.
Qed.

Lemma proof_of_build_entail_wit_8_2 : build_entail_wit_8_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists key_current data_current
    key_written_2 data_written_2 S_prefix_2.
  finish_entail.
Qed.

Lemma proof_of_build_entail_wit_9 : build_entail_wit_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (push_result_representation__push_finalization
      S_prefix_2 key_result_2 data_result_2
      i data_x key_x ltac:(lia) PreH11)
    as Hrepresentation.
  Exists key_result_2 data_result_2 S_prefix_2.
  finish_entail.
  eapply build_prefix_extend__build_progress; eauto; lia.
Qed.

Lemma proof_of_build_entail_wit_10 : build_entail_wit_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists key_result data_result
    (multiset_insert S_prefix_2 (heap_item key_x data_x)).
  finish_entail.
Qed.

Lemma priority_queue_index_undef_pair_to_heap_tail_zero :
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

Lemma proof_of_build_entail_wit_11_1_split_goal_spatial :
  build_entail_wit_11_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst n_pre.
  apply Zlength_nil_inv in PreH4.
  apply Zlength_nil_inv in PreH5.
  subst key_input data_input.
  rewrite (IntArray.full_empty key_pre 0).
  rewrite (IntArray.full_empty data_pre 0).
  Intros.
  Intros.
  unfold store_heap.
  Exists (@nil Z) (@nil Z).
  rewrite (IntArray.full_empty key_pre 0).
  rewrite (IntArray.full_empty data_pre 0).
  eapply derivable1_trans with
    (y := heap_tail key_pre 0 ** heap_tail data_pre 0).
  - apply priority_queue_index_undef_pair_to_heap_tail_zero.
  - finish_entail.
    unfold heap_representation, heap_relation, heap_ordered,
      multiset_size, list_to_multiset, heap_capacity.
    simpl.
    repeat split; try lia.
    apply Permutation_refl.
Qed.

Lemma proof_of_build_entail_wit_11_1 : build_entail_wit_11_1.
Proof.
  left.
  Goal_apply proof_of_build_entail_wit_11_1_split_goal_spatial.
Qed.

Lemma proof_of_build_entail_wit_11_2_split_goal_spatial :
  build_entail_wit_11_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  assert (Hequiv :
    multiset_equiv S_prefix
      (list_to_multiset (pair_list key_input data_input))).
  {
    eapply build_prefix_complete__build_finalization.
    - exact PreH8.
    - lia.
    - lia.
  }
  pose proof
    (store_heap_equiv_transport__build_finalization
      S_prefix (list_to_multiset (pair_list key_input data_input))
      key_prefix data_prefix n_pre Hequiv PreH9)
    as Hrep_target.
  sep_apply
    (concrete_arrays_to_store_heap__build_finalization
      key_pre data_pre (list_to_multiset (pair_list key_input data_input))
      key_prefix data_prefix n_pre ltac:(lia) Hrep_target).
  entailer!.
Qed.

Lemma proof_of_build_entail_wit_11_2 : build_entail_wit_11_2.
Proof.
  right.
  Goal_apply proof_of_build_entail_wit_11_2_split_goal_spatial.
Qed.

Lemma proof_of_pop_entail_wit_1 : pop_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_heap.
  Intros before_key.
  Intros before_data.
  pose proof H as Hrep_bounds.
  destruct Hrep_bounds as [Hsize_nonnegative [Hcapacity_bound _]].
  assert (Hbounds : 0 <= n_pre <= heap_capacity) by lia.
  sep_apply_l_atomic
    (heap_tail_to_undef_seg key_pre n_pre Hbounds).
  sep_apply_l_atomic
    (heap_tail_to_undef_seg data_pre n_pre Hbounds).
  pose proof
    (heap_root_is_multiset_minimum__pop_initialization
      S_before before_key before_data n_pre PreH1 H)
    as [Hprefix Hminimum].
  pose proof H as Hrepresentation.
  destruct Hrepresentation as [_ [Hcapacity _]].
  Exists
    (heap_item
      (Znth 0 before_key 0) (Znth 0 before_data 0))
    before_key before_data.
  finish_entail.
Qed.

Lemma proof_of_pop_entail_wit_2 : pop_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists before_key before_data popped_2.
  finish_entail.
  all:
    unfold PrefixMinimum in PreH4;
    destruct PreH4 as (_ & _ & _ & Hroot & _);
    rewrite Hroot;
    reflexivity.
Qed.

Lemma proof_of_pop_entail_wit_3 : pop_entail_wit_3.
Proof.
  right.
  LLM_pre_process ltac:(int_auto).
  subst n_pre.
  Exists popped_2.
  eapply derivable1_trans with
    (y := IntArray.full key_pre 1 before_key **
      IntArray.undef_seg key_pre 1 heap_capacity **
      IntArray.full data_pre 1 before_data **
      IntArray.undef_seg data_pre 1 heap_capacity).
  - repeat cancel.
  - eapply derivable1_trans with
      (y := store_heap key_pre data_pre
        (multiset_remove S_before popped_2) 0).
    + apply singleton_store_heap_after_remove__pop_singleton;
        assumption.
    + finish_entail.
Qed.

Lemma proof_of_pop_entail_wit_4 : pop_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists before_key_2 before_data_2 popped_2.
  finish_entail.
  unfold heap_capacity in *.
  lia.
Qed.

Lemma proof_of_pop_entail_wit_5 : pop_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH8 as Hrepresentation.
  destruct Hrepresentation as
    (_ & _ & _ & Hkey_length & Hdata_length &
     _ & Hordered).
  pose proof
    (pop_root_replacement_loop_state__pop_initialization
      before_key_2 before_data_2 n_pre
      PreH3 Hkey_length Hdata_length Hordered)
    as Hloop.
  Exists
    (replace_Znth 0
      (Znth (n_pre - 1) before_key_2 0) before_key_2)
    (replace_Znth 0
      (Znth (n_pre - 1) before_data_2 0) before_data_2)
    before_key_2 before_data_2 popped_2.
  finish_entail.
Qed.

Lemma proof_of_pop_entail_wit_6 : pop_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_key_2 current_data_2
    before_key_2 before_data_2 popped_2.
  finish_entail.
Qed.

Lemma proof_of_pop_entail_wit_7 : pop_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_key_2 current_data_2
    before_key_2 before_data_2 popped_2.
  finish_entail.
Qed.

Lemma proof_of_pop_entail_wit_8_1 : pop_entail_wit_8_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_data_2 before_key_2 before_data_2
    current_key_2 popped_2.
  subst smallest left right.
  finish_entail.
  replace (idx * 2 + 1 + 1) with (heap_right_child idx)
    by (unfold heap_right_child; lia).
  apply pop_select_right__pop_child_selection.
  - exact PreH7.
  - unfold heap_right_child. lia.
  - unfold heap_left_child, heap_right_child.
    replace (idx * 2 + 2) with (idx * 2 + 1 + 1) by lia.
    exact PreH1.
Qed.

Lemma proof_of_pop_entail_wit_8_2 : pop_entail_wit_8_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_data_2 before_key_2 before_data_2
    current_key_2 popped_2.
  subst smallest left right.
  finish_entail.
  apply pop_select_left__pop_child_selection.
  - exact PreH6.
  - unfold heap_left_child. lia.
  - left. unfold heap_right_child. lia.
Qed.

Lemma proof_of_pop_entail_wit_8_3 : pop_entail_wit_8_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_data_2 before_key_2 before_data_2
    current_key_2 popped_2.
  subst smallest left right.
  finish_entail.
  apply pop_select_left__pop_child_selection.
  - exact PreH7.
  - unfold heap_left_child. lia.
  - right.
    unfold heap_left_child, heap_right_child.
    replace (idx * 2 + 2) with (idx * 2 + 1 + 1) by lia.
    lia.
Qed.

Lemma proof_of_pop_entail_wit_9 : pop_entail_wit_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_data_2 before_key_2 before_data_2
    current_key_2 popped_2.
  assert (Hready :
    PopReadyState before_key_2 before_data_2
      current_key_2 current_data_2 n_pre popped_2).
  {
    eapply pop_comparison_ready__pop_ready_exit; eauto.
  }
  pose proof PreH12 as Hselected.
  destruct Hselected as
    (_ & _ & _ & _ & _ & _ & Hselected_choice & _).
  subst left right.
  unfold heap_selected_child in Hselected_choice.
  destruct (Z_lt_dec (heap_right_child idx) (n_pre - 1)).
  - destruct
      (Z.leb
        (Znth (heap_left_child idx) current_key_2 0)
        (Znth (heap_right_child idx) current_key_2 0));
      subst smallest;
      unfold heap_left_child, heap_right_child in *;
      finish_entail.
  - subst smallest.
    unfold heap_left_child, heap_right_child in *.
    finish_entail.
Qed.

Lemma proof_of_pop_entail_wit_10 : pop_entail_wit_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH12 as Hselected.
  unfold PopSelectedChild in Hselected.
  destruct Hselected as
    (Hidx_nonnegative & Hidx_bound & Hidx_selected &
     Hselected_nonnegative & Hselected_bound &
     Hselected_parent & Hselected_choice & Hselected_dominates).
  pose proof
    (pop_next_index_arithmetic__pop_swap_transition
      current_key (n_pre - 1) idx smallest
      PreH6 PreH11 Hselected_choice)
    as (Hleft_nonnegative & Hleft_bound &
        Hright_nonnegative & Hright_bound).
  unfold heap_left_child in
    Hleft_nonnegative, Hleft_bound.
  unfold heap_right_child in
    Hright_nonnegative, Hright_bound.
  pose proof
    (pop_swap_advances_loop__pop_swap_transition
      before_key_2 before_data_2 current_key current_data
      n_pre idx smallest PreH16 PreH12 PreH1)
    as (Hkey_read & Hdata_read & Hloop).
  Exists before_key_2 before_data_2
    (replace_Znth smallest (Znth idx current_data 0)
      (replace_Znth idx (Znth smallest current_data 0)
        current_data))
    (replace_Znth smallest (Znth idx current_key 0)
      (replace_Znth idx (Znth smallest current_key 0)
        current_key))
    popped_2.
  finish_entail.
Qed.

Lemma proof_of_pop_entail_wit_11 : pop_entail_wit_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_key_2 current_data_2
    before_key_2 before_data_2 popped_2.
  finish_entail.
  unfold heap_capacity in *.
  lia.
Qed.

Lemma proof_of_pop_entail_wit_12_1 : pop_entail_wit_12_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_key_2 current_data_2
    before_key_2 before_data_2 popped_2.
  finish_entail.
  eapply pop_leaf_ready__pop_ready_exit; eauto.
Qed.

Lemma proof_of_pop_entail_wit_12_2 : pop_entail_wit_12_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_key_2 current_data_2
    before_key_2 before_data_2 popped_2.
  finish_entail.
Qed.

Lemma proof_of_pop_entail_wit_13 : pop_entail_wit_13.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_key current_data before_key_2 before_data_2 popped_2.
  finish_entail.
  eapply pop_ready_write_result__pop_finalization; eauto.
Qed.

Lemma proof_of_pop_entail_wit_14 : pop_entail_wit_14.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_l_atomic
    (pop_result_store_retired_pair__pop_finalization
      key_pre data_pre S_before before_key before_data
      result_key_values result_data_values n_pre popped_2
      PreH4 PreH10).
  Exists popped_2.
  finish_entail.
Qed.

Lemma proof_of_pop_return_wit_2 : pop_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists result_data popped_2 result_key.
  subst n_pre.
  finish_entail.
  replace (1 - 1) with 0 by lia.
  repeat cancel.
Qed.
