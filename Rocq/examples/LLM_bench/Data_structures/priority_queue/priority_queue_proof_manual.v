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
From SimpleC.EE.LLM_bench.Data_structures.priority_queue Require Import priority_queue_goal.
From SimpleC.EE.LLM_bench.Data_structures.priority_queue Require Import priority_queue_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib.
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
  Intros base.
  Exists base.
  finish_entail.
  unfold heap_representation in H.
  tauto.
Qed.

Lemma proof_of_push_entail_wit_2_split_goal_1 :
  push_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  exact
    (push_appended_loop_state__push_initialization
      S_before base n_pre x_pre PreH3).
Qed.

Lemma proof_of_push_entail_wit_2_split_goal_2 :
  push_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  exact
    (push_appended_source__push_initialization
      S_before base n_pre x_pre PreH3).
Qed.

Lemma proof_of_push_entail_wit_2 : push_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_push_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_push_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_push_entail_wit_3 : push_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists written_2 written_2.
  finish_entail.
Qed.

Lemma proof_of_push_entail_wit_4 : push_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (heap_parent_positive_bounds__push_sift_up
      child n_pre ltac:(lia) ltac:(lia))
    as [Hparent_nonnegative [Hparent_lt Hparent_bound]].
  Exists current_2 written_2.
  finish_entail;
  unfold heap_parent in
    Hparent_nonnegative, Hparent_lt, Hparent_bound;
  auto.
Qed.

Lemma proof_of_push_entail_wit_5 : push_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists written_2 current_2.
  finish_entail.
  eapply push_break_establishes_result__push_sift_up; eauto.
Qed.

Lemma proof_of_push_entail_wit_6 : push_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (push_swap_advances_loop__push_sift_up
      written_2 current n_pre child parent x_pre
      PreH11 PreH4 PreH9 PreH1)
    as [Hswapped_value Hswapped_loop].
  Exists written_2
    (replace_Znth child (Znth parent current 0)
      (replace_Znth parent (Znth child current 0) current)).
  finish_entail.
Qed. 

Lemma proof_of_push_entail_wit_7 : push_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst parent.
  Exists current_2 written_2.
  finish_entail.
Qed.

Lemma proof_of_push_entail_wit_8_1 : push_entail_wit_8_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current written_2.
  finish_entail.
  assert (Hchild_zero : child = 0) by lia.
  subst child.
  eapply push_zero_exit_result__push_finalization; eauto.
Qed. 

Lemma proof_of_push_entail_wit_9_split_goal_spatial :
  push_entail_wit_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof
    (push_result_representation__push_finalization
      S_before result n_pre x_pre PreH2 PreH6)
    as Hrepresentation.
  unfold store_heap.
  Exists result.
  finish_entail.
Qed.

Lemma proof_of_push_entail_wit_9 : push_entail_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_push_entail_wit_9_split_goal_spatial.
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
        input n_pre PreH3 Hone)
      as [Hprefix Hrepresentation].
    sep_apply
      (IntArray.full_split_to_seg
        heap_pre 1 n_pre input);
      try lia.
    unfold store_heap.
    Exists (list_to_multiset (Znth 0 input 0 :: nil)).
    Exists (sublist 0 1 input).
    sep_apply
      (IntArray.seg_to_full
        heap_pre 0 1 (sublist 0 1 input)).
    finish_entail.
    replace (heap_pre + 0 * sizeof(INT)) with heap_pre by lia.
    replace (1 - 0) with 1 by lia.
    cancel.
Qed. 

Lemma proof_of_build_entail_wit_2 : build_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists S_prefix_2.
  sep_apply
    (build_split_next_cell__build_progress
      heap_pre i n_pre input);
    try lia.
  finish_entail.
  all: try (rewrite Znth_sublist by lia; f_equal; lia).
  unfold heap_spare.
  cancel.
Qed. 

Lemma proof_of_build_entail_wit_4 : build_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists S_prefix_2.
  finish_entail.
  eapply build_prefix_extend__build_progress; eauto; lia.
Qed. 

Lemma proof_of_build_entail_wit_6_1_split_goal_spatial :
  build_entail_wit_6_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst n_pre.
  apply Zlength_nil_inv in PreH4.
  subst input.
  unfold store_heap.
  Exists (@nil Z).
  finish_entail.
  unfold heap_representation, heap_relation, heap_ordered,
    multiset_size, list_to_multiset, heap_capacity.
  simpl.
  repeat split; try lia.
  apply Permutation_refl.
Qed.

Lemma proof_of_build_entail_wit_6_1 : build_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_build_entail_wit_6_1_split_goal_spatial.
Qed. 

Lemma proof_of_build_entail_wit_6_2_split_goal_spatial :
  build_entail_wit_6_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  unfold store_heap.
  Intros concrete.
  assert (Hequiv :
    multiset_equiv S_prefix (list_to_multiset input)).
  {
    eapply build_prefix_complete__build_finalization.
    - exact PreH7.
    - lia.
  }
  match goal with
  | Hrep : heap_representation S_prefix concrete n_pre |- _ =>
      pose proof
        (store_heap_equiv_transport__build_finalization
          S_prefix (list_to_multiset input) concrete n_pre
          Hequiv Hrep)
        as Hrep_target
  end.
  Exists concrete.
  finish_entail.
Qed.

Lemma proof_of_build_entail_wit_6_2 : build_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_build_entail_wit_6_2_split_goal_spatial.
Qed. 

Lemma proof_of_pop_entail_wit_1 : pop_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_heap.
  Intros before.
  pose proof
    (heap_root_is_multiset_max__pop_initialization
      S_before before n_pre PreH1 H)
    as [Hprefix [Hroot Hmaximum]].
  pose proof H as Hrepresentation.
  destruct Hrepresentation as [_ [Hcapacity _]].
  Exists before.
  finish_entail.
Qed. 

Lemma proof_of_pop_entail_wit_3_split_goal_spatial :
  pop_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hlength : Zlength before = 1).
    {
      destruct PreH6 as
        [_ [_ [_ [Hlength [_ _]]]]].
      lia.
    }
    assert (Hsize : multiset_size S_before = 1).
    {
      destruct PreH6 as
        [_ [_ [Hsize [_ [_ _]]]]].
      lia.
    }
    pose proof
      (remove_max_singleton_empty__pop_singleton S_before Hsize)
      as Hremoved.
    assert (Hremoved_representation :
      heap_representation
        (multiset_remove S_before (multiset_max S_before))
        (@nil Z) 0).
    {
      unfold heap_representation.
      split; [lia|].
      split; [unfold heap_capacity; lia|].
      split.
      - unfold multiset_size.
        rewrite Hremoved.
        reflexivity.
      - split; [reflexivity|].
        split.
        + unfold heap_relation.
          rewrite Hremoved.
          apply Permutation_refl.
        + unfold heap_ordered.
          intros child [Hchild_positive Hchild].
          exfalso.
          exact (Z.lt_asymm 0 child Hchild_positive Hchild).
    }
    subst n_pre.
    sep_apply_l_atomic
      (singleton_full_split_retired__pop_singleton
        heap_pre before ret Hlength (eq_sym PreH4)).
    unfold store_heap.
    Exists (@nil Z).
    finish_entail.
    unfold heap_spare.
    replace (0 + 1) with 1 by lia.
    cancel.
Qed.

Lemma proof_of_pop_entail_wit_3 : pop_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_pop_entail_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_pop_entail_wit_4 : pop_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hgt : 1 < n_pre) by lia.
  pose proof PreH6 as Hrepresentation.
  destruct Hrepresentation as
    [_ [_ [_ [Hlength [_ Hordered]]]]].
  pose proof
    (pop_root_replacement_loop_state__pop_initialization
      before_2 n_pre Hgt Hlength Hordered)
    as Hloop.
  Exists
    (replace_Znth 0 (Znth (n_pre - 1) before_2 0) before_2)
    before_2.
  finish_entail.
Qed. 

Lemma proof_of_pop_entail_wit_5 : pop_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_2 before_2.
  finish_entail.
Qed.

Lemma proof_of_pop_entail_wit_6 : pop_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_2 before_2.
  finish_entail.
Qed.

Lemma proof_of_pop_entail_wit_7_1 : pop_entail_wit_7_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_2 before_2.
  subst largest left right.
  finish_entail.
  replace (idx * 2 + 1 + 1) with (heap_right_child idx)
    by (unfold heap_right_child; lia).
  apply pop_select_right__pop_child_selection.
  - exact PreH10.
  - unfold heap_right_child. lia.
  - unfold heap_left_child, heap_right_child.
    replace (idx * 2 + 2) with (idx * 2 + 1 + 1) by lia.
    exact PreH1.
Qed. 

Lemma proof_of_pop_entail_wit_7_2 : pop_entail_wit_7_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_2 before_2.
  subst largest left right.
  finish_entail.
  apply pop_select_left__pop_child_selection.
  - exact PreH9.
  - unfold heap_left_child. lia.
  - left. unfold heap_right_child. lia.
Qed. 

Lemma proof_of_pop_entail_wit_7_3 : pop_entail_wit_7_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_2 before_2.
  subst largest left right.
  finish_entail.
  apply pop_select_left__pop_child_selection.
  - exact PreH10.
  - unfold heap_left_child. lia.
  - right.
    unfold heap_left_child, heap_right_child.
    replace (idx * 2 + 2) with (idx * 2 + 1 + 1) by lia.
    exact PreH1.
Qed. 

Lemma proof_of_pop_entail_wit_8 : pop_entail_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_2 before_2.
  assert (Hready : PopReadyState before_2 current_2 n_pre ret).
  {
    eapply pop_comparison_ready__pop_ready_exit; eauto.
  }
  pose proof PreH15 as Hselected.
  destruct Hselected as
    (_ & _ & _ & _ & _ & _ & Hselected & _).
  subst left right.
  unfold heap_selected_child in Hselected.
  destruct (Z_lt_dec (heap_right_child idx) (n_pre - 1)).
  - destruct
      (Z_lt_dec
        (Znth (heap_left_child idx) current_2 0)
        (Znth (heap_right_child idx) current_2 0));
      subst largest;
      unfold heap_left_child, heap_right_child in *;
      finish_entail.
  - subst largest.
    unfold heap_left_child, heap_right_child in *.
    finish_entail.
Qed. 

Lemma proof_of_pop_entail_wit_9 : pop_entail_wit_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists
    (replace_Znth largest (Znth idx current 0)
      (replace_Znth idx (Znth largest current 0) current))
    before_2.
  pose proof PreH15 as Hselected.
  unfold PopSelectedChild in Hselected.
  destruct Hselected as
    (Hidx_nonnegative & Hidx_bound & Hidx_selected &
     Hselected_nonnegative & Hselected_bound &
     Hselected_parent & Hselected_choice & Hselected_dominates).
  pose proof
    (pop_next_index_arithmetic__pop_swap_transition
      current (n_pre - 1) idx largest
      PreH9 PreH14 Hselected_choice)
    as (Hleft_nonnegative & Hleft_bound &
        Hright_nonnegative & Hright_bound).
  unfold heap_left_child in
    Hleft_nonnegative, Hleft_bound.
  unfold heap_right_child in
    Hright_nonnegative, Hright_bound.
  pose proof PreH16 as Hloop.
  unfold PopLoopState in Hloop.
  destruct Hloop as
    (_ & _ & Hcurrent_length & _).
  assert
    (Hswapped_read :
      Znth largest
        (replace_Znth largest (Znth idx current 0)
          (replace_Znth idx (Znth largest current 0) current)) 0 =
      Znth idx current 0).
  {
    rewrite Znth_replace_Znth_Same.
    - reflexivity.
    - rewrite Zlength_replace_Znth, Hcurrent_length.
      lia.
  }
  finish_entail.
  eapply pop_swap_advances_loop__pop_swap_transition; eauto.
Qed. 

Lemma proof_of_pop_entail_wit_10 : pop_entail_wit_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_2 before_2.
  finish_entail.
  unfold heap_capacity in *.
  lia.
Qed. 

Lemma proof_of_pop_entail_wit_11_1 : pop_entail_wit_11_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_2 before_2.
  finish_entail.
  eapply pop_leaf_ready__pop_ready_exit; eauto.
Qed. 

Lemma proof_of_pop_entail_wit_11_2 : pop_entail_wit_11_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current_2 before_2.
  finish_entail.
Qed.

Lemma proof_of_pop_entail_wit_12 : pop_entail_wit_12.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists current before_2.
  finish_entail.
  eapply pop_ready_write_result__pop_finalization; eauto.
Qed. 

Lemma proof_of_pop_entail_wit_13_split_goal_spatial :
  pop_entail_wit_13_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  rewrite <- PreH6.
  eapply pop_result_store_retired__pop_finalization; eauto.
Qed.

Lemma proof_of_pop_entail_wit_13 : pop_entail_wit_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_pop_entail_wit_13_split_goal_spatial.
Qed. 

Lemma proof_of_pop_return_wit_2_split_goal_spatial :
  pop_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst n_pre.
  cancel.
  replace (1 - 1) with 0 by lia.
  cancel.
Qed.

Lemma proof_of_pop_return_wit_2 : pop_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_pop_return_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_heap_sort_entail_wit_1_split_goal_1 :
  heap_sort_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (heap_sort_initial_state__heap_sort_setup input) as Hinitial.
  exact Hinitial.
Qed.

Lemma proof_of_heap_sort_entail_wit_1_split_goal_2 :
  heap_sort_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

(* This split goal is no longer generated.
Lemma proof_of_heap_sort_entail_wit_1_split_goal_spatial :
  heap_sort_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.
*)

Lemma proof_of_heap_sort_entail_wit_1 : heap_sort_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_heap_sort_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_heap_sort_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_heap_sort_entail_wit_2 : heap_sort_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (@nil Z) (list_to_multiset input).
  finish_entail.
  rewrite Zlength_nil, Z.sub_diag.
  reflexivity.
Qed.

Lemma proof_of_heap_sort_entail_wit_5 : heap_sort_entail_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists suffix_2 active_2.
  sep_apply_l_atomic
    (heap_sort_written_slot_split__heap_sort_write
      heap_pre i n_pre extracted suffix_2 PreH4 PreH5).
  finish_entail.
Qed.

Lemma proof_of_heap_sort_entail_wit_6 : heap_sort_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists suffix_2 active_2.
  split_pure_spatial.
  - unfold heap_retired_cell.
    replace (i - 1 + 1) with i by lia.
    sep_apply_l_atomic
      (IntArray.seg_merge_to_seg heap_pre
        (i - 1) i n_pre (extracted :: nil) suffix_2).
    + dump_pre_spatial.
      lia.
    + simpl.
      cancel.
  - pose proof
      (heap_sort_extract_step__heap_sort_transition
        input active_2 suffix_2 extracted
        PreH6 PreH7 PreH10) as [Hremove_size Hstate].
    rewrite Hremove_size, PreH8.
    rewrite Zlength_cons, PreH9.
    split_pures;
      dump_pre_spatial;
      try lia;
      try assumption.
Qed.

Lemma proof_of_heap_sort_entail_wit_8 : heap_sort_entail_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi : i = 0) by lia.
  assert (Hsize_zero : multiset_size active = 0) by lia.
  pose proof
    (heap_sort_empty_state_output__heap_sort_finalization
      input active suffix Hsize_zero PreH9)
    as [Hactive_nil [Hpermutation Hincreasing]].
  replace i with 0 by lia.
  Exists suffix.
  sep_apply_l_atomic
    (heap_sort_zero_store_join__heap_sort_finalization
      heap_pre n_pre active suffix ltac:(lia)).
  finish_entail.
Qed.
