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
  | split_pures; dump_pre_spatial; try lia; try int_auto;
    try assumption; try reflexivity;
    try solve [apply heap_representation_forget; assumption];
    try solve [apply PushLoopState_forget; assumption];
    try solve [apply PopLoopState_forget; assumption];
    try solve [apply PrefixMaximum_forget; assumption];
    try solve [apply PopSelectedChild_forget; assumption];
    try solve [apply multiset_maximum_compat; assumption];
    try solve [apply HeapSortState_compat; assumption] ].

Lemma proof_of_push_entail_wit_1 : push_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_heap. Intros base.
  match goal with H : heap_representation _ _ _ |- _ => pose proof H as Hrep end.
  apply heap_representation_compat in Hrep; try lia.
  pose proof (push_appended_source__push_initialization S_before base n_pre x_pre Hrep).
  pose proof (push_appended_loop_state__push_initialization S_before base n_pre x_pre Hrep).
  Exists (base ++ x_pre :: nil) (base ++ x_pre :: nil).
  sep_apply_l_atomic (IntArray.seg_single heap_pre n_pre x_pre).
  sep_apply_l_atomic (IntArray.full_to_seg heap_pre n_pre base).
  sep_apply_l_atomic (IntArray.seg_merge_to_full heap_pre 0 n_pre (n_pre + 1) base (x_pre :: nil) ltac:(lia)).
  replace (heap_pre + 0 * sizeof(INT)) with heap_pre by lia.
  replace (n_pre + 1 - 0) with (n_pre + 1) by lia.
  finish_entail.
Qed.

Lemma proof_of_push_entail_wit_2 : push_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (heap_parent_positive_bounds__push_sift_up child n_pre ltac:(lia) ltac:(lia))
    as [Hparent_nonnegative [Hparent_lt Hparent_bound]].
  Exists current_2 written_2.
  finish_entail; unfold heap_parent in Hparent_nonnegative, Hparent_lt, Hparent_bound; auto.
Qed.

Lemma proof_of_push_entail_wit_3 : push_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply PushLoopState_compat in PreH11; try lia.
  pose proof (push_swap_advances_loop__push_sift_up written_2 current_2 n_pre child parent x_pre
    PreH11 PreH4 PreH9 PreH1) as [Hvalue Hloop].
  Exists (replace_Znth child (Znth parent current_2 0)
    (replace_Znth parent (Znth child current_2 0) current_2)) written_2.
  finish_entail.
Qed.

Lemma proof_of_push_return_wit_1_split_goal_spatial : push_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply PushLoopState_compat in PreH7; try lia.
  assert (child = 0) by lia. subst child.
  pose proof (push_zero_exit_result__push_finalization S_before written current n_pre x_pre PreH6 PreH7).
  pose proof (push_result_representation__push_finalization S_before current n_pre x_pre PreH3 H).
  unfold store_heap. Exists current. finish_entail.
Qed.
Lemma proof_of_push_return_wit_1 : push_return_wit_1.
Proof. aggressive_pre_process. Goal_apply proof_of_push_return_wit_1_split_goal_spatial. Qed.

Lemma proof_of_push_return_wit_2_split_goal_spatial : push_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply PushLoopState_compat in PreH11; try lia.
  pose proof (push_break_establishes_result__push_sift_up S_before written current n_pre child parent x_pre
    PreH10 PreH11 PreH9 PreH1) as Hresult.
  pose proof (push_result_representation__push_finalization S_before current n_pre x_pre PreH3 Hresult).
  unfold store_heap. Exists current. finish_entail.
Qed.
Lemma proof_of_push_return_wit_2 : push_return_wit_2.
Proof. aggressive_pre_process. Goal_apply proof_of_push_return_wit_2_split_goal_spatial. Qed.

Lemma proof_of_build_entail_wit_1 : build_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct (Z.eq_dec n_pre 0) as [Hzero | Hpositive].
  - subst n_pre. Left. finish_entail.
  - Right.
    pose proof (build_initial_prefix__build_progress input n_pre PreH3 ltac:(lia))
      as [Hprefix Hrepresentation].
    apply (proj2 (BuildPrefixState_compat _ input 1 ltac:(lia) ltac:(lia))) in Hprefix.
    sep_apply (IntArray.full_split_to_seg heap_pre 1 n_pre input); try lia.
    unfold store_heap. Exists (list_to_multiset (Znth 0 input 0 :: nil)).
    Exists (sublist 0 1 input).
    sep_apply (IntArray.seg_to_full heap_pre 0 1 (sublist 0 1 input)).
    finish_entail.
    replace (heap_pre + 0 * sizeof(INT)) with heap_pre by lia.
    replace (1 - 0) with 1 by lia. cancel.
Qed.

Lemma proof_of_build_entail_wit_2 : build_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto). Exists S_prefix_2.
  sep_apply (build_split_next_cell__build_progress heap_pre i n_pre input); try lia.
  finish_entail.
  all: try (rewrite Znth_sublist by lia; f_equal; lia).
  unfold heap_spare. cancel.
Qed.

Lemma proof_of_build_entail_wit_3_split_goal_1 : build_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  apply BuildPrefixState_compat; try lia.
  apply BuildPrefixState_compat in PreH7; try lia.
  eapply build_prefix_extend__build_progress; eauto; lia.
Qed.
Lemma proof_of_build_entail_wit_3 : build_entail_wit_3.
Proof. aggressive_pre_process. Goal_apply proof_of_build_entail_wit_3_split_goal_1. Qed.

Lemma proof_of_build_return_wit_1_split_goal_spatial : build_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto). subst n_pre. apply Zlength_nil_inv in PreH4. subst input.
  unfold store_heap. Exists (@nil Z). finish_entail.
  unfold heap_representation, heap_relation, heap_ordered, multiset_size, list_to_multiset.
  simpl. repeat split; try lia. apply Permutation_refl.
Qed.
Lemma proof_of_build_return_wit_1 : build_return_wit_1.
Proof. aggressive_pre_process. Goal_apply proof_of_build_return_wit_1_split_goal_spatial. Qed.

Lemma proof_of_build_return_wit_2_split_goal_spatial : build_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto). assert (Hi : i = n_pre) by lia. subst i.
  apply BuildPrefixState_compat in PreH7; try lia.
  pose proof (build_prefix_complete__build_finalization S_prefix input n_pre PreH7 ltac:(lia)) as Hequiv.
  unfold store_heap. Intros concrete.
  apply heap_representation_compat in H; try lia.
  pose proof (store_heap_equiv_transport__build_finalization S_prefix (list_to_multiset input)
    concrete n_pre Hequiv H).
  Exists concrete. rewrite (Zsublist_nil input n_pre n_pre) by lia.
  rewrite (IntArray.seg_empty heap_pre n_pre n_pre). finish_entail. Intros. cancel.
Qed.
Lemma proof_of_build_return_wit_2 : build_return_wit_2.
Proof. aggressive_pre_process. Goal_apply proof_of_build_return_wit_2_split_goal_spatial. Qed.

Lemma proof_of_pop_entail_wit_1 : pop_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto). unfold store_heap. Intros before.
  apply heap_representation_compat in H; try lia.
  pose proof (heap_root_is_multiset_max__pop_initialization S_before before n_pre PreH1 H)
    as [Hprefix [Hroot Hmaximum]].
  Exists before. finish_entail.
Qed.

Lemma proof_of_pop_entail_wit_2 : pop_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH4 as [Hsize [Hlen [Hperm Horder]]].
  pose proof (pop_root_replacement_loop_state__pop_initialization before n_pre ltac:(lia) Hlen Horder).
  Exists (replace_Znth 0 (Znth (n_pre - 1) before 0) before) before. finish_entail.
Qed.

Lemma proof_of_pop_entail_wit_3_1 : pop_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(int_auto). Exists current_2 before_2. finish_entail.
  apply PopSelectedChild_forget.
  replace (idx * 2 + 1 + 1) with (heap_right_child idx) by (unfold heap_right_child; lia).
  apply pop_select_right__pop_child_selection.
  - exact PreH11.
  - unfold heap_right_child. lia.
  - unfold heap_left_child, heap_right_child.
    replace (idx * 2 + 2) with (idx * 2 + 1 + 1) by lia. exact PreH1.
Qed.

Lemma proof_of_pop_entail_wit_3_2 : pop_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(int_auto). Exists current_2 before_2. finish_entail.
  apply PopSelectedChild_forget. apply pop_select_left__pop_child_selection.
  - exact PreH10.
  - unfold heap_left_child. lia.
  - left. unfold heap_right_child. lia.
Qed.

Lemma proof_of_pop_entail_wit_3_3 : pop_entail_wit_3_3.
Proof.
  LLM_pre_process ltac:(int_auto). Exists current_2 before_2. finish_entail.
  apply PopSelectedChild_forget. apply pop_select_left__pop_child_selection.
  - exact PreH11.
  - unfold heap_left_child. lia.
  - right. unfold heap_left_child, heap_right_child.
    replace (idx * 2 + 2) with (idx * 2 + 1 + 1) by lia. exact PreH1.
Qed.

Lemma proof_of_pop_entail_wit_4 : pop_entail_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (PopSelectedChild_forward _ _ _ _ PreH9 PreH15) as Hforward.
  apply PopSelectedChild_compat in PreH15; try lia.
  apply PopLoopState_compat in PreH16; try lia.
  pose proof (pop_swap_advances_loop__pop_swap_transition before_2 current_2 n_pre idx largest
    PreH16 PreH15 PreH1).
  Exists (replace_Znth largest (Znth idx current_2 0)
    (replace_Znth idx (Znth largest current_2 0) current_2)) before_2.
  finish_entail. unfold heap_capacity in *. lia.
Qed.

Lemma proof_of_pop_return_wit_1_split_goal_spatial : pop_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH6 as [Hs [Hl _]].
  apply heap_representation_compat in PreH6; try lia.
  apply PrefixMaximum_compat in PreH7; try lia.
  apply PopLoopState_compat in PreH13; try lia.
  pose proof (pop_leaf_ready__pop_ready_exit before current n_pre ret idx PreH7 PreH13 PreH1) as Hready.
  pose proof (pop_ready_write_result__pop_finalization S_before before current n_pre ret
    PreH5 PreH6 Hready) as Hresult.
  sep_apply_l_atomic (pop_result_store_retired__pop_finalization heap_pre S_before before current n_pre ret
    PreH3 Hresult).
  sep_apply_l_atomic (store_heap_forget heap_pre (multiset_remove S_before ret) (n_pre - 1)). cancel.
Qed.
Lemma proof_of_pop_return_wit_1 : pop_return_wit_1.
Proof. aggressive_pre_process. Goal_apply proof_of_pop_return_wit_1_split_goal_spatial. Qed.

Lemma proof_of_pop_return_wit_2_split_goal_spatial : pop_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof PreH6 as [Hs [Hl _]].
  pose proof (PopSelectedChild_forward _ _ _ _ PreH9 PreH15) as Hforward.
  apply heap_representation_compat in PreH6; try lia.
  apply PrefixMaximum_compat in PreH7; try lia.
  apply PopLoopState_compat in PreH16; try lia.
  apply PopSelectedChild_compat in PreH15; try lia.
  pose proof (pop_comparison_ready__pop_ready_exit before current n_pre ret idx largest
    PreH7 PreH16 PreH15 PreH1) as Hready.
  pose proof (pop_ready_write_result__pop_finalization S_before before current n_pre ret
    PreH5 PreH6 Hready) as Hresult.
  sep_apply_l_atomic (pop_result_store_retired__pop_finalization heap_pre S_before before current n_pre ret
    PreH3 Hresult).
  sep_apply_l_atomic (store_heap_forget heap_pre (multiset_remove S_before ret) (n_pre - 1)). cancel.
Qed.
Lemma proof_of_pop_return_wit_2 : pop_return_wit_2.
Proof. aggressive_pre_process. Goal_apply proof_of_pop_return_wit_2_split_goal_spatial. Qed.

Lemma proof_of_pop_return_wit_3_split_goal_spatial : pop_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto). subst n_pre.
  destruct PreH4 as [Hsize [Hlength _]].
  pose proof (remove_max_singleton_empty__pop_singleton S_before Hsize) as Hremoved.
  rewrite PreH6. replace (1 - 1) with 0 by lia.
  sep_apply_l_atomic (singleton_full_split_retired__pop_singleton heap_pre before
    (Znth 0 before 0) Hlength eq_refl).
  unfold store_heap. Exists (@nil Z). finish_entail.
  - unfold heap_spare. replace (0 + 1) with 1 by lia. cancel.
  - unfold heap_representation, heap_relation, heap_ordered, multiset_size.
    rewrite Hremoved. simpl. repeat split; try lia. apply Permutation_refl.
Qed.
Lemma proof_of_pop_return_wit_3 : pop_return_wit_3.
Proof. aggressive_pre_process. Goal_apply proof_of_pop_return_wit_3_split_goal_spatial. Qed.

Lemma proof_of_heap_sort_entail_wit_1_split_goal_1 : heap_sort_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto). apply HeapSortState_compat.
  apply heap_sort_initial_state__heap_sort_setup.
Qed.
Lemma proof_of_heap_sort_entail_wit_1_split_goal_2 : heap_sort_entail_wit_1_split_goal_2.
Proof. LLM_pre_process ltac:(int_auto). rewrite Zlength_nil. lia. Qed.
Lemma proof_of_heap_sort_entail_wit_1_split_goal_3 : heap_sort_entail_wit_1_split_goal_3.
Proof. LLM_pre_process ltac:(int_auto). Qed.
Lemma proof_of_heap_sort_entail_wit_1 : heap_sort_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_heap_sort_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_heap_sort_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_heap_sort_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_heap_sort_entail_wit_2 : heap_sort_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (heap_sort_extract input active_2 suffix_2 retval PreH1 PreH10) as [Hsize Hnext].
  Exists (retval :: suffix_2) (multiset_remove active_2 retval).
  sep_apply_l_atomic (IntArray.seg_single heap_pre (i - 1) retval).
  replace (i - 1 + 1) with i by lia.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.seg_merge_to_seg heap_pre (i - 1) i n_pre (retval :: nil) suffix_2).
    + dump_pre_spatial. lia.
    + simpl. cancel.
  - rewrite Hsize, PreH8. rewrite Zlength_cons, PreH9.
    split_pures; dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_heap_sort_return_wit_1 : heap_sort_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi : i = 0) by lia. replace i with 0 in * by lia.
  apply HeapSortState_compat in PreH9.
  pose proof (heap_sort_empty_state_output__heap_sort_finalization input active suffix
    ltac:(lia) PreH9) as [Hnil [HP HI]].
  Exists suffix.
  sep_apply_l_atomic (store_heap_to_internal heap_pre active 0 ltac:(lia) ltac:(unfold heap_capacity; lia)).
  sep_apply_l_atomic (heap_sort_zero_store_join__heap_sort_finalization heap_pre n_pre active suffix ltac:(lia)).
  finish_entail.
Qed.
