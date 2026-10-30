From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P032_1561C_deep_down_below_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P032_1561C_deep_down_below_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P032_1561C_deep_down_below_lib.
Local Open Scope sac.

Lemma proof_of_sift_caves_entail_wit_1 : sift_caves_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  Exists gains requirements.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      unfold ParallelPermutation in *;
      try reflexivity; try lia; try assumption.
Qed.

Lemma proof_of_sift_caves_entail_wit_2_1 : sift_caves_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (2 * root_pre + 1 + 1) with (2 * root_pre + 2) in * by lia.
  Left.
  Exists gains_now_2 requirements_now_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      unfold ParallelPermutation in *;
      try reflexivity; try lia; try assumption.
    unfold SelectedLargerChild.
    split.
    + right; reflexivity.
    + split; [lia |].
      split.
      * intros; lia.
      * intros; reflexivity.
Qed.

Lemma proof_of_sift_caves_entail_wit_2_2 : sift_caves_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (2 * root + 1 + 1) with (2 * root + 2) in * by lia.
  Right.
  Exists root gains_now_2 requirements_now_2.
  split_pure_spatial.
  - cancel ((( &( "root" ) )) # Int |-> root).
    cancel (Int64Array.full req_pre n requirements_now_2).
    cancel (Int64Array.full gain_pre n gains_now_2).
  - split_pures; dump_pre_spatial;
      unfold ParallelPermutation in *;
      try reflexivity; try lia; try assumption.
    unfold SelectedLargerChild.
    split.
    + right; reflexivity.
    + split; [lia |].
      split.
      * intros; lia.
      * intros; reflexivity.
Qed.

Lemma proof_of_sift_caves_entail_wit_2_3 : sift_caves_entail_wit_2_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (2 * root + 1 + 1) with (2 * root + 2) in * by lia.
  Right.
  Exists root gains_now_2 requirements_now_2.
  split_pure_spatial.
  - cancel ((( &( "root" ) )) # Int |-> root).
    cancel (Int64Array.full req_pre n requirements_now_2).
    cancel (Int64Array.full gain_pre n gains_now_2).
  - split_pures; dump_pre_spatial;
      unfold ParallelPermutation in *;
      try reflexivity; try lia; try assumption.
    unfold SelectedLargerChild.
    split.
    + left; reflexivity.
    + split; [lia |].
      split.
      * intros; reflexivity.
      * intros; lia.
Qed.

Lemma proof_of_sift_caves_entail_wit_2_4 : sift_caves_entail_wit_2_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (2 * root_pre + 1 + 1) with (2 * root_pre + 2) in * by lia.
  Left.
  Exists gains_now_2 requirements_now_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      unfold ParallelPermutation in *;
      try reflexivity; try lia; try assumption.
    unfold SelectedLargerChild.
    split.
    + left; reflexivity.
    + split; [lia |].
      split.
      * intros; reflexivity.
      * intros; lia.
Qed.

Lemma proof_of_sift_caves_entail_wit_2_5 : sift_caves_entail_wit_2_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (2 * root_pre + 1 + 1) with (2 * root_pre + 2) in * by lia.
  Left.
  Exists gains_now_2 requirements_now_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      unfold ParallelPermutation in *;
      try reflexivity; try lia; try assumption.
    unfold SelectedLargerChild.
    split.
    + left; reflexivity.
    + split; [lia |].
      split.
      * intros; reflexivity.
      * intros; lia.
Qed.

Lemma proof_of_sift_caves_entail_wit_2_6 : sift_caves_entail_wit_2_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (2 * root + 1 + 1) with (2 * root + 2) in * by lia.
  Right.
  Exists root gains_now_2 requirements_now_2.
  split_pure_spatial.
  - cancel ((( &( "root" ) )) # Int |-> root).
    cancel (Int64Array.full req_pre n requirements_now_2).
    cancel (Int64Array.full gain_pre n gains_now_2).
  - split_pures; dump_pre_spatial;
      unfold ParallelPermutation in *;
      try reflexivity; try lia; try assumption.
    unfold SelectedLargerChild.
    split.
    + left; reflexivity.
    + split; [lia |].
      split.
      * intros; reflexivity.
      * intros; lia.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_1_split_goal_1 : sift_caves_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite double_replace_suffix__sift_swap by lia.
  exact PreH16.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_1_split_goal_2 : sift_caves_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite double_replace_suffix__sift_swap by lia.
  exact PreH15.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_1_split_goal_3 : sift_caves_entail_wit_3_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (root_pre < child_2).
  { pose proof PreH12 as Hselected. unfold SelectedLargerChild in Hselected.
    destruct Hselected as [[-> | ->] _]; lia. }
  rewrite Z.quot_div_nonneg by lia.
  eapply selected_swap_descendant_edge__sift_swap; eauto; try lia.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_1_split_goal_4 : sift_caves_entail_wit_3_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (root_pre < child_2).
  { pose proof PreH12 as Hselected. unfold SelectedLargerChild in Hselected.
    destruct Hselected as [[-> | ->] _]; lia. }
  rewrite Z.quot_div_nonneg by lia.
  eapply selected_swap_descendant_edge__sift_swap; eauto; try lia.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_1_split_goal_5 : sift_caves_entail_wit_3_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply heap_except_after_selected_swap__sift_swap; eauto; try lia.
  intros Hrootpos Hparent.
  pose proof (heap_parent_bounds__sift_swap root_pre ltac:(lia)). lia.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_1_split_goal_6 : sift_caves_entail_wit_3_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply parallel_permutation_swap__sift_swap; eauto; lia.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_1_split_goal_7 : sift_caves_entail_wit_3_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SelectedLargerChild in PreH12.
  destruct PreH12 as [[-> | ->] _]; lia.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_1_split_goal_8 : sift_caves_entail_wit_3_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat rewrite Zlength_replace_Znth. exact PreH5.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_1_split_goal_9 : sift_caves_entail_wit_3_1_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat rewrite Zlength_replace_Znth. exact PreH4.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_1 : sift_caves_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_caves_entail_wit_3_1_split_goal_1.
  - Goal_apply proof_of_sift_caves_entail_wit_3_1_split_goal_2.
  - Goal_apply proof_of_sift_caves_entail_wit_3_1_split_goal_3.
  - Goal_apply proof_of_sift_caves_entail_wit_3_1_split_goal_4.
  - Goal_apply proof_of_sift_caves_entail_wit_3_1_split_goal_5.
  - Goal_apply proof_of_sift_caves_entail_wit_3_1_split_goal_6.
  - Goal_apply proof_of_sift_caves_entail_wit_3_1_split_goal_7.
  - Goal_apply proof_of_sift_caves_entail_wit_3_1_split_goal_8.
  - Goal_apply proof_of_sift_caves_entail_wit_3_1_split_goal_9.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_2_split_goal_1 : sift_caves_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite double_replace_suffix__sift_swap by lia.
  exact PreH17.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_2_split_goal_2 : sift_caves_entail_wit_3_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite double_replace_suffix__sift_swap by lia.
  exact PreH16.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_2_split_goal_3 : sift_caves_entail_wit_3_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (root < child_2).
  { pose proof PreH12 as Hselected. unfold SelectedLargerChild in Hselected.
    destruct Hselected as [[-> | ->] _]; lia. }
  rewrite Z.quot_div_nonneg by lia.
  eapply selected_swap_descendant_edge__sift_swap; eauto; try lia.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_2_split_goal_4 : sift_caves_entail_wit_3_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (root < child_2).
  { pose proof PreH12 as Hselected. unfold SelectedLargerChild in Hselected.
    destruct Hselected as [[-> | ->] _]; lia. }
  rewrite Z.quot_div_nonneg by lia.
  eapply selected_swap_descendant_edge__sift_swap; eauto; try lia.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_2_split_goal_5 : sift_caves_entail_wit_3_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply heap_except_after_selected_swap__sift_swap; eauto; try lia.
  intros Hrootpos Hparent.
  rewrite Z.quot_div_nonneg in PreH13 by lia.
  exact PreH13.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_2_split_goal_6 : sift_caves_entail_wit_3_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply parallel_permutation_swap__sift_swap; eauto; lia.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_2_split_goal_7 : sift_caves_entail_wit_3_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SelectedLargerChild in PreH12.
  destruct PreH12 as [[-> | ->] _]; lia.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_2_split_goal_8 : sift_caves_entail_wit_3_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat rewrite Zlength_replace_Znth. exact PreH5.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_2_split_goal_9 : sift_caves_entail_wit_3_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat rewrite Zlength_replace_Znth. exact PreH4.
Qed.

Lemma proof_of_sift_caves_entail_wit_3_2 : sift_caves_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_caves_entail_wit_3_2_split_goal_1.
  - Goal_apply proof_of_sift_caves_entail_wit_3_2_split_goal_2.
  - Goal_apply proof_of_sift_caves_entail_wit_3_2_split_goal_3.
  - Goal_apply proof_of_sift_caves_entail_wit_3_2_split_goal_4.
  - Goal_apply proof_of_sift_caves_entail_wit_3_2_split_goal_5.
  - Goal_apply proof_of_sift_caves_entail_wit_3_2_split_goal_6.
  - Goal_apply proof_of_sift_caves_entail_wit_3_2_split_goal_7.
  - Goal_apply proof_of_sift_caves_entail_wit_3_2_split_goal_8.
  - Goal_apply proof_of_sift_caves_entail_wit_3_2_split_goal_9.
Qed.

Lemma proof_of_sift_caves_return_wit_1_split_goal_1 : sift_caves_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (heap_parents_after_selected_stop__sift_returns
    requirements_now root_pre hi_pre root_pre child PreH12 ltac:(lia) PreH14).
Qed.

Lemma proof_of_sift_caves_return_wit_1 : sift_caves_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_caves_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_sift_caves_return_wit_2_split_goal_1 : sift_caves_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (heap_parents_after_selected_stop__sift_returns
    requirements_now root_pre hi_pre root child PreH12 ltac:(lia) PreH15).
Qed.

Lemma proof_of_sift_caves_return_wit_2 : sift_caves_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_caves_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_sift_caves_return_wit_3_split_goal_1 : sift_caves_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (heap_parents_after_leaf_stop__sift_returns
    requirements_now root_pre hi_pre root_pre PreH1 PreH13).
Qed.

Lemma proof_of_sift_caves_return_wit_3 : sift_caves_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_caves_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_sift_caves_return_wit_4_split_goal_1 : sift_caves_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (heap_parents_after_leaf_stop__sift_returns
    requirements_now root_pre hi_pre root PreH1 PreH13).
Qed.

Lemma proof_of_sift_caves_return_wit_4 : sift_caves_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sift_caves_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_sort_caves_safety_wit_1_split_goal_1 : sort_caves_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (n_pre ÷ 2 <= n_pre) by (apply Z.quot_le_upper_bound; lia).
  dump_pre_spatial.
  change INT_MAX with 2147483647.
  lia.
Qed.

Lemma proof_of_sort_caves_safety_wit_1_split_goal_2 : sort_caves_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (0 <= n_pre ÷ 2) by (apply Z.quot_pos; lia).
  dump_pre_spatial.
  change INT_MIN with (-2147483648).
  lia.
Qed.

Lemma proof_of_sort_caves_safety_wit_1 : sort_caves_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_caves_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_sort_caves_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_sort_caves_entail_wit_1_split_goal_1 : sort_caves_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  replace (n_pre / 2 - 1 + 1) with (n_pre / 2) by lia.
  apply heap_parents_vacuous_above_last_parent__sort_heapify.
  lia.
Qed.

Lemma proof_of_sort_caves_entail_wit_1_split_goal_2 : sort_caves_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ParallelPermutation.
  apply Permutation_refl.
Qed.

Lemma proof_of_sort_caves_entail_wit_1_split_goal_3 : sort_caves_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (0 <= n_pre ÷ 2) by (apply Z.quot_pos; lia).
  lia.
Qed.

Lemma proof_of_sort_caves_entail_wit_1 : sort_caves_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_caves_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_sort_caves_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_sort_caves_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_sort_caves_entail_wit_2_split_goal_1 : sort_caves_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply heap_parents_to_ordered_except__sort_heapify.
  exact PreH11.
Qed.

Lemma proof_of_sort_caves_entail_wit_2 : sort_caves_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sort_caves_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_sort_caves_entail_wit_3_split_goal_1 : sort_caves_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (root - 1 + 1) with root by lia.
  exact PreH4.
Qed.

Lemma proof_of_sort_caves_entail_wit_3_split_goal_2 : sort_caves_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ParallelPermutation in *.
  eapply Permutation_trans.
  - exact PreH15.
  - exact PreH3.
Qed.

Lemma proof_of_sort_caves_entail_wit_3 : sort_caves_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_caves_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_sort_caves_entail_wit_3_split_goal_2.
Qed.

Lemma proof_of_sort_caves_entail_wit_4_split_goal_1 : sort_caves_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply heapify_exit_state__sort_heapify; eauto.
Qed.

Lemma proof_of_sort_caves_entail_wit_4 : sort_caves_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sort_caves_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_sort_caves_entail_wit_5_split_goal_1 : sort_caves_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply heap_extract_cross__sort_extraction; eauto; lia.
Qed.

Lemma proof_of_sort_caves_entail_wit_5_split_goal_2 : sort_caves_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply heap_extract_suffix__sort_extraction; eauto; lia.
Qed.

Lemma proof_of_sort_caves_entail_wit_5_split_goal_3 : sort_caves_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH10 as [_ [_ [_ [Hheap _]]]].
  eapply heap_extract_except__sort_extraction; eauto; lia.
Qed.

Lemma proof_of_sort_caves_entail_wit_5_split_goal_4 : sort_caves_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH10 as [_ [_ [Hperm _]]].
  eapply parallel_permutation_swap__sort_extraction; eauto; lia.
Qed.

Lemma proof_of_sort_caves_entail_wit_5_split_goal_5 : sort_caves_entail_wit_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat rewrite Zlength_replace_Znth.
  exact PreH7.
Qed.

Lemma proof_of_sort_caves_entail_wit_5_split_goal_6 : sort_caves_entail_wit_5_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat rewrite Zlength_replace_Znth.
  exact PreH6.
Qed.

Lemma proof_of_sort_caves_entail_wit_5 : sort_caves_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_caves_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_sort_caves_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_sort_caves_entail_wit_5_split_goal_3.
  - Goal_apply proof_of_sort_caves_entail_wit_5_split_goal_4.
  - Goal_apply proof_of_sort_caves_entail_wit_5_split_goal_5.
  - Goal_apply proof_of_sort_caves_entail_wit_5_split_goal_6.
Qed.

Lemma proof_of_sort_caves_entail_wit_6_split_goal_1 : sort_caves_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (hi - 1 + 1) with hi in PreH5 by lia.
  apply (heap_state_after_sift__sort_extraction
    requirements gains requirements_now_2 gains_now_2
    requirements_after gains_after n_pre hi
    PreH9 PreH10 PreH11 PreH12 PreH1 PreH2 ltac:(lia)
    PreH15 PreH3 PreH4 PreH5 PreH17).
  intros p q Hp Hq. apply PreH18. lia.
Qed.

Lemma proof_of_sort_caves_entail_wit_6 : sort_caves_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sort_caves_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_sort_caves_return_wit_1_split_goal_1 : sort_caves_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (hi = 0) by lia. subst hi.
  eapply heap_state_zero_increasing__sort_extraction; eauto; lia.
Qed.

Lemma proof_of_sort_caves_return_wit_1_split_goal_2 : sort_caves_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH10 as [_ [_ [Hperm _]]]. exact Hperm.
Qed.

Lemma proof_of_sort_caves_return_wit_1 : sort_caves_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_sort_caves_return_wit_1_split_goal_1.
  - Goal_apply proof_of_sort_caves_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_sort_caves_partial_solve_wit_1_pure_split_goal_1 : sort_caves_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (n_pre ÷ 2 <= n_pre) by (apply Z.quot_le_upper_bound; lia).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_sort_caves_partial_solve_wit_1_pure : sort_caves_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_sort_caves_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_4_split_goal_1 : solver_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (summary_pointwise_bounds__solver_bounds
    requirements_sorted gains_sorted i PreH16 ltac:(lia)) as Hbounds.
  destruct Hbounds as [_ [Hrequirements _]].
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_4_split_goal_2 : solver_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (summary_pointwise_bounds__solver_bounds
    requirements_sorted gains_sorted i PreH16 ltac:(lia)) as Hbounds.
  destruct Hbounds as [_ [Hrequirements _]].
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_5_split_goal_1 : solver_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (summary_pointwise_bounds__solver_bounds
    requirements_sorted gains_sorted i PreH17 ltac:(lia)) as Hbounds.
  destruct Hbounds as [_ [_ Hgains]].
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_5_split_goal_2 : solver_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (summary_pointwise_bounds__solver_bounds
    requirements_sorted gains_sorted i PreH17 ltac:(lia)) as Hbounds.
  destruct Hbounds as [_ [_ Hgains]].
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_5_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_6_split_goal_1 : solver_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (summary_pointwise_bounds__solver_bounds
    requirements_sorted gains_sorted i PreH17 ltac:(lia)) as Hbounds.
  destruct Hbounds as [_ [_ Hgains]].
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_6_split_goal_2 : solver_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (summary_pointwise_bounds__solver_bounds
    requirements_sorted gains_sorted i PreH17 ltac:(lia)) as Hbounds.
  destruct Hbounds as [_ [_ Hgains]].
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold GreedyNeed. repeat split; try lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply (summary_bounds_preserved_by_pair_permutation__solver_greedy
    caves requirements gains requirements_after gains_after).
  - unfold CaveInputBounds. split; [lia|]. split.
    + intros j Hj.
      rewrite (Znth_indep caves j (@nil Z) __default__List_Z Hj).
      apply PreH7. lia.
    + split; [lia|]. intros k Hk. apply PreH9. lia.
  - exact PreH13.
  - exact PreH3.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SortedCaveSummaries.
  exact (conj PreH13 (conj PreH3 PreH4)).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold CaveInputBounds. split; [lia|]. split.
  - intros j Hj.
    rewrite (Znth_indep caves j (@nil Z) __default__List_Z Hj).
    apply PreH7. lia.
  - split; [lia|]. intros k Hk. apply PreH9. lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_5 : solver_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply greedy_need_step_raise__solver_greedy; eauto.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_2 : solver_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite sum_sublist_snoc__solver_greedy by lia. lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_3 : solver_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH17 as [_ [_ Hpointwise]].
  specialize (Hpointwise i ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_4 : solver_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH17 as [Hlength [Hsum Hpointwise]].
  assert (Hnonneg : Forall (fun x : Z => 0 <= x) gains_sorted_2).
  {
    apply Forall_forall. intros x Hx.
    apply In_nth with (d := 0) in Hx.
    destruct Hx as [k [Hk Hx]].
    specialize (Hpointwise (Z.of_nat k)).
    unfold Znth in Hpointwise. rewrite Nat2Z.id in Hpointwise.
    rewrite Hx in Hpointwise.
    specialize (Hpointwise ltac:(rewrite !Zlength_correct in *; lia)). lia.
  }
  pose proof (sum_sublist_prefix_le_total__solver_greedy
    gains_sorted_2 (i + 1) Hnonneg) as Hprefix.
  rewrite sum_sublist_snoc__solver_greedy in Hprefix by lia. lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1_split_goal_5 : solver_entail_wit_2_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH17 as [_ [_ Hpointwise]].
  specialize (Hpointwise i ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_2_1_split_goal_5.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply greedy_need_step_keep__solver_greedy; eauto.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_2 : solver_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite sum_sublist_snoc__solver_greedy by lia. lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_3 : solver_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH17 as [Hlength [Hsum Hpointwise]].
  assert (Hnonneg : Forall (fun x : Z => 0 <= x) gains_sorted_2).
  {
    apply Forall_forall. intros x Hx.
    apply In_nth with (d := 0) in Hx.
    destruct Hx as [k [Hk Hx]].
    specialize (Hpointwise (Z.of_nat k)).
    unfold Znth in Hpointwise. rewrite Nat2Z.id in Hpointwise.
    rewrite Hx in Hpointwise.
    specialize (Hpointwise ltac:(rewrite !Zlength_correct in *; lia)). lia.
  }
  pose proof (sum_sublist_prefix_le_total__solver_greedy
    gains_sorted_2 (i + 1) Hnonneg) as Hprefix.
  rewrite sum_sublist_snoc__solver_greedy in Hprefix by lia. lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2_split_goal_4 : solver_entail_wit_2_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH17 as [_ [_ Hpointwise]].
  specialize (Hpointwise i ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_2_2_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply sorted_greedy_need_characterizes_spec__solver_final; eauto.
  replace (Zlength caves) with i by lia.
  exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
Qed.
