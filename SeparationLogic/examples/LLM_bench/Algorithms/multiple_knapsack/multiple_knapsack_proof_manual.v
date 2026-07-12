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
From SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack Require Import multiple_knapsack_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_lib.
Local Open Scope sac.

Lemma proof_of_multipleKnapsack_safety_wit_12 : multipleKnapsack_safety_wit_12.
Proof.
  pre_process.
  entailer!.
  - destruct PreH37 as [_ Hold_bound].
    specialize (Hold_bound pos ltac:(lia)).
    nia.
  - destruct PreH37 as [_ Hold_bound].
    specialize (Hold_bound pos ltac:(lia)).
    nia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_1 : multipleKnapsack_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  split_pure_spatial.
  - sep_apply (IntArray.undef_full_split_to_undef_seg dp_pre 0 (capacity_pre + 1) ltac:(lia)).
    repeat cancel.
    rewrite IntArray.undef_seg_empty.
    rewrite IntArray.seg_empty.
    entailer!.
  - entailer!.
    unfold MKZeroPrefix.
    repeat split; try lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_2 : multipleKnapsack_entail_wit_2.
Proof.
  pre_process.
  Exists (dp_l_2 ++ 0 :: nil).
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    + apply MKZeroPrefix_extend_by_zero; auto.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_3 : multipleKnapsack_entail_wit_3.
Proof.
  pre_process.
  assert (Hj : j = capacity_pre + 1) by lia.
  rewrite Hj in *.
  Exists dp_l_2.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    sep_apply (IntArray.seg_to_full dp_pre 0 (capacity_pre + 1) dp_l_2).
    replace (dp_pre + 0 * sizeof (INT)) with dp_pre by lia.
    replace (capacity_pre + 1 - 0) with (capacity_pre + 1) by lia.
    repeat cancel.
  - repeat split_pures; try solve [dump_pre_spatial; auto; try lia].
    dump_pre_spatial.
    apply MKZeroPrefix_implies_MKDPTable_zero_items; auto.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_4 : multipleKnapsack_entail_wit_4.
Proof.
  pre_process.
  Exists qval0.
  Exists qidx0.
  Exists old0.
  Exists dp_l_2.
  split_pure_spatial.
  - repeat cancel.
  - sep_apply (IntArray.full_Zlength old_pre (capacity_pre + 1) old0).
    Intros.
    sep_apply (IntArray.full_Zlength q_idx_pre (capacity_pre + 1) qidx0).
    Intros.
    sep_apply (IntArray.full_Zlength q_val_pre (capacity_pre + 1) qval0).
    Intros.
    entailer!.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_5 : multipleKnapsack_entail_wit_5.
Proof.
  pre_process.
  Exists qval_l_2.
  Exists qidx_l_2.
  Exists old_l_2.
  Exists dp_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    apply MKCopyPrefix_zero; auto.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6 : multipleKnapsack_entail_wit_6.
Proof.
  pre_process.
  Exists qval_l_2.
  Exists qidx_l_2.
  Exists (replace_Znth j (Znth j dp_l_2 0) old_l_2).
  Exists dp_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    + apply MKCopyPrefix_extend_by_replace_Znth; auto; lia.
    + rewrite Zlength_replace_Znth; auto.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_7 : multipleKnapsack_entail_wit_7.
Proof.
  pre_process.
  assert (Hj : j = capacity_pre + 1) by lia.
  rewrite Hj in *.
  assert (Hweight_current : 1 <= Znth i weights_l 0 <= capacity_pre + 1)
    by (pose proof (PreH19 i ltac:(lia)) as Hcur; tauto).
  assert (Hvalue_current : 0 <= Znth i values_l 0 <= 1000)
    by (pose proof (PreH19 i ltac:(lia)) as Hcur; tauto).
  assert (Hcount_current : 0 <= Znth i counts_l 0 <= capacity_pre)
    by (pose proof (PreH19 i ltac:(lia)) as Hcur; tauto).
  assert (Hglobal_bounds :
    forall idx, 0 <= idx < Zlength weights_l ->
      1 <= Znth idx weights_l 0 /\ 0 <= Znth idx values_l 0 <= 1000).
  {
    intros idx Hidx.
    pose proof (PreH19 idx ltac:(lia)) as Hidx_bounds.
    tauto.
  }
  Exists qval_l_2. Exists qidx_l_2. Exists old_l_2. Exists dp_l_2.
  split_pure_spatial.
  - repeat cancel.
  - repeat split_pures; try solve [dump_pre_spatial; auto; try lia].
    + dump_pre_spatial.
      eapply MKDPTable_copy_implies_MKDPValueBound_under_global_item_bounds; eauto; lia.
    + dump_pre_spatial.
      eapply MKDPTable_implies_MKTransitionValueBound_for_current_item; eauto; lia.
    + dump_pre_spatial.
      eapply MKCopyPrefix_full_implies_MKItemResidueProgress_zero; eauto; lia.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_8 : multipleKnapsack_entail_wit_8.
Proof.
  pre_process.
  Exists qval_l_2.
  Exists qidx_l_2.
  Exists old_l_2.
  Exists dp_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    apply MKDPTable_copy_full with (src := dp_l_2); auto.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_9 : multipleKnapsack_entail_wit_9.
Proof.
  pre_process.
  Exists qval_l_2.
  Exists qidx_l_2.
  Exists old_l_2.
  Exists dp_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    + apply MKResidueLoopState_empty_queue_init; auto; lia.
    + apply MKItemResiduePrefixProgress_init; auto; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10 : multipleKnapsack_entail_wit_10.
Proof.
  pre_process.
  Exists qval_l_2.
  Exists qidx_l_2.
  Exists old_l.
  Exists dp_l_2.
  assert (Hkcap : k <= capacity_pre).
  {
    assert (Hkwcap : k * w <= capacity_pre) by lia.
    replace k with (k * 1) by lia.
    eapply Z.le_trans with (m := k * w).
    - apply Z.mul_le_mono_nonneg_l; lia.
    - exact Hkwcap.
  }
  pose proof PreH37 as H35_value_bound.
  destruct H35_value_bound as [_ Hold_value_bound].
  pose proof (Hold_value_bound pos ltac:(lia)) as Hold_pos_bound.
  assert (Hkv_nonneg : 0 <= k * v) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hkv_bound : k * v <= 1000000).
  {
    assert (Hkv_cap : k * v <= capacity_pre * 1000).
    { apply Z.mul_le_mono_nonneg; lia. }
    assert (Hcap_prod : capacity_pre * 1000 <= 1000 * 1000).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    replace 1000000 with (1000 * 1000) by lia.
    lia.
  }
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial;
      try reflexivity;
      try eassumption;
      try lia.
    apply MKResidueLoopState_to_MKQueueDropLoopState_predrop with (dp := dp_l_2).
    exact PreH40.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_11 : multipleKnapsack_entail_wit_11.
Proof.
  pre_process.
  Exists qval_l_2. Exists qidx_l_2. Exists old_l_2. Exists dp_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    apply MKQueueDropLoopState_pop_expired_preserves_predrop; auto.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_2 : multipleKnapsack_entail_wit_12_2.
Proof.
  pre_process.
  Exists qval_l_2. Exists qidx_l_2. Exists old_l_2. Exists dp_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    apply MKQueueDropLoopState_empty_exit_to_MKQueueAfterDrop; auto.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_1 : multipleKnapsack_entail_wit_12_1.
Proof.
  pre_process.
  Exists qval_l_2. Exists qidx_l_2. Exists old_l_2. Exists dp_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    eapply MKQueueDropLoopState_nonempty_exit_to_MKQueueAfterDrop
      with (current := current) (curpos := pos); eauto; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_13 : multipleKnapsack_entail_wit_13.
Proof.
  pre_process.
  Exists qval_l_2. Exists qidx_l_2. Exists old_l_2. Exists dp_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    eapply MKQueueAfterDrop_to_MKQueuePendingState_current; eauto; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_14 : multipleKnapsack_entail_wit_14.
Proof.
  pre_process.
  Exists qval_l_2. Exists qidx_l_2. Exists old_l_2. Exists dp_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    eapply MKQueuePendingState_pop_dominated_tail_preserves; eauto; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_1 : multipleKnapsack_entail_wit_15_1.
Proof.
  pre_process.
  Exists (replace_Znth tail current qval_l_2).
  Exists (replace_Znth tail k qidx_l_2).
  Exists old_l_2.
  Exists dp_l_2.
  assert (Hpush :
    MKQueueState old_l_2
      (replace_Znth tail k qidx_l_2)
      (replace_Znth tail current qval_l_2)
      head (tail + 1) r w v cnt (k + 1) capacity_pre).
  {
    eapply MKQueuePendingState_push_to_MKQueueState; eauto; try lia.
    rewrite PreH33, PreH28. reflexivity.
  }
  assert (Hpush_trans :
    MKTransitionValue old_l_2 w v cnt capacity_pre (r + k * w)
      (Znth head (replace_Znth tail current qval_l_2) 0 + k * v)).
  {
    replace (r + k * w) with (r + (k + 1 - 1) * w) by ring.
    replace (Znth head (replace_Znth tail current qval_l_2) 0 + k * v)
      with (Znth head (replace_Znth tail current qval_l_2) 0 +
              (k + 1 - 1) * v) by ring.
    eapply MKQueueState_head_transition; eauto; lia.
  }
  assert (Hpush_bound :
    0 <= Znth head (replace_Znth tail current qval_l_2) 0 + k * v <= 1000000).
  {
    replace (Znth head (replace_Znth tail current qval_l_2) 0 + k * v)
      with (Znth head (replace_Znth tail current qval_l_2) 0 +
              (k + 1 - 1) * v) by ring.
    eapply MKQueueState_head_bound; eauto; lia.
  }
  split_pure_spatial.
  - cancel (IntArray.full q_val_pre (capacity_pre + 1)
              (replace_Znth tail current qval_l_2)).
    cancel (IntArray.full q_idx_pre (capacity_pre + 1)
              (replace_Znth tail k qidx_l_2)).
    cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    cancel (IntArray.full counts_pre n_pre counts_l).
    cancel (IntArray.full dp_pre (capacity_pre + 1) dp_l_2).
    cancel (IntArray.full old_pre (capacity_pre + 1) old_l_2).
  - split_pures; dump_pre_spatial;
      try rewrite Zlength_replace_Znth;
      try assumption;
      try exact Hpush;
      try exact Hpush_bound;
      try (rewrite PreH28; exact Hpush_trans);
      try lia.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_15_2 : multipleKnapsack_entail_wit_15_2.
Proof.
  pre_process.
  Exists (replace_Znth tail current qval_l_2).
  Exists (replace_Znth tail k qidx_l_2).
  Exists old_l_2.
  Exists dp_l_2.
  assert (Hpush :
    MKQueueState old_l_2
      (replace_Znth tail k qidx_l_2)
      (replace_Znth tail current qval_l_2)
      head (tail + 1) r w v cnt (k + 1) capacity_pre).
  {
    eapply MKQueuePendingState_push_to_MKQueueState; eauto; try lia.
    rewrite PreH32, PreH27. reflexivity.
  }
  assert (Hpush_trans :
    MKTransitionValue old_l_2 w v cnt capacity_pre (r + k * w)
      (Znth head (replace_Znth tail current qval_l_2) 0 + k * v)).
  {
    replace (r + k * w) with (r + (k + 1 - 1) * w) by ring.
    replace (Znth head (replace_Znth tail current qval_l_2) 0 + k * v)
      with (Znth head (replace_Znth tail current qval_l_2) 0 +
              (k + 1 - 1) * v) by ring.
    eapply MKQueueState_head_transition; eauto; lia.
  }
  assert (Hpush_bound :
    0 <= Znth head (replace_Znth tail current qval_l_2) 0 + k * v <= 1000000).
  {
    replace (Znth head (replace_Znth tail current qval_l_2) 0 + k * v)
      with (Znth head (replace_Znth tail current qval_l_2) 0 +
              (k + 1 - 1) * v) by ring.
    eapply MKQueueState_head_bound; eauto; lia.
  }
  split_pure_spatial.
  - cancel (IntArray.full q_val_pre (capacity_pre + 1)
              (replace_Znth tail current qval_l_2)).
    cancel (IntArray.full q_idx_pre (capacity_pre + 1)
              (replace_Znth tail k qidx_l_2)).
    cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    cancel (IntArray.full counts_pre n_pre counts_l).
    cancel (IntArray.full dp_pre (capacity_pre + 1) dp_l_2).
    cancel (IntArray.full old_pre (capacity_pre + 1) old_l_2).
  - split_pures; dump_pre_spatial;
      try rewrite Zlength_replace_Znth;
      try assumption;
      try exact Hpush;
      try exact Hpush_bound;
      try (rewrite PreH27; exact Hpush_trans);
      try lia.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_16 : multipleKnapsack_entail_wit_16.
Proof.
  pre_process.
  Exists qval_l_2. Exists qidx_l_2. Exists old_l_2.
  Exists (replace_Znth pos (Znth head qval_l_2 0 + k * v) dp_l_2).
  split_pure_spatial.
  - cancel (IntArray.full dp_pre (capacity_pre + 1)
      (replace_Znth pos (Znth head qval_l_2 0 + k * v) dp_l_2)).
    cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    cancel (IntArray.full counts_pre n_pre counts_l).
    cancel (IntArray.full old_pre (capacity_pre + 1) old_l_2).
    cancel (IntArray.full q_idx_pre (capacity_pre + 1) qidx_l_2).
    cancel (IntArray.full q_val_pre (capacity_pre + 1) qval_l_2).
  - split_pures; dump_pre_spatial; auto; try lia;
      try (rewrite Zlength_replace_Znth; lia).
    + eapply MKItemResiduePrefixProgress_extend_after_dp_write; eauto; lia.
    + eapply MKResidueLoopState_after_dp_write.
      * eapply MKItemResiduePrefixProgress_extend_after_dp_write; eauto; lia.
      * exact PreH44.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_17 : multipleKnapsack_entail_wit_17.
Proof.
  pre_process.
  Exists qval_l_2. Exists qidx_l_2. Exists old_l_2. Exists dp_l_2.
  split_pure_spatial.
  - cancel (IntArray.full weights_pre n_pre weights_l).
    cancel (IntArray.full values_pre n_pre values_l).
    cancel (IntArray.full counts_pre n_pre counts_l).
    cancel (IntArray.full dp_pre (capacity_pre + 1) dp_l_2).
    cancel (IntArray.full old_pre (capacity_pre + 1) old_l_2).
    cancel (IntArray.full q_idx_pre (capacity_pre + 1) qidx_l_2).
    cancel (IntArray.full q_val_pre (capacity_pre + 1) qval_l_2).
  - split_pures; dump_pre_spatial; auto; try lia.
    eapply MKResidueLoopState_to_MKItemResidueProgress_next_residue; eauto; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_19 : multipleKnapsack_entail_wit_19.
Proof.
  pre_process.
  Exists qval_l_2. Exists qidx_l_2. Exists old_l_2. Exists dp_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial; auto.
    eapply MKItemResidueProgress_complete_implies_MKDPTable_next_item.
    + rewrite PreH6. lia.
    + lia.
    + lia.
    + exact PreH15.
    + exact PreH16.
    + exact PreH17.
    + intros idx Hidx.
      specialize (PreH31 idx).
      assert (Hidx_n : 0 <= idx < n_pre) by (rewrite PreH6 in Hidx; exact Hidx).
      specialize (PreH31 Hidx_n).
      lia.
    + exact PreH1.
    + exact PreH27.
    + exact PreH30.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_21 : multipleKnapsack_entail_wit_21.
Proof.
  pre_process.
  Exists qval_l_2. Exists qidx_l_2. Exists old_l_2. Exists dp_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial; auto.
    + assert (i = n_pre) by lia.
      subst i.
      exact PreH15.
    + assert (i = n_pre) by lia.
      subst i.
      eapply MKDPTable_final_capacity_implies_MultipleKnapsackAnswer; eauto.
Qed.
