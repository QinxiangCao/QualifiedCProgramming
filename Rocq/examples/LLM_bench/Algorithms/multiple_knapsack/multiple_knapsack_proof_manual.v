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
From SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack Require Import multiple_knapsack_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_lib.
Local Open Scope sac.

Lemma proof_of_multipleKnapsack_safety_wit_12_split_goal_1 : multipleKnapsack_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKDPValueBound in PreH38.
  destruct PreH38 as [_ Hbound].
  specialize (Hbound pos ltac:(lia)).
  assert (0 <= k * v) by nia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_multipleKnapsack_safety_wit_12_split_goal_2 : multipleKnapsack_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKDPValueBound in PreH38.
  destruct PreH38 as [_ Hbound].
  specialize (Hbound pos ltac:(lia)).
  assert (k * v <= 1001000) by nia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_multipleKnapsack_safety_wit_12 : multipleKnapsack_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_safety_wit_12_split_goal_2.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_1_split_goal_1 : multipleKnapsack_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH9.
  lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_1_split_goal_2 : multipleKnapsack_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKZeroPrefixSemantics.
  intros; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_1_split_goal_3 : multipleKnapsack_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKZeroPrefixSafety.
  split; [lia | reflexivity].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_1_split_goal_4 : multipleKnapsack_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_1 : multipleKnapsack_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_2_split_goal_1 : multipleKnapsack_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKZeroPrefixSemantics in *.
  intros cap Hcap.
  destruct (Z.eq_dec cap j) as [-> | Hneq].
  - rewrite app_Znth2 by lia.
    rewrite PreH9.
    replace (j - j) with 0 by lia.
    rewrite Znth0_cons.
    reflexivity.
  - rewrite app_Znth1 by (rewrite PreH9; lia).
    apply PreH14.
    lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_2_split_goal_2 : multipleKnapsack_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKZeroPrefixSafety in *.
  destruct PreH13 as [Hj Hlen].
  split; [lia |].
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_2_split_goal_3 : multipleKnapsack_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_2 : multipleKnapsack_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_2_split_goal_3.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_3 : multipleKnapsack_entail_wit_3.
Proof.
  aggressive_pre_process.
  assert (Hj : j = capacity_pre + 1) by lia.
  subst j.
  Exists dp_l_2.
  split_pure_spatial.
  - replace (Zlength dp_l_2) with (capacity_pre + 1) by lia.
    sep_apply (IntArray.seg_to_full dp_pre 0 (capacity_pre + 1) dp_l_2).
    replace (dp_pre + 0 * sizeof(INT)) with dp_pre by lia.
    replace (capacity_pre + 1 - 0) with (capacity_pre + 1) by lia.
    cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption;
      [ replace (capacity_pre + 1) with (Zlength dp_l_2) by lia;
        exact PreH13
      | replace (capacity_pre + 1) with (Zlength dp_l_2) by lia;
        exact PreH14
      | unfold MKDPTableSafety, MKZeroPrefixSafety in *;
        destruct PreH13 as [Hhi Hlen];
        repeat split; try lia
      | unfold MKDPTableSemantics;
        intros cap Hcap;
        rewrite PreH14 by lia;
        apply MultipleKnapsackPrefixAnswer_zero_items;
        lia ].
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_4_split_goal_1 : multipleKnapsack_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH14.
  exact H.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_4_split_goal_2 : multipleKnapsack_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKScratchArraysSafety in PreH9.
  tauto.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_4_split_goal_3 : multipleKnapsack_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKScratchArraysSafety in PreH9.
  tauto.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_4_split_goal_4 : multipleKnapsack_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKScratchArraysSafety in PreH9.
  tauto.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_4 : multipleKnapsack_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_4_split_goal_4.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_5_split_goal_1 : multipleKnapsack_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH17.
  exact H.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_5_split_goal_2 : multipleKnapsack_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKCopyPrefixSemantics.
  intros cap Hcap.
  lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_5_split_goal_3 : multipleKnapsack_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKCopyPrefixSafety.
  repeat split; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_5 : multipleKnapsack_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_5_split_goal_3.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6_split_goal_1 : multipleKnapsack_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKCopyPrefixSemantics in *.
  intros cap Hcap.
  destruct (Z.eq_dec cap j) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by lia. reflexivity.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply PreH20. lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6_split_goal_2 : multipleKnapsack_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKCopyPrefixSafety in *.
  destruct PreH19 as (Hj & Hsrc & Hdst).
  repeat split; try lia; try assumption.
  rewrite Zlength_replace_Znth. exact Hdst.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6_split_goal_3 : multipleKnapsack_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6 : multipleKnapsack_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_6_split_goal_2.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_6_split_goal_3.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_7_split_goal_1 : multipleKnapsack_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH21. assumption.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_7_split_goal_2 : multipleKnapsack_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKItemResidueProgressSemantics.
  split.
  - intros rem k pos Hpos Hrem. lia.
  - intros rem k pos Hpos Hrem Hk Hpos_range.
    unfold MKCopyPrefixSemantics in PreH20.
    symmetry. apply PreH20. lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_7_split_goal_3 : multipleKnapsack_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH21 i ltac:(lia)) as Hitem.
  unfold MKItemResidueProgressSafety.
  unfold MKCopyPrefixSafety in PreH19.
  destruct PreH19 as (_ & Hdp & Hold).
  repeat split; try lia; assumption.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_7_split_goal_4 : multipleKnapsack_entail_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace j with (capacity_pre + 1) in PreH20 by lia.
  exact PreH20.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_7_split_goal_5 : multipleKnapsack_entail_wit_7_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace j with (capacity_pre + 1) in PreH19 by lia.
  exact PreH19.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_7_split_goal_6 : multipleKnapsack_entail_wit_7_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH21 i ltac:(lia)) as Hitem.
  assert (Hdp : MKDPTable weights_l values_l counts_l i capacity_pre dp_l_2).
  { unfold MKDPTable, MKDPTableSafety, MKDPTableSemantics in *.
    tauto. }
  assert (Hcopy : MKCopyPrefix dp_l_2 old_l_2 (capacity_pre + 1) capacity_pre).
  { replace j with (capacity_pre + 1) in PreH19, PreH20 by lia.
    unfold MKCopyPrefix, MKCopyPrefixSafety, MKCopyPrefixSemantics in *.
    tauto. }
  eapply MKDPTable_implies_MKTransitionValueBound_for_current_item;
    try eassumption; try lia.
  intros idx Hidx.
  specialize (PreH21 idx).
  rewrite PreH6 in Hidx.
  specialize (PreH21 Hidx).
  tauto.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_7_split_goal_7 : multipleKnapsack_entail_wit_7_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hdp : MKDPTable weights_l values_l counts_l i capacity_pre dp_l_2).
  { unfold MKDPTable, MKDPTableSafety, MKDPTableSemantics in *.
    tauto. }
  assert (Hcopy : MKCopyPrefix dp_l_2 old_l_2 (capacity_pre + 1) capacity_pre).
  { replace j with (capacity_pre + 1) in PreH19, PreH20 by lia.
    unfold MKCopyPrefix, MKCopyPrefixSafety, MKCopyPrefixSemantics in *.
    tauto. }
  eapply MKDPTable_copy_implies_MKDPValueBound_under_global_item_bounds;
    try eassumption; try lia.
  intros idx Hidx.
  specialize (PreH21 idx).
  rewrite PreH6 in Hidx.
  specialize (PreH21 Hidx).
  tauto.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_7 : multipleKnapsack_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_7_split_goal_3.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_7_split_goal_4.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_7_split_goal_5.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_7_split_goal_6.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_7_split_goal_7.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_8_split_goal_1 : multipleKnapsack_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros; eauto.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_8_split_goal_2 : multipleKnapsack_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKDPTableSemantics, MKCopyPrefixSemantics in *.
  intros cap Hcap.
  rewrite (PreH28 cap ltac:(lia)).
  apply PreH24; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_8_split_goal_3 : multipleKnapsack_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKDPTableSafety, MKCopyPrefixSafety in *.
  tauto.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_8 : multipleKnapsack_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_8_split_goal_3.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_9_split_goal_1 : multipleKnapsack_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros; eauto.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_9_split_goal_2 : multipleKnapsack_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKResidueLoopSemantics, MKQueueResultSemantics,
    MKQueueEntriesValidForResult, MKQueueIndexIncreasing,
    MKQueueValueDecreasing, MKQueueCoversResultWindow,
    MKQueueResultValueBound in *.
  repeat split; intros; try lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_9_split_goal_3 : multipleKnapsack_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKResidueLoopSafety, MKQueueStorageSafety,
    MKItemResidueProgressSafety in *.
  repeat split; try lia; assumption.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_9_split_goal_4 : multipleKnapsack_entail_wit_9_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKItemResiduePrefixSemantics, MKItemResidueProgressSemantics in *.
  destruct PreH33 as [Hdone Hsame].
  split.
  - intros; lia.
  - intros pos Hpos.
    split.
    + intros rem t Hpos_eq Hrem Ht.
      eapply Hdone; eauto.
    + intros rem t Hpos_eq Hrem Ht Hcase.
      eapply Hsame; eauto.
      lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_9_split_goal_5 : multipleKnapsack_entail_wit_9_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKItemResiduePrefixSafety, MKItemResidueProgressSafety in *.
  repeat split; try lia; assumption.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_9 : multipleKnapsack_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_9_split_goal_3.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_9_split_goal_4.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_9_split_goal_5.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_10_split_goal_1 : multipleKnapsack_entail_wit_10_split_goal_1.
Proof.
  aggressive_pre_process.
  apply PreH44.
  exact H.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10_split_goal_2 : multipleKnapsack_entail_wit_10_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold MKResidueLoopSemantics in PreH43.
  destruct PreH43 as [_ Hqueue].
  unfold MKQueueResultSemantics in Hqueue.
  destruct Hqueue as (Hvalid & Hinc & Hdec & Hcover & Hbound & _).
  unfold MKQueueDropSemantics.
  split; [exact Hvalid|].
  split; [exact Hinc|].
  split; [exact Hdec|].
  split.
  - unfold MKQueueCoversWindow.
    intros cand Hcand0 Hcandlt Hcandlo Hcandlen.
    unfold MKQueueCoversResultWindow in Hcover.
    apply Hcover; lia.
  - exact Hbound.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10_split_goal_3 : multipleKnapsack_entail_wit_10_split_goal_3.
Proof.
  aggressive_pre_process.
  unfold MKResidueLoopSafety in PreH42.
  unfold MKQueueDropSafety, MKQueueStorageSafety.
  destruct PreH42 as (Hr & Hk & Hhead & Htail & Hold & _Hdp & Hqidx & Hqval).
  repeat split; try assumption; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10_split_goal_4 : multipleKnapsack_entail_wit_10_split_goal_4.
Proof.
  aggressive_pre_process.
  unfold MKDPValueBound in PreH38.
  destruct PreH38 as [_ Hbound].
  specialize (Hbound pos ltac:(lia)).
  assert (Hpos : pos = r + k * w) by lia.
  rewrite <- Hpos.
  pose proof (Z.sub_add (k * v) (Znth pos old_l 0)) as Hcancel.
  rewrite Hcancel.
  lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10_split_goal_5 : multipleKnapsack_entail_wit_10_split_goal_5.
Proof.
  aggressive_pre_process.
  unfold MKDPValueBound in PreH38.
  destruct PreH38 as [_ Hbound].
  specialize (Hbound pos ltac:(lia)).
  assert (Hpos : pos = r + k * w) by lia.
  rewrite <- Hpos.
  pose proof (Z.sub_add (k * v) (Znth pos old_l 0)) as Hcancel.
  rewrite Hcancel.
  lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10_split_goal_6 : multipleKnapsack_entail_wit_10_split_goal_6.
Proof.
  aggressive_pre_process.
  unfold multiple_knapsack_lib.MKDPValueBound in PreH38.
  destruct PreH38 as [_ Hbound].
  specialize (Hbound pos (conj PreH30 PreH1)).
  assert (Hkv : 0 <= k * v) by nia.
  rewrite <- PreH27.
  lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10_split_goal_7 : multipleKnapsack_entail_wit_10_split_goal_7.
Proof.
  aggressive_pre_process.
  unfold multiple_knapsack_lib.MKDPValueBound in PreH38.
  destruct PreH38 as [_ Hbound].
  specialize (Hbound pos (conj PreH30 PreH1)).
  pose proof
    (Z.mul_le_mono_nonneg_l 1 w k PreH28 PreH21) as Hkw.
  rewrite Z.mul_1_r in Hkw.
  assert (Hkcap : k <= capacity_pre) by lia.
  assert (Hkv : k * v <= 1000000) by nia.
  rewrite <- PreH27.
  lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10 : multipleKnapsack_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_10_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_10_split_goal_2.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_10_split_goal_3.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_10_split_goal_4.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_10_split_goal_5.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_10_split_goal_6.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_10_split_goal_7.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_11_split_goal_1 : multipleKnapsack_entail_wit_11_split_goal_1.
Proof.
  aggressive_pre_process.
  unfold MKQueueDropSemantics in *.
  destruct PreH49 as (Hvalid & Hinc & Hdec & Hcover & Hbound).
  split.
  - intros p Hp. apply Hvalid. lia.
  - split.
    + intros p q Hp. apply Hinc. lia.
    + split.
      * intros p q Hp. apply Hdec. lia.
      * split.
        -- intros cand Hcand0 Hcandlt Hcandlo Hcandlen.
           destruct (Hcover cand Hcand0 Hcandlt Hcandlo Hcandlen)
             as (p & Hp_range & Hcand_p & Hp_k & Hp_val).
           destruct Hp_range as [Hhead_p Hp_tail].
           exists p.
           split.
           ++ destruct (Z.eq_dec p head) as [-> | Hneq]; split; lia.
           ++ split; [exact Hcand_p|].
              split; [exact Hp_k|exact Hp_val].
        -- intros p Hp. apply Hbound. lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_11_split_goal_2 : multipleKnapsack_entail_wit_11_split_goal_2.
Proof.
  aggressive_pre_process.
  unfold MKQueueDropSafety, MKQueueStorageSafety in *.
  destruct PreH48 as (Hr & Hk & Hhead & Htail & Htail_len & Hqidx & Hqval & Hold).
  repeat split; try assumption; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_11 : multipleKnapsack_entail_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_11_split_goal_2.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_12_1_split_goal_1 : multipleKnapsack_entail_wit_12_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH49 idx H).
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_1_split_goal_2 : multipleKnapsack_entail_wit_12_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKQueueDropSemantics in PreH48.
  unfold MKQueueAfterDropSemantics.
  destruct PreH48 as (Hentries & Hinc & Hdec & Hcovers & Hbound).
  repeat split; try assumption;
    unfold MKQueueEntriesValidAfterDrop, MKQueueIndexIncreasing,
      MKQueueValueDecreasing, MKQueueCoversWindow,
      MKQueueResultValueBound in *; intros; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_1 : multipleKnapsack_entail_wit_12_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_12_1_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_12_1_split_goal_2.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_12_2_split_goal_1 : multipleKnapsack_entail_wit_12_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH50 idx H).
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_2_split_goal_2 : multipleKnapsack_entail_wit_12_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hstate : MKQueueDropLoopState old_l_2 qidx_l_2 qval_l_2
    head tail r w v cnt k capacity_pre).
  {
    unfold MKQueueDropLoopState, MKQueueDropSafety, MKQueueStorageSafety,
      MKQueueDropSemantics in *.
    intuition.
  }
  pose proof (MKQueueDropLoopState_nonempty_exit_to_MKQueueAfterDrop
    old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH1 PreH2 PreH24 PreH16 PreH17 PreH22 PreH28 ltac:(lia) PreH33 PreH37
    PreH45 Hstate) as Hafter.
  unfold MKQueueAfterDrop, MKQueueAfterDropSemantics in *.
  intuition.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_2 : multipleKnapsack_entail_wit_12_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_12_2_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_12_2_split_goal_2.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_13_split_goal_1 : multipleKnapsack_entail_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH49 idx H).
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_13_split_goal_2 : multipleKnapsack_entail_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKQueueAfterDropSemantics in PreH48.
  unfold MKQueuePendingSemantics.
  destruct PreH48 as (Hentries & Hinc & Hdec & Hcovers & Hbound).
  split; [exact Hentries|].
  split; [exact Hinc|].
  split; [exact Hdec|].
  split.
  - unfold MKQueueCoversWithPending, MKQueueCoversWindow in *.
    intros. left. eauto.
  - split; [exact Hbound|]. lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_13 : multipleKnapsack_entail_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_13_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_13_split_goal_2.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_14_split_goal_1 : multipleKnapsack_entail_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKQueuePendingSemantics in PreH50.
  unfold MKQueuePendingSemantics.
  destruct PreH50 as (Hentries & Hinc & Hdec & Hcovers & Hbound & Hcurrent).
  split.
  - unfold MKQueueEntriesValidAfterDrop in *.
    intros p Hp. apply Hentries. lia.
  - split.
    + unfold MKQueueIndexIncreasing in *.
      intros p q Hpq. apply Hinc. lia.
    + split.
      * unfold MKQueueValueDecreasing in *.
        intros p q Hpq. apply Hdec. lia.
      * split.
        -- unfold MKQueueCoversWithPending in *.
           intros cand Hcand0 Hcandk Hwindow Hlen.
           specialize (Hcovers cand Hcand0 Hcandk Hwindow Hlen).
           destruct Hcovers as [Hex | Hcur]; [|right; exact Hcur].
           destruct Hex as (p & Hp & Hpcand & Hpk & Hpval).
           destruct (Z_lt_ge_dec p (tail - 1)) as [Hplt | Hpge].
           ++ left. exists p. lia.
           ++ right.
              assert (p = tail - 1) by lia. subst p. lia.
        -- split.
           ++ unfold MKQueueResultValueBound in *.
              intros p Hp. apply Hbound. lia.
           ++ exact Hcurrent.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_14_split_goal_2 : multipleKnapsack_entail_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKQueueDropSafety in *.
  unfold MKQueueStorageSafety in *.
  destruct PreH49 as (Hr & Hk & Hstorage).
  destruct Hstorage as (Hheadtail & Htailk & Htailidx & Hidxlen & Hvallen & Holdlen).
  repeat split; try assumption; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_14 : multipleKnapsack_entail_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_14_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_14_split_goal_2.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_15_1_split_goal_1 : multipleKnapsack_entail_wit_15_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH50.
  exact H.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_1_split_goal_2 : multipleKnapsack_entail_wit_15_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (head = tail) by lia.
  subst head.
  rewrite Znth_replace_Znth_Same by (rewrite PreH12; lia).
  lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_1_split_goal_3 : multipleKnapsack_entail_wit_15_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (head = tail) by lia.
  subst head.
  rewrite Znth_replace_Znth_Same by (rewrite PreH12; lia).
  lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_1_split_goal_4 : multipleKnapsack_entail_wit_15_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (MKQueuePending_push_complete_outcome__g06
    old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH27 PreH48 PreH49 PreH32 (conj PreH30 PreH31) PreH25 PreH29
    ltac:(intros; lia)) as (_ & _ & _ & _ & Htransition).
  rewrite PreH27 in Htransition.
  exact Htransition.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_1_split_goal_5 : multipleKnapsack_entail_wit_15_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (MKQueuePending_push_complete_outcome__g06
    old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH27 PreH48 PreH49 PreH32 (conj PreH30 PreH31) PreH25 PreH29
    ltac:(intros; lia)) as (_ & _ & _ & Htransition_safe & _).
  rewrite PreH27 in Htransition_safe.
  exact Htransition_safe.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_1_split_goal_6 : multipleKnapsack_entail_wit_15_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (MKQueuePending_push_complete_outcome__g06
    old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH27 PreH48 PreH49 PreH32 (conj PreH30 PreH31) PreH25 PreH29
    ltac:(intros; lia)) as (_ & Hresult & _).
  exact Hresult.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_1_split_goal_7 : multipleKnapsack_entail_wit_15_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (MKQueuePending_push_complete_outcome__g06
    old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH27 PreH48 PreH49 PreH32 (conj PreH30 PreH31) PreH25 PreH29
    ltac:(intros; lia)) as (Hresult & _).
  exact Hresult.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_1_split_goal_8 : multipleKnapsack_entail_wit_15_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH12.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_1_split_goal_9 : multipleKnapsack_entail_wit_15_1_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH11.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_1 : multipleKnapsack_entail_wit_15_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_1_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_1_split_goal_2.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_1_split_goal_3.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_1_split_goal_4.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_1_split_goal_5.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_1_split_goal_6.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_1_split_goal_7.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_1_split_goal_8.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_1_split_goal_9.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_15_2_split_goal_1 : multipleKnapsack_entail_wit_15_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH51.
  lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_2_split_goal_2 : multipleKnapsack_entail_wit_15_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (MKQueuePending_push_complete_outcome__g06
    old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH28 PreH49 PreH50 PreH33 (conj PreH31 PreH32) PreH26 PreH30
    ltac:(intros; exact PreH1)) as (_ & _ & Hbound & _).
  exact (proj2 Hbound).
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_2_split_goal_3 : multipleKnapsack_entail_wit_15_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (MKQueuePending_push_complete_outcome__g06
    old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH28 PreH49 PreH50 PreH33 (conj PreH31 PreH32) PreH26 PreH30
    ltac:(intros; exact PreH1)) as (_ & _ & Hbound & _).
  exact (proj1 Hbound).
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_2_split_goal_4 : multipleKnapsack_entail_wit_15_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (MKQueuePending_push_complete_outcome__g06
    old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH28 PreH49 PreH50 PreH33 (conj PreH31 PreH32) PreH26 PreH30
    ltac:(intros; exact PreH1)) as (_ & _ & _ & _ & Htransition).
  rewrite PreH28 in Htransition.
  exact Htransition.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_2_split_goal_5 : multipleKnapsack_entail_wit_15_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MKTransitionSafety.
  repeat split; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_2_split_goal_6 : multipleKnapsack_entail_wit_15_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (MKQueuePending_push_complete_outcome__g06
    old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH28 PreH49 PreH50 PreH33 (conj PreH31 PreH32) PreH26 PreH30
    ltac:(intros; exact PreH1)) as (_ & Hresult & _).
  exact Hresult.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_2_split_goal_7 : multipleKnapsack_entail_wit_15_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (MKQueuePending_push_complete_outcome__g06
    old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos
    PreH28 PreH49 PreH50 PreH33 (conj PreH31 PreH32) PreH26 PreH30
    ltac:(intros; exact PreH1)) as (Hresult & _).
  exact Hresult.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_2_split_goal_8 : multipleKnapsack_entail_wit_15_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH13.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_2_split_goal_9 : multipleKnapsack_entail_wit_15_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH12.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15_2 : multipleKnapsack_entail_wit_15_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_2_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_2_split_goal_2.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_2_split_goal_3.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_2_split_goal_4.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_2_split_goal_5.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_2_split_goal_6.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_2_split_goal_7.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_2_split_goal_8.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_15_2_split_goal_9.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_16_split_goal_1 : multipleKnapsack_entail_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH52; assumption.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_16_split_goal_2 : multipleKnapsack_entail_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (MKResidueLoopSemantics_after_dp_write__g09
    old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w v cnt k head tail capacity_pre pos
    (Znth head qval_l_2 0 + k * v)
    PreH14 ltac:(lia) PreH26 (conj PreH29 PreH30) PreH8 PreH45 PreH47 PreH49)
    as Hstep.
  rewrite PreH26 in Hstep.
  exact Hstep.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_16_split_goal_3 : multipleKnapsack_entail_wit_16_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (MKResidueLoopSafety_after_dp_write__g09
    old_l_2 dp_l_2 qidx_l_2 qval_l_2 r w k head tail capacity_pre pos
    (Znth head qval_l_2 0 + k * v) PreH8 PreH46) as Hstep.
  rewrite PreH26 in Hstep.
  exact Hstep.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_16_split_goal_4 : multipleKnapsack_entail_wit_16_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (MKItemResiduePrefixSemantics_after_dp_write__g09
    old_l_2 dp_l_2 r w v cnt k capacity_pre pos
    (Znth head qval_l_2 0 + k * v)
    ltac:(lia) PreH14 PreH15 PreH26 (conj PreH29 PreH30) PreH8 PreH45 PreH49)
    as Hstep.
  rewrite PreH26 in Hstep.
  exact Hstep.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_16_split_goal_5 : multipleKnapsack_entail_wit_16_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (MKItemResiduePrefixSafety_after_dp_write__g09
    old_l_2 dp_l_2 r w cnt k capacity_pre pos
    (Znth head qval_l_2 0 + k * v) PreH8 PreH44) as Hstep.
  rewrite PreH26 in Hstep.
  exact Hstep.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_16_split_goal_6 : multipleKnapsack_entail_wit_16_split_goal_6.
Proof. LLM_pre_process ltac:(lia || int_auto). Qed.

Lemma proof_of_multipleKnapsack_entail_wit_16_split_goal_7 : multipleKnapsack_entail_wit_16_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth; exact PreH8.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_16 : multipleKnapsack_entail_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_16_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_16_split_goal_2.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_16_split_goal_3.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_16_split_goal_4.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_16_split_goal_5.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_16_split_goal_6.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_16_split_goal_7.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_17_split_goal_1 : multipleKnapsack_entail_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH44; assumption.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_17_split_goal_2 : multipleKnapsack_entail_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply MKItemResidueProgressSemantics_next_residue__g09; eauto; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_17_split_goal_3 : multipleKnapsack_entail_wit_17_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply MKItemResidueProgressSafety_next_residue__g09; eauto.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_17 : multipleKnapsack_entail_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_17_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_17_split_goal_2.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_17_split_goal_3.
Qed. 

Lemma proof_of_multipleKnapsack_entail_wit_18_split_goal_1 : multipleKnapsack_entail_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH38; assumption.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_18 : multipleKnapsack_entail_wit_18.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_multipleKnapsack_entail_wit_18_split_goal_1.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_19_split_goal_1 : multipleKnapsack_entail_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH33; assumption.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_19_split_goal_2 : multipleKnapsack_entail_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hweights_pos :
    forall idx, 0 <= idx < Zlength weights_l -> 1 <= Znth idx weights_l 0).
  { intros idx Hidx.
    pose proof (PreH33 idx ltac:(lia)) as Hbounds.
    tauto. }
  pose proof (MKItemResidue_complete_table__g09
    weights_l values_l counts_l i capacity_pre old_l_2 dp_l_2 r w v cnt
    ltac:(lia) ltac:(lia) ltac:(lia) PreH15 PreH16 PreH17 Hweights_pos
    PreH1 PreH27 PreH28 PreH31 PreH32) as Hnext.
  exact (proj2 Hnext).
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_19_split_goal_3 : multipleKnapsack_entail_wit_19_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hweights_pos :
    forall idx, 0 <= idx < Zlength weights_l -> 1 <= Znth idx weights_l 0).
  { intros idx Hidx.
    pose proof (PreH33 idx ltac:(lia)) as Hbounds.
    tauto. }
  pose proof (MKItemResidue_complete_table__g09
    weights_l values_l counts_l i capacity_pre old_l_2 dp_l_2 r w v cnt
    ltac:(lia) ltac:(lia) ltac:(lia) PreH15 PreH16 PreH17 Hweights_pos
    PreH1 PreH27 PreH28 PreH31 PreH32) as Hnext.
  exact (proj1 Hnext).
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_19 : multipleKnapsack_entail_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_19_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_19_split_goal_2.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_19_split_goal_3.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_20_split_goal_1 : multipleKnapsack_entail_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH25; assumption.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_20 : multipleKnapsack_entail_wit_20.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_multipleKnapsack_entail_wit_20_split_goal_1.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_21_split_goal_1 : multipleKnapsack_entail_wit_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  apply (MKDPTable_final_capacity_implies_MultipleKnapsackAnswer
    weights_l values_l counts_l capacity_pre dp_l_2 n_pre);
    try assumption; try lia.
  apply MKDPTable_from_safety_semantics__g10; assumption.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_21_split_goal_2 : multipleKnapsack_entail_wit_21_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  exact PreH16.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_21_split_goal_3 : multipleKnapsack_entail_wit_21_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia.
  subst i.
  exact PreH15.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_21 : multipleKnapsack_entail_wit_21.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_21_split_goal_1.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_21_split_goal_2.
  - Goal_apply proof_of_multipleKnapsack_entail_wit_21_split_goal_3.
Qed.
