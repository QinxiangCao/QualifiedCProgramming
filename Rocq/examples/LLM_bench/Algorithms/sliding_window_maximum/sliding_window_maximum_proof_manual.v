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
From SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum Require Import sliding_window_maximum_goal.
From SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum Require Import sliding_window_maximum_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_lib.
Local Open Scope sac.

Lemma proof_of_maxSlidingWindow_entail_wit_1_split_goal_1 : maxSlidingWindow_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_1_split_goal_2 : maxSlidingWindow_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SWMQueueState, SWMQueueEntriesInWindow,
    SWMQueueIndexIncreasing, SWMQueueValueDecreasing,
    SWMQueueCoversWindow.
  repeat split; intros; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_1_split_goal_3 : maxSlidingWindow_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SWMQueueStorageSafe.
  repeat split; intros; try lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_1_split_goal_4 : maxSlidingWindow_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SWMOutputPrefix.
  intros; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_1_split_goal_5 : maxSlidingWindow_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SWMOutputPrefixShape.
  repeat split; try lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_1 : maxSlidingWindow_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_1_split_goal_5.
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_2_split_goal_1 : maxSlidingWindow_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH22; assumption.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_2_split_goal_2 : maxSlidingWindow_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SWMQueueDropLoopState.
  unfold SWMQueueState in PreH21.
  destruct PreH21 as (Hentries & Hindex & Hvalue & Hcovers & Hmax).
  split; [exact Hentries|].
  split; [exact Hindex|].
  split; [exact Hvalue|].
  unfold SWMQueueCoversOpenWindow, SWMQueueCoversWindow in *.
  intros idx Hidx Hwindow.
  apply Hcovers; try assumption; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_2 : maxSlidingWindow_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_2_split_goal_2.
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_3_split_goal_1 : maxSlidingWindow_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply drop_loop_remove_expired_head__head_drop_transitions; eassumption.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_3_split_goal_2 : maxSlidingWindow_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SWMQueueStorageSafe in *.
  destruct PreH20 as (Hlength & Hprocessed & Hrange & Htail & Hentries).
  split; [exact Hlength |].
  split; [exact Hprocessed |].
  split; [lia |].
  split; [exact Htail |].
  intros pos0 Hpos0. apply Hentries. lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_3 : maxSlidingWindow_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_3_split_goal_2.
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_4_1_split_goal_1 : maxSlidingWindow_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_4_1_split_goal_2 : maxSlidingWindow_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH20 as (Hentries & Hindices & Hvalues & Hcovers).
  unfold SWMQueueAfterDrop.
  split.
  - unfold SWMQueueEntriesInOpenWindow.
    intros pos Hpos. exfalso. lia.
  - repeat split; assumption.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_4_1 : maxSlidingWindow_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_4_1_split_goal_2.
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_4_2_split_goal_1 : maxSlidingWindow_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH22; assumption.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_4_2_split_goal_2 : maxSlidingWindow_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply drop_loop_exit_nonexpired__head_drop_transitions; eauto; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_4_2 : maxSlidingWindow_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_4_2_split_goal_2.
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_5_split_goal_1 : maxSlidingWindow_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH20; exact H.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_5_split_goal_2 : maxSlidingWindow_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SWMQueueAfterDrop in PreH19.
  destruct PreH19 as [Hentries [Hindices [Hvalues Hcovers]]].
  unfold SWMQueuePendingState.
  split; [exact Hentries |].
  split; [exact Hindices |].
  split; [exact Hvalues |].
  unfold SWMQueueCoversWithPending.
  intros idx Hidx Hwindow.
  left. apply Hcovers; assumption.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_5 : maxSlidingWindow_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_5_split_goal_2.
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_6_split_goal_1 : maxSlidingWindow_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply SWMQueuePendingState_drop_tail__pending_and_tail_drop; eauto.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_6_split_goal_2 : maxSlidingWindow_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold SWMQueueStorageSafe in *.
  destruct PreH20 as [Hlen [Hprocessed [Hbounds [Htail Hentries]]]].
  repeat split; try assumption; try lia.
  all: pose proof (Hentries pos ltac:(lia)) as Hentry; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_6 : maxSlidingWindow_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_6_split_goal_2.
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_7_1_split_goal_1 : maxSlidingWindow_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_7_1 : maxSlidingWindow_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maxSlidingWindow_entail_wit_7_1_split_goal_1.
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_7_2_split_goal_1 : maxSlidingWindow_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH22; exact H.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_7_2 : maxSlidingWindow_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maxSlidingWindow_entail_wit_7_2_split_goal_1.
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_8_split_goal_1 : maxSlidingWindow_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply replace_Znth_append_bounds__value_loop_exit_and_append;
    eauto; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_8_split_goal_2 : maxSlidingWindow_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply queue_append_state__value_loop_exit_and_append;
    eauto; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_8_split_goal_3 : maxSlidingWindow_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply queue_append_storage__value_loop_exit_and_append.
  - lia.
  - lia.
  - lia.
  - lia.
  - intros pos Hpos.
    rewrite PreH4.
    apply PreH20; exact Hpos.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_8_split_goal_4 : maxSlidingWindow_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH5.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_8 : maxSlidingWindow_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_8_split_goal_3.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_8_split_goal_4.
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_9_split_goal_1 : maxSlidingWindow_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH20 as [_ [_ [_ [_ Hmax]]]].
  replace (i - k_pre + 1) with (i + 1 - k_pre) by lia.
  apply Hmax.
  split; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_9_split_goal_2 : maxSlidingWindow_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH21; exact H.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_9 : maxSlidingWindow_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_9_split_goal_2.
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_10_split_goal_1 : maxSlidingWindow_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH22; exact H.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_10_split_goal_2 : maxSlidingWindow_entail_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite <- PreH14.
  eapply SWMOutputPrefix_app_single__window_output_append;
    [exact PreH18 | exact PreH19 |].
  rewrite PreH14.
  replace (i - k_pre + 1 + k_pre) with (i + 1) by lia.
  exact PreH23.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_10_split_goal_3 : maxSlidingWindow_entail_wit_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite <- PreH14.
  eapply SWMOutputPrefixShape_app_single__window_output_append;
    eauto; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_10 : maxSlidingWindow_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_10_split_goal_1.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_10_split_goal_2.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_10_split_goal_3.
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_11_1_split_goal_1 : maxSlidingWindow_entail_wit_11_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH19; assumption.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_11_1 : maxSlidingWindow_entail_wit_11_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maxSlidingWindow_entail_wit_11_1_split_goal_1.
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_11_2_split_goal_1 : maxSlidingWindow_entail_wit_11_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH21; assumption.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_11_2 : maxSlidingWindow_entail_wit_11_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maxSlidingWindow_entail_wit_11_2_split_goal_1.
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_12_split_goal_1 : maxSlidingWindow_entail_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH21; assumption.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_12 : maxSlidingWindow_entail_wit_12.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maxSlidingWindow_entail_wit_12_split_goal_1.
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_13 : maxSlidingWindow_entail_wit_13.
Proof.
  aggressive_pre_process.
  replace i with n_pre in * by lia.
  replace out_idx with (n_pre - k_pre + 1) in * by lia.
  Exists out_l_2.
  split_pure_spatial.
  - sep_apply (IntArray.seg_to_full out_pre 0 (n_pre - k_pre + 1) out_l_2).
    replace (out_pre + 0 * sizeof(INT)) with out_pre by lia.
    replace (n_pre - k_pre + 1 - 0) with (n_pre - k_pre + 1) by lia.
    cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    unfold SlidingWindowMaximum.
    destruct PreH18 as (_ & _ & _ & Houtlen).
    split.
    + lia.
    + intros idx Hidx.
      apply (PreH19 idx).
      lia.
Qed. 
