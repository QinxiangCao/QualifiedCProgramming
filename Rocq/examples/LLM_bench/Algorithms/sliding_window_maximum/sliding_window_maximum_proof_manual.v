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
Require Import AUXLib.MonotonicList.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_lib.
Local Open Scope sac.
Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg.

Ltac swm_forall :=
  repeat match goal with
  | H : Forall ?P (sublist ?a ?b ?l) |- _ =>
    rewrite (SWM_Forall_sublist P l a b ltac:(lia) ltac:(lia)) in H
  end;
  try match goal with
  | |- Forall ?P (sublist ?a ?b ?l) =>
    apply (proj2 (SWM_Forall_sublist P l a b ltac:(lia)
      ltac:(try rewrite Zlength_replace_Znth; lia)))
  end;
  intros.
Ltac swm_arith :=
  swm_forall;
  repeat match goal with
  | H : forall i : Z, _ -> _ |- context [Znth ?j _ 0] =>
    let B := fresh "bound" in pose proof (H j ltac:(lia)) as B; clear H
  end;
  solve [lia | int_auto | rewrite Zlength_app_cons; lia].

Lemma swm_after_drop_pending l q h t i k :
  SWMQueueAfterDrop l q h t i k -> SWMQueuePendingState l q h t i k.
Proof.
  intros (Hentries & Hindices & Hvalues & Hcovers).
  unfold SWMQueuePendingState. split; [exact Hentries |].
  split; [exact Hindices |]. split; [exact Hvalues |].
  unfold SWMQueueCoversWithPending. intros idx Hidx Hwindow.
  left. apply Hcovers; assumption.
Qed.



Lemma proof_of_maxSlidingWindow_entail_wit_1 : maxSlidingWindow_entail_wit_1.
Proof.
  unfold maxSlidingWindow_entail_wit_1. right. intros.
  sep_apply (IntArray.undef_full_split_to_undef_seg (&("q")) n_pre 100000); try lia.
  entailer!.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_2 : maxSlidingWindow_entail_wit_2.
Proof.
  unfold maxSlidingWindow_entail_wit_2. right. intros.
  rewrite Zlength_app_cons. entailer!.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_3 : maxSlidingWindow_entail_wit_3.
Proof.
  unfold maxSlidingWindow_entail_wit_3. right. intros.
  replace z with n_pre in * by lia. Exists q_init.
  sep_apply (IntArray.seg_to_full (&("q")) 0 n_pre q_init).
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r. repeat rewrite Z.sub_0_r.
  assert (Hqueue : SWMQueueState l q_init 0 0 0 k_pre).
  { unfold SWMQueueState, SWMQueueEntriesInWindow,
      SWMQueueIndexIncreasing, SWMQueueValueDecreasing, SWMQueueCoversWindow.
    rewrite Zsublist_nil by lia. split; [constructor |].
    repeat split; intros; lia. }
  assert (Hout : SWMOutputPrefix l k_pre 0 (@nil Z)) by
    (unfold SWMOutputPrefix; intros; lia).
  rewrite Zsublist_nil by lia.
  entailer!; try constructor; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_4_split_goal_1 : maxSlidingWindow_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : SWMQueueState _ _ _ _ _ _ |- _ =>
    destruct H as (Hentries & Hindex & Hvalue & Hcovers & Hmax) end.
  unfold SWMQueueDropLoopState. repeat split; try assumption.
  unfold SWMQueueCoversOpenWindow, SWMQueueCoversWindow in *.
  intros idx Hidx Hwindow. apply Hcovers; try assumption; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_4 : maxSlidingWindow_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maxSlidingWindow_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_5_split_goal_1 : maxSlidingWindow_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: swm_arith.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_5_split_goal_2 : maxSlidingWindow_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: swm_arith.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_5_split_goal_3 : maxSlidingWindow_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply drop_loop_remove_expired_head__head_drop_transitions; eauto; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_5 : maxSlidingWindow_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_5_split_goal_3.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_6_1_split_goal_1 : maxSlidingWindow_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply swm_after_drop_pending.
  match goal with H : SWMQueueDropLoopState _ _ _ _ _ _ |- _ =>
    destruct H as (Hentries & Hindices & Hvalues & Hcovers) end.
  unfold SWMQueueAfterDrop. split.
  - unfold SWMQueueEntriesInOpenWindow. rewrite Zsublist_nil by lia. constructor.
  - repeat split; assumption.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_6_1 : maxSlidingWindow_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_maxSlidingWindow_entail_wit_6_1_split_goal_1.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_6_2_split_goal_1 : maxSlidingWindow_entail_wit_6_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: swm_arith.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_6_2_split_goal_2 : maxSlidingWindow_entail_wit_6_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply swm_after_drop_pending.
  eapply drop_loop_exit_nonexpired__head_drop_transitions; eauto; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_6_2 : maxSlidingWindow_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_6_2_split_goal_1.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_6_2_split_goal_2.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_7_split_goal_1 : maxSlidingWindow_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: swm_arith.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_7_split_goal_2 : maxSlidingWindow_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: swm_arith.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_7_split_goal_3 : maxSlidingWindow_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: swm_arith.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_7_split_goal_4 : maxSlidingWindow_entail_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply SWMQueuePendingState_drop_tail__pending_and_tail_drop; eauto; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_7 : maxSlidingWindow_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_7_split_goal_3.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_7_split_goal_4.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_1 : maxSlidingWindow_entail_wit_8_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  swm_forall.
  match goal with |- context [Znth ?pos (replace_Znth ?tail ?i ?q) 0] =>
    destruct (Z.eq_dec pos tail) as [Heq | Hne];
    [subst pos; rewrite Znth_replace_Znth_Same by lia; lia |
     rewrite Znth_replace_Znth_Diff by lia; swm_arith]
  end.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_2 : maxSlidingWindow_entail_wit_8_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  swm_forall.
  match goal with |- context [Znth ?pos (replace_Znth ?tail ?i ?q) 0] =>
    destruct (Z.eq_dec pos tail) as [Heq | Hne];
    [subst pos; rewrite Znth_replace_Znth_Same by lia; lia |
     rewrite Znth_replace_Znth_Diff by lia; swm_arith]
  end.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_3 : maxSlidingWindow_entail_wit_8_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply queue_append_state__value_loop_exit_and_append; eauto; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_4 : maxSlidingWindow_entail_wit_8_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_8_1 : maxSlidingWindow_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_1.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_2.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_3.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_8_1_split_goal_4.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_1 : maxSlidingWindow_entail_wit_8_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  swm_forall.
  match goal with |- context [Znth ?pos (replace_Znth ?tail ?i ?q) 0] =>
    destruct (Z.eq_dec pos tail) as [Heq | Hne];
    [subst pos; rewrite Znth_replace_Znth_Same by lia; lia |
     rewrite Znth_replace_Znth_Diff by lia; swm_arith]
  end.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_2 : maxSlidingWindow_entail_wit_8_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  swm_forall.
  match goal with |- context [Znth ?pos (replace_Znth ?tail ?i ?q) 0] =>
    destruct (Z.eq_dec pos tail) as [Heq | Hne];
    [subst pos; rewrite Znth_replace_Znth_Same by lia; lia |
     rewrite Znth_replace_Znth_Diff by lia; swm_arith]
  end.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_3 : maxSlidingWindow_entail_wit_8_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply queue_append_state__value_loop_exit_and_append; eauto; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_4 : maxSlidingWindow_entail_wit_8_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_8_2 : maxSlidingWindow_entail_wit_8_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_1.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_2.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_3.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_8_2_split_goal_4.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_9_split_goal_1 : maxSlidingWindow_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with H : SWMQueueState _ _ _ _ _ _ |- _ =>
    destruct H as (_ & _ & _ & _ & Hmax) end.
  replace (i-k_pre+1) with (i+1-k_pre) by lia.
  apply Hmax. split; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_9_split_goal_2 : maxSlidingWindow_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: swm_arith.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_9_split_goal_3 : maxSlidingWindow_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: swm_arith.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_9 : maxSlidingWindow_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_9_split_goal_3.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_10_1_split_goal_1 : maxSlidingWindow_entail_wit_10_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply SWMOutputPrefix_app_single__window_output_append.
  - unfold SWMOutputPrefixShape. repeat split; lia.
  - match goal with H : SWMOutputPrefix _ _ _ _ |- _ =>
      replace (i-k_pre+1) with out_idx by lia; exact H end.
  - replace (i-k_pre+1+k_pre) with (i+1) by lia. assumption.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_10_1_split_goal_2 : maxSlidingWindow_entail_wit_10_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: swm_arith.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_10_1 : maxSlidingWindow_entail_wit_10_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_10_1_split_goal_1.
  - Goal_apply proof_of_maxSlidingWindow_entail_wit_10_1_split_goal_2.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_12 : maxSlidingWindow_entail_wit_12.
Proof.
  unfold maxSlidingWindow_entail_wit_12. right. intros.
  replace i with n_pre in * by lia.
  replace out_idx with (n_pre - k_pre + 1) in * by lia.
  Exists out_l_2.
  sep_apply (IntArray.seg_to_full out_pre 0 (n_pre - k_pre + 1) out_l_2).
  sep_apply (IntArray.full_to_undef_full (&("q")) n_pre q_l).
  sep_apply (IntArray.undef_full_to_undef_seg (&("q")) n_pre).
  sep_apply (IntArray.undef_seg_merge_to_undef_full (&("q")) 0 n_pre 100000); try lia.
  repeat rewrite Z.mul_0_l. repeat rewrite Z.add_0_r. repeat rewrite Z.sub_0_r.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    unfold SlidingWindowMaximum. split; [lia |].
    intros idx Hidx.
    match goal with H : SWMOutputPrefix _ _ _ _ |- _ => apply (H idx) end.
    lia.
Qed.
