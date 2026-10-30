From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.LiteOS Require Import OsSortLinkGetRemainTime_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.tick_backup.
Local Open Scope sac.

Lemma proof_of_OsSortLinkGetRemainTime_return_wit_2_split_goal_spatial :
    OsSortLinkGetRemainTime_return_wit_2_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    intros.
    unfold storesortedLinkNode.
    simpl.
    Exists targetSortList_pre.
    split_pure_spatial; [ cancel | dump_pre_spatial; reflexivity ].
Qed.

Lemma proof_of_OsSortLinkGetRemainTime_return_wit_2 : OsSortLinkGetRemainTime_return_wit_2.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_OsSortLinkGetRemainTime_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_OsSortLinkGetRemainTime_return_wit_1_split_goal_spatial :
    OsSortLinkGetRemainTime_return_wit_1_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    intros.
    unfold storesortedLinkNode.
    simpl.
    Exists targetSortList_pre.
    split_pure_spatial; [ cancel | dump_pre_spatial; reflexivity ].
Qed.

Lemma proof_of_OsSortLinkGetRemainTime_return_wit_1 : OsSortLinkGetRemainTime_return_wit_1.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_OsSortLinkGetRemainTime_return_wit_1_split_goal_spatial.
Qed.



Lemma proof_of_OsSortLinkGetRemainTime_which_implies_wit_1_split_goal_spatial :
  OsSortLinkGetRemainTime_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  unfold storesortedLinkNode.
  Intros y.
  apply addr_of_arrow_field_inv in H.
  rewrite H.
  simpl.
  cancel.
Qed.

Lemma proof_of_OsSortLinkGetRemainTime_which_implies_wit_1 : OsSortLinkGetRemainTime_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_OsSortLinkGetRemainTime_which_implies_wit_1_split_goal_spatial.
Qed.
