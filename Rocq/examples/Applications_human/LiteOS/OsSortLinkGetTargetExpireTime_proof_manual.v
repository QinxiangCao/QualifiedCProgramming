Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.LiteOS Require Import OsSortLinkGetTargetExpireTime_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.tick_backup.
Local Open Scope sac.

Lemma proof_of_OsSortLinkGetTargetExpireTime_return_wit_2_split_goal_spatial :
    OsSortLinkGetTargetExpireTime_return_wit_2_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    intros.
    unfold storesortedLinkNode.
    simpl.
    Exists targetSortList_pre.
    split_pure_spatial.
    - cancel.
    - dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_OsSortLinkGetTargetExpireTime_return_wit_2 :
    OsSortLinkGetTargetExpireTime_return_wit_2.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_OsSortLinkGetTargetExpireTime_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_OsSortLinkGetTargetExpireTime_return_wit_1_split_goal_spatial :
    OsSortLinkGetTargetExpireTime_return_wit_1_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    intros.
    unfold storesortedLinkNode.
    simpl.
    Exists targetSortList_pre.
    split_pure_spatial; [ cancel | dump_pre_spatial; reflexivity ].
Qed.

Lemma proof_of_OsSortLinkGetTargetExpireTime_return_wit_1 :
    OsSortLinkGetTargetExpireTime_return_wit_1.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_OsSortLinkGetTargetExpireTime_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_OsSortLinkGetTargetExpireTime_which_implies_wit_1_split_goal_spatial :
  OsSortLinkGetTargetExpireTime_which_implies_wit_1_split_goal_spatial.
Proof.
  unfold storesortedLinkNode.
  LLM_pre_process ltac:(int_auto).
  simpl.
  Intros y.
  apply addr_of_arrow_field_inv in H.
  rewrite H.
  csimpl.
  simpl.
  cancel.
Qed.

Lemma proof_of_OsSortLinkGetTargetExpireTime_which_implies_wit_1 :
  OsSortLinkGetTargetExpireTime_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_OsSortLinkGetTargetExpireTime_which_implies_wit_1_split_goal_spatial.
Qed.
