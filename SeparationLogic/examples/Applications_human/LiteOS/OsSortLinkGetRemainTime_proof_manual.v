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
From SimpleC.EE.Applications_human.LiteOS Require Import OsSortLinkGetRemainTime_goal.
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

Lemma proof_of_OsSortLinkGetRemainTime_return_wit_2 : OsSortLinkGetRemainTime_return_wit_2.
Proof. 
    pre_process.
    intros.
    entailer!.
    unfold storesortedLinkNode.
    simpl.
    entailer!.
    Exists targetSortList_pre.
    entailer!.
Qed. 

Lemma proof_of_OsSortLinkGetRemainTime_return_wit_1 : OsSortLinkGetRemainTime_return_wit_1.
Proof. 
    pre_process.
    intros.
    prop_apply (store_uint64_range (&(targetSortList_pre # "SortLinkList" ->ₛ "responseTime")) t).
    unfold storesortedLinkNode.
    simpl.
    entailer!.
    simpl.
    
    Exists targetSortList_pre.
    entailer!.
    apply unsigned_last_nbits_eq.
    unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize in H.
    simpl in H.
    lia.
Qed. 



Lemma proof_of_OsSortLinkGetRemainTime_which_implies_wit_1 : OsSortLinkGetRemainTime_which_implies_wit_1.
Proof. 
  unfold OsSortLinkGetRemainTime_which_implies_wit_1. 
  unfold storesortedLinkNode.
  pre_process.
  simpl.
  entailer!.
  Intros y.
  apply addr_of_arrow_field_inv in H.
  entailer!.
  rewrite H.
  entailer!.
Qed.
