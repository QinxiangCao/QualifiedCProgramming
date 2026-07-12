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
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.Los_Verify_State_def.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.tick_backup.
Local Open Scope sac.
From SimpleC.EE.Applications_human Require Import los_sortlink_strategy_goal.
From SimpleC.EE.Applications_human Require Import los_sortlink_strategy_proof.

(*----- Function OsSortLinkGetRemainTime -----*)

Definition OsSortLinkGetRemainTime_safety_wit_1 := 
forall (A: Type) (targetSortList_pre: Z) (currTime_pre: Z) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) (PreH1 : (currTime_pre >= t)) (PreH2 : (currTime_pre >= 0)) ,
  ((( &( "targetSortList" ) )) # Ptr  |-> targetSortList_pre)
  **  (storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((targetSortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((( &( "currTime" ) )) # UInt64  |-> currTime_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OsSortLinkGetRemainTime_return_wit_1 := 
(
forall (A: Type) (targetSortList_pre: Z) (currTime_pre: Z) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) (PreH1 : (currTime_pre < t)) (PreH2 : (currTime_pre >= 0)) ,
  (storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((targetSortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
|--
  “ (currTime_pre < t) ” 
  &&  “ ((unsigned_last_nbits ((t - currTime_pre )) (64)) = (t - currTime_pre )) ”
  &&  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
) \/
(
forall (A: Type) (targetSortList_pre: Z) (currTime_pre: Z) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) (PreH1 : (currTime_pre < t)) (PreH2 : (currTime_pre >= 0)) ,
  (storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((targetSortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
|--
  “ ((unsigned_last_nbits ((t - currTime_pre )) (64)) = (t - currTime_pre )) ”
  &&  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
).

Definition OsSortLinkGetRemainTime_return_wit_1_split_goal_1 := 
forall (A: Type) (targetSortList_pre: Z) (currTime_pre: Z) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) (PreH1 : (currTime_pre < t)) (PreH2 : (currTime_pre >= 0)) ,
  (storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((targetSortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
|--
  “ ((unsigned_last_nbits ((t - currTime_pre )) (64)) = (t - currTime_pre )) ”
.

Definition OsSortLinkGetRemainTime_return_wit_1_split_goal_spatial := 
forall (A: Type) (targetSortList_pre: Z) (currTime_pre: Z) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) (PreH1 : (currTime_pre < t)) (PreH2 : (currTime_pre >= 0)) ,
  (storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((targetSortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
|--
  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
.

Definition OsSortLinkGetRemainTime_return_wit_2 := 
(
forall (A: Type) (targetSortList_pre: Z) (currTime_pre: Z) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) (PreH1 : (currTime_pre >= t)) (PreH2 : (currTime_pre >= 0)) ,
  (storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((targetSortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
|--
  “ (currTime_pre >= t) ” 
  &&  “ (0 = 0) ”
  &&  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
) \/
(
forall (A: Type) (targetSortList_pre: Z) (currTime_pre: Z) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) (PreH1 : (currTime_pre >= t)) (PreH2 : (currTime_pre >= 0)) ,
  (storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((targetSortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
|--
  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
).

Definition OsSortLinkGetRemainTime_return_wit_2_split_goal_spatial := 
forall (A: Type) (targetSortList_pre: Z) (currTime_pre: Z) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) (PreH1 : (currTime_pre >= t)) (PreH2 : (currTime_pre >= 0)) ,
  (storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((targetSortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
|--
  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
.

Definition OsSortLinkGetRemainTime_partial_solve_wit_1 := 
forall (A: Type) (targetSortList_pre: Z) (currTime_pre: Z) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) (PreH1 : (currTime_pre >= 0)) ,
  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  “ (currTime_pre >= 0) ”
  &&  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
.

Definition OsSortLinkGetRemainTime_which_implies_wit_1 := 
(
forall (A: Type) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) (targetSortList: Z) ,
  (storesortedLinkNode storeA &((targetSortList)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((targetSortList)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((targetSortList)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
) \/
(
forall (A: Type) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) (targetSortList: Z) ,
  (storesortedLinkNode storeA &((targetSortList)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((targetSortList)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((targetSortList)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
).

Definition OsSortLinkGetRemainTime_which_implies_wit_1_split_goal_spatial := 
forall (A: Type) (t: Z) (a: A) (storeA: (Z -> (A -> Assertion))) (targetSortList: Z) ,
  (storesortedLinkNode storeA &((targetSortList)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((targetSortList)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((targetSortList)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
.

Module Type VC_Correct.

Include los_sortlink_Strategy_Correct.

Axiom proof_of_OsSortLinkGetRemainTime_safety_wit_1 : OsSortLinkGetRemainTime_safety_wit_1.
Axiom proof_of_OsSortLinkGetRemainTime_return_wit_1 : OsSortLinkGetRemainTime_return_wit_1.
Axiom proof_of_OsSortLinkGetRemainTime_return_wit_2 : OsSortLinkGetRemainTime_return_wit_2.
Axiom proof_of_OsSortLinkGetRemainTime_partial_solve_wit_1 : OsSortLinkGetRemainTime_partial_solve_wit_1.
Axiom proof_of_OsSortLinkGetRemainTime_which_implies_wit_1 : OsSortLinkGetRemainTime_which_implies_wit_1.

End VC_Correct.
