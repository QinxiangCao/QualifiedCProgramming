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

(*----- Function GET_SORTLIST_VALUE -----*)

Definition GET_SORTLIST_VALUE_return_wit_1 := 
(
forall (A: Type) (sortList_pre: Z) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) ,
  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
|--
  “ (t = t) ”
  &&  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
) \/
(
forall (A: Type) (sortList_pre: Z) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) (PreH1 : (t <= UINT64_MAX)) (PreH2 : (t >= 0)) ,
  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
|--
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
).

Definition GET_SORTLIST_VALUE_return_wit_1_split_goal_spatial := 
forall (A: Type) (sortList_pre: Z) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) (PreH1 : (t <= UINT64_MAX)) (PreH2 : (t >= 0)) ,
  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
|--
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
.

Definition GET_SORTLIST_VALUE_partial_solve_wit_1 := 
forall (A: Type) (sortList_pre: Z) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) ,
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
.

Definition GET_SORTLIST_VALUE_which_implies_wit_1 := 
(
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) (sortList: Z) ,
  (storesortedLinkNode storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
) \/
(
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) (sortList: Z) ,
  (storesortedLinkNode storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
).

Definition GET_SORTLIST_VALUE_which_implies_wit_1_split_goal_spatial := 
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) (sortList: Z) ,
  (storesortedLinkNode storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
.

(*----- Function SET_SORTLIST_VALUE -----*)

Definition SET_SORTLIST_VALUE_return_wit_1 := 
(
forall (A: Type) (value_pre: Z) (sortList_pre: Z) (storeA: (Z -> (A -> Assertion))) (a: A) ,
  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> value_pre)
|--
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (value_pre)) )
) \/
(
forall (A: Type) (value_pre: Z) (sortList_pre: Z) (storeA: (Z -> (A -> Assertion))) (a: A) (PreH1 : (value_pre <= UINT64_MAX)) (PreH2 : (value_pre >= 0)) ,
  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> value_pre)
|--
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (value_pre)) )
).

Definition SET_SORTLIST_VALUE_return_wit_1_split_goal_spatial := 
forall (A: Type) (value_pre: Z) (sortList_pre: Z) (storeA: (Z -> (A -> Assertion))) (a: A) (PreH1 : (value_pre <= UINT64_MAX)) (PreH2 : (value_pre >= 0)) ,
  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> value_pre)
|--
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (value_pre)) )
.

Definition SET_SORTLIST_VALUE_partial_solve_wit_1 := 
forall (A: Type) (sortList_pre: Z) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) ,
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
.

Definition SET_SORTLIST_VALUE_which_implies_wit_1 := 
(
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) (sortList: Z) ,
  (storesortedLinkNode storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
) \/
(
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) (sortList: Z) ,
  (storesortedLinkNode storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
).

Definition SET_SORTLIST_VALUE_which_implies_wit_1_split_goal_spatial := 
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (t: Z) (a: A) (sortList: Z) ,
  (storesortedLinkNode storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
.

Module Type VC_Correct.

Include los_sortlink_Strategy_Correct.

Axiom proof_of_GET_SORTLIST_VALUE_return_wit_1 : GET_SORTLIST_VALUE_return_wit_1.
Axiom proof_of_GET_SORTLIST_VALUE_partial_solve_wit_1 : GET_SORTLIST_VALUE_partial_solve_wit_1.
Axiom proof_of_GET_SORTLIST_VALUE_which_implies_wit_1 : GET_SORTLIST_VALUE_which_implies_wit_1.
Axiom proof_of_SET_SORTLIST_VALUE_return_wit_1 : SET_SORTLIST_VALUE_return_wit_1.
Axiom proof_of_SET_SORTLIST_VALUE_partial_solve_wit_1 : SET_SORTLIST_VALUE_partial_solve_wit_1.
Axiom proof_of_SET_SORTLIST_VALUE_which_implies_wit_1 : SET_SORTLIST_VALUE_which_implies_wit_1.

End VC_Correct.
