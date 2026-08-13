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

(*----- Function OsDeleteNodeSortLink -----*)

Definition OsDeleteNodeSortLink_safety_wit_1 := 
forall (A: Type) (sortList_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node_callee_pstNext: Z) (node_callee_pstPrev: Z) (PreH1 : (node_callee_pstPrev = 0)) (PreH2 : (node_callee_pstNext = 0)) (PreH3 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) )) ,
  ((( &( "sortList" ) )) # Ptr  |-> sortList_pre)
  **  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> node_callee_pstPrev)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> node_callee_pstNext)
  **  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((map (sortedLinkNodeMapping) (l2)))) )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition OsDeleteNodeSortLink_safety_wit_2 := 
forall (A: Type) (sortList_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node_callee_pstNext: Z) (node_callee_pstPrev: Z) (PreH1 : (node_callee_pstPrev = 0)) (PreH2 : (node_callee_pstNext = 0)) (PreH3 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) )) ,
  ((( &( "sortList" ) )) # Ptr  |-> sortList_pre)
  **  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> node_callee_pstPrev)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> node_callee_pstNext)
  **  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((map (sortedLinkNodeMapping) (l2)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OsDeleteNodeSortLink_return_wit_1 := 
(
forall (A: Type) (sortList_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node_callee_pstNext: Z) (node_callee_pstPrev: Z) (PreH1 : (node_callee_pstPrev = 0)) (PreH2 : (node_callee_pstNext = 0)) (PreH3 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) )) ,
  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (unsigned_last_nbits ((-1)) (64)))
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> node_callee_pstPrev)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> node_callee_pstNext)
  **  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((map (sortedLinkNodeMapping) (l2)))) )
|--
  EX (v_2: Z)  (v: Z) ,
  “ (v = 0) ” 
  &&  “ (v_2 = 0) ”
  &&  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_2)
  **  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
) \/
(
forall (A: Type) (sortList_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node_callee_pstNext: Z) (node_callee_pstPrev: Z) (PreH1 : ((unsigned_last_nbits ((-1)) (64)) <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits ((-1)) (64)) >= 0)) (PreH3 : (node_callee_pstPrev = 0)) (PreH4 : (node_callee_pstNext = 0)) (PreH5 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) )) ,
  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (unsigned_last_nbits ((-1)) (64)))
  **  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((map (sortedLinkNodeMapping) (l2)))) )
|--
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
).

Definition OsDeleteNodeSortLink_return_wit_1_split_goal_spatial := 
forall (A: Type) (sortList_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node_callee_pstNext: Z) (node_callee_pstPrev: Z) (PreH1 : ((unsigned_last_nbits ((-1)) (64)) <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits ((-1)) (64)) >= 0)) (PreH3 : (node_callee_pstPrev = 0)) (PreH4 : (node_callee_pstNext = 0)) (PreH5 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) )) ,
  (storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (unsigned_last_nbits ((-1)) (64)))
  **  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((map (sortedLinkNodeMapping) (l2)))) )
|--
  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
.

Definition OsDeleteNodeSortLink_partial_solve_wit_1 := 
forall (A: Type) (sortList_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) ,
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) )
|--
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) )
.

Definition OsDeleteNodeSortLink_partial_solve_wit_2 := 
forall (A: Type) (sortList_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (PreH1 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) )) ,
  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
|--
  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) ) ”
  &&  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
.

Definition OsDeleteNodeSortLink_partial_solve_wit_3 := 
forall (A: Type) (sortList_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node_callee_pstNext: Z) (node_callee_pstPrev: Z) (PreH1 : (node_callee_pstPrev = 0)) (PreH2 : (node_callee_pstNext = 0)) (PreH3 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) )) ,
  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> node_callee_pstPrev)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> node_callee_pstNext)
  **  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
  **  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((map (sortedLinkNodeMapping) (l2)))) )
|--
  “ (node_callee_pstPrev = 0) ” 
  &&  “ (node_callee_pstNext = 0) ” 
  &&  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList_pre))) (l2)))) ) ”
  &&  (storesortedLinkNode storeA &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> node_callee_pstPrev)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> node_callee_pstNext)
  **  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((map (sortedLinkNodeMapping) (l2)))) )
.

Definition OsDeleteNodeSortLink_which_implies_wit_1 := 
(
forall (A: Type) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (sortList: Z) ,
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList))) (l2)))) )
|--
  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList))) (l2)))) ) ”
  &&  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((sortList)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
) \/
(
forall (A: Type) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (sortList: Z) ,
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList))) (l2)))) )
|--
  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList))) (l2)))) ) ”
  &&  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((sortList)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
).

Definition OsDeleteNodeSortLink_which_implies_wit_1_split_goal_1 := 
forall (A: Type) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (sortList: Z) ,
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList))) (l2)))) )
|--
  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList))) (l2)))) ) ”
.

Definition OsDeleteNodeSortLink_which_implies_wit_1_split_goal_spatial := 
forall (A: Type) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (sortList: Z) ,
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (sortList))) (l2)))) )
|--
  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((sortList)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
.

Definition OsDeleteNodeSortLink_which_implies_wit_2 := 
(
forall (A: Type) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (sortList: Z) ,
  (storesortedLinkNode storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
) \/
(
forall (A: Type) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (sortList: Z) ,
  (storesortedLinkNode storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
).

Definition OsDeleteNodeSortLink_which_implies_wit_2_split_goal_spatial := 
forall (A: Type) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (sortList: Z) ,
  (storesortedLinkNode storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((sortList)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((sortList)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
.

Module Type VC_Correct.

Include los_sortlink_Strategy_Correct.

Axiom proof_of_OsDeleteNodeSortLink_safety_wit_1 : OsDeleteNodeSortLink_safety_wit_1.
Axiom proof_of_OsDeleteNodeSortLink_safety_wit_2 : OsDeleteNodeSortLink_safety_wit_2.
Axiom proof_of_OsDeleteNodeSortLink_return_wit_1 : OsDeleteNodeSortLink_return_wit_1.
Axiom proof_of_OsDeleteNodeSortLink_partial_solve_wit_1 : OsDeleteNodeSortLink_partial_solve_wit_1.
Axiom proof_of_OsDeleteNodeSortLink_partial_solve_wit_2 : OsDeleteNodeSortLink_partial_solve_wit_2.
Axiom proof_of_OsDeleteNodeSortLink_partial_solve_wit_3 : OsDeleteNodeSortLink_partial_solve_wit_3.
Axiom proof_of_OsDeleteNodeSortLink_which_implies_wit_1 : OsDeleteNodeSortLink_which_implies_wit_1.
Axiom proof_of_OsDeleteNodeSortLink_which_implies_wit_2 : OsDeleteNodeSortLink_which_implies_wit_2.

End VC_Correct.
