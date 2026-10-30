From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.Los_Verify_State_def.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.tick_backup.
Local Open Scope sac.
From SimpleC.EE.Applications_human Require Import los_sortlink_strategy_goal.
From SimpleC.EE.Applications_human Require Import los_sortlink_strategy_proof.

(*----- Function LOS_ListInit -----*)

Definition LOS_ListInit_return_wit_1 :=
(
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (list_pre: Z),
  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre)
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
|--
  (store_dll storeA list_pre (@nil (@DL_Node A)) )
) \/
(
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (list_pre: Z),
  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre)
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
|--
  (store_dll storeA list_pre (@nil (@DL_Node A)) )
).

Definition LOS_ListInit_return_wit_1_split_goal_spatial :=
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (list_pre: Z),
  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> list_pre)
  **  ((&((list_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> list_pre)
|--
  (store_dll storeA list_pre (@nil (@DL_Node A)) )
.

(*----- Function OsSortLinkInit -----*)

Definition OsSortLinkInit_safety_wit_1 :=
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z),
  (store_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (@nil (@DL_Node A)) )
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OsSortLinkInit_return_wit_1 :=
forall (A: Type) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z),
  (store_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (@nil (@DL_Node A)) )
|--
  “ (0 = 0) ”
  &&  (store_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (@nil (@DL_Node A)) )
.

Definition OsSortLinkInit_partial_solve_wit_1 :=
forall (sortLinkHead_pre: Z),
  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |->_)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |->_)
|--
  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |->_)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |->_)
.

Module Type VC_Correct.

Include los_sortlink_Strategy_Correct.

Axiom proof_of_LOS_ListInit_return_wit_1 : LOS_ListInit_return_wit_1.
Axiom proof_of_OsSortLinkInit_safety_wit_1 : OsSortLinkInit_safety_wit_1.
Axiom proof_of_OsSortLinkInit_return_wit_1 : OsSortLinkInit_return_wit_1.
Axiom proof_of_OsSortLinkInit_partial_solve_wit_1 : OsSortLinkInit_partial_solve_wit_1.

End VC_Correct.
