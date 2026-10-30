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

(*----- Function OsGetNextExpireTime -----*)

Definition OsGetNextExpireTime_return_wit_1 :=
(
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (startTime_pre: Z) (tickPrecision_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval_2 >= retval)) (PreH2 : (retval = (getFirstNodeExpireTime (l2) (startTime_pre) (tickPrecision_pre)))) (PreH3 : (retval_2 = (getFirstNodeExpireTime (l1) (startTime_pre) (tickPrecision_pre)))),
  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
  **  (store_task_sorted_dll sg l1 )
|--
  “ (retval = (getminExpireTime (l1) (l2) (startTime_pre) (tickPrecision_pre))) ”
  &&  (store_task_sorted_dll sg l1 )
  **  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
) \/
(
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (startTime_pre: Z) (tickPrecision_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval_2 >= retval)) (PreH2 : (retval = (getFirstNodeExpireTime (l2) (startTime_pre) (tickPrecision_pre)))) (PreH3 : (retval_2 = (getFirstNodeExpireTime (l1) (startTime_pre) (tickPrecision_pre)))),
  TT && emp 
|--
  “ (retval = (getminExpireTime (l1) (l2) (startTime_pre) (tickPrecision_pre))) ”
  &&  emp
).

Definition OsGetNextExpireTime_return_wit_1_split_goal_1 :=
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (startTime_pre: Z) (tickPrecision_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval_2 >= retval)) (PreH2 : (retval = (getFirstNodeExpireTime (l2) (startTime_pre) (tickPrecision_pre)))) (PreH3 : (retval_2 = (getFirstNodeExpireTime (l1) (startTime_pre) (tickPrecision_pre)))),
  (retval = (getminExpireTime (l1) (l2) (startTime_pre) (tickPrecision_pre)))
.

Definition OsGetNextExpireTime_return_wit_2 :=
(
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (startTime_pre: Z) (tickPrecision_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (getFirstNodeExpireTime (l2) (startTime_pre) (tickPrecision_pre)))) (PreH3 : (retval = (getFirstNodeExpireTime (l1) (startTime_pre) (tickPrecision_pre)))),
  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
  **  (store_task_sorted_dll sg l1 )
|--
  “ (retval = (getminExpireTime (l1) (l2) (startTime_pre) (tickPrecision_pre))) ”
  &&  (store_task_sorted_dll sg l1 )
  **  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
) \/
(
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (startTime_pre: Z) (tickPrecision_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (getFirstNodeExpireTime (l2) (startTime_pre) (tickPrecision_pre)))) (PreH3 : (retval = (getFirstNodeExpireTime (l1) (startTime_pre) (tickPrecision_pre)))),
  TT && emp 
|--
  “ (retval = (getminExpireTime (l1) (l2) (startTime_pre) (tickPrecision_pre))) ”
  &&  emp
).

Definition OsGetNextExpireTime_return_wit_2_split_goal_1 :=
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (startTime_pre: Z) (tickPrecision_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval < retval_2)) (PreH2 : (retval_2 = (getFirstNodeExpireTime (l2) (startTime_pre) (tickPrecision_pre)))) (PreH3 : (retval = (getFirstNodeExpireTime (l1) (startTime_pre) (tickPrecision_pre)))),
  (retval = (getminExpireTime (l1) (l2) (startTime_pre) (tickPrecision_pre)))
.

Definition OsGetNextExpireTime_partial_solve_wit_1_pure :=
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (startTime_pre: Z) (tickPrecision_pre: Z),
  ((( &( "taskExpireTime" ) )) # UInt64  |->_)
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "tickPrecision" ) )) # UInt64  |-> tickPrecision_pre)
  **  (store_task_sorted_dll sg l1 )
  **  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
|--
  “ (( &( "g_taskSortLink" ) ) = ( &( "g_taskSortLink" ) )) ”
.

Definition OsGetNextExpireTime_partial_solve_wit_1_aux :=
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars),
  (store_task_sorted_dll sg l1 )
  **  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
|--
  “ (( &( "g_taskSortLink" ) ) = ( &( "g_taskSortLink" ) )) ”
  &&  (store_task_sorted_dll sg l1 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
  **  (store_swtmr_sorted_dll sg l2 )
.

Definition OsGetNextExpireTime_partial_solve_wit_1 := OsGetNextExpireTime_partial_solve_wit_1_pure -> OsGetNextExpireTime_partial_solve_wit_1_aux.

Definition OsGetNextExpireTime_partial_solve_wit_2_pure :=
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (startTime_pre: Z) (tickPrecision_pre: Z) (retval: Z) (PreH1 : (retval = (getFirstNodeExpireTime (l1) (startTime_pre) (tickPrecision_pre)))),
  ((( &( "swtmrExpireTime" ) )) # UInt64  |->_)
  **  (store_task_sorted_dll sg l1 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
  **  ((( &( "taskExpireTime" ) )) # UInt64  |-> retval)
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "tickPrecision" ) )) # UInt64  |-> tickPrecision_pre)
  **  (store_swtmr_sorted_dll sg l2 )
|--
  “ (( &( "g_swtmrSortLink" ) ) = ( &( "g_swtmrSortLink" ) )) ”
.

Definition OsGetNextExpireTime_partial_solve_wit_2_aux :=
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (startTime_pre: Z) (tickPrecision_pre: Z) (retval: Z) (PreH1 : (retval = (getFirstNodeExpireTime (l1) (startTime_pre) (tickPrecision_pre)))),
  (store_task_sorted_dll sg l1 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
  **  (store_swtmr_sorted_dll sg l2 )
|--
  “ (( &( "g_swtmrSortLink" ) ) = ( &( "g_swtmrSortLink" ) )) ”
  &&  “ (retval = (getFirstNodeExpireTime (l1) (startTime_pre) (tickPrecision_pre))) ”
  &&  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))
  **  (store_task_sorted_dll sg l1 )
.

Definition OsGetNextExpireTime_partial_solve_wit_2 := OsGetNextExpireTime_partial_solve_wit_2_pure -> OsGetNextExpireTime_partial_solve_wit_2_aux.

(* Shallow FunAssertion specs for GetSortLinkNextExpireTime. *)
Definition GetSortLinkNextExpireTime_sig : FuncSig := ([ * struct "SortLinkAttribute"; u64; u64], u64)%ctype.

Definition GetSortLinkNextExpireTime_swmtrSpec : Spec GetSortLinkNextExpireTime_sig :=
  fun F =>
ALL (sg: StableGlobVars),
ALL (l: (@list (@DL_Node (@sortedLinkNode Z)))),
HoareFun ([ * struct "SortLinkAttribute"; u64; u64], u64)%ctype
  (fun '(sortHead_pre, (startTime_pre, tickPrecision_pre)) =>
  (“ (sortHead_pre = ( &( "g_swtmrSortLink" ) )) ”
  &&  (store_swtmr_sorted_dll sg l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))))
  (fun '(sortHead_pre, (startTime_pre, tickPrecision_pre)) retval =>
  (“ (retval = (getFirstNodeExpireTime (l) (startTime_pre) (tickPrecision_pre))) ”
  &&  (store_swtmr_sorted_dll sg l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))))
  F.

Definition GetSortLinkNextExpireTime_taskSpec : Spec GetSortLinkNextExpireTime_sig :=
  fun F =>
ALL (sg: StableGlobVars),
ALL (l: (@list (@DL_Node (@sortedLinkNode Z)))),
HoareFun ([ * struct "SortLinkAttribute"; u64; u64], u64)%ctype
  (fun '(sortHead_pre, (startTime_pre, tickPrecision_pre)) =>
  (“ (sortHead_pre = ( &( "g_taskSortLink" ) )) ”
  &&  (store_task_sorted_dll sg l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))))
  (fun '(sortHead_pre, (startTime_pre, tickPrecision_pre)) retval =>
  (“ (retval = (getFirstNodeExpireTime (l) (startTime_pre) (tickPrecision_pre))) ”
  &&  (store_task_sorted_dll sg l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))))
  F.

Definition GetSortLinkNextExpireTime_highSpec : Spec GetSortLinkNextExpireTime_sig :=
  fun F =>
ALL A : Type,
ALL (storeA: (Z -> (A -> Assertion))),
ALL (l: (@list (@DL_Node (@sortedLinkNode A)))),
HoareFun ([ * struct "SortLinkAttribute"; u64; u64], u64)%ctype
  (fun '(sortHead_pre, (startTime_pre, tickPrecision_pre)) =>
  ((store_sorted_dll storeA &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))))
  (fun '(sortHead_pre, (startTime_pre, tickPrecision_pre)) retval =>
  (“ (retval = (getFirstNodeExpireTime (l) (startTime_pre) (tickPrecision_pre))) ”
  &&  (store_sorted_dll storeA &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))))
  F.

Definition GetSortLinkNextExpireTime_highSpec_entail_swmtrSpec :=
forall (sortHead_pre: Z) (startTime_pre: Z) (tickPrecision_pre: Z) (sg_swmtrSpec: StableGlobVars) (l_swmtrSpec: (@list (@DL_Node (@sortedLinkNode Z)))),
  (“ (sortHead_pre = ( &( "g_swtmrSortLink" ) )) ”
  &&  (store_swtmr_sorted_dll sg_swmtrSpec l_swmtrSpec )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 )))
|--
EX (A: Type) ,
EX (storeA_highSpec: (Z -> (A -> Assertion)))(l_highSpec: (@list (@DL_Node (@sortedLinkNode A)))),
  ((store_sorted_dll storeA_highSpec &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l_highSpec )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 )))
  **
  (ALL (retval: Z),
  (“ (retval = (getFirstNodeExpireTime (l_highSpec) (startTime_pre) (tickPrecision_pre))) ”
  &&  (store_sorted_dll storeA_highSpec &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l_highSpec )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 )))
  -*
  (“ (retval = (getFirstNodeExpireTime (l_swmtrSpec) (startTime_pre) (tickPrecision_pre))) ”
  &&  (store_swtmr_sorted_dll sg_swmtrSpec l_swmtrSpec )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))))
.

Definition GetSortLinkNextExpireTime_highSpec_entail_taskSpec :=
forall (sortHead_pre: Z) (startTime_pre: Z) (tickPrecision_pre: Z) (sg_taskSpec: StableGlobVars) (l_taskSpec: (@list (@DL_Node (@sortedLinkNode Z)))),
  (“ (sortHead_pre = ( &( "g_taskSortLink" ) )) ”
  &&  (store_task_sorted_dll sg_taskSpec l_taskSpec )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 )))
|--
EX (A: Type) ,
EX (storeA_highSpec: (Z -> (A -> Assertion)))(l_highSpec: (@list (@DL_Node (@sortedLinkNode A)))),
  ((store_sorted_dll storeA_highSpec &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l_highSpec )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 )))
  **
  (ALL (retval: Z),
  (“ (retval = (getFirstNodeExpireTime (l_highSpec) (startTime_pre) (tickPrecision_pre))) ”
  &&  (store_sorted_dll storeA_highSpec &((sortHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l_highSpec )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 )))
  -*
  (“ (retval = (getFirstNodeExpireTime (l_taskSpec) (startTime_pre) (tickPrecision_pre))) ”
  &&  (store_task_sorted_dll sg_taskSpec l_taskSpec )
  **  ((( &( "OS_SORT_LINK_UINT64_MAX" ) )) # UInt64  |-> ((Z.lxor 2 64) - 1 ))))
.

Module Type VC_Correct.

Include los_sortlink_Strategy_Correct.

Axiom proof_of_OsGetNextExpireTime_return_wit_1 : OsGetNextExpireTime_return_wit_1.
Axiom proof_of_OsGetNextExpireTime_return_wit_2 : OsGetNextExpireTime_return_wit_2.
Axiom proof_of_OsGetNextExpireTime_partial_solve_wit_1_pure : OsGetNextExpireTime_partial_solve_wit_1_pure.
Axiom proof_of_OsGetNextExpireTime_partial_solve_wit_1 : OsGetNextExpireTime_partial_solve_wit_1.
Axiom proof_of_OsGetNextExpireTime_partial_solve_wit_2_pure : OsGetNextExpireTime_partial_solve_wit_2_pure.
Axiom proof_of_OsGetNextExpireTime_partial_solve_wit_2 : OsGetNextExpireTime_partial_solve_wit_2.
Axiom proof_of_GetSortLinkNextExpireTime_highSpec_entail_swmtrSpec : GetSortLinkNextExpireTime_highSpec_entail_swmtrSpec.
Axiom proof_of_GetSortLinkNextExpireTime_highSpec_entail_taskSpec : GetSortLinkNextExpireTime_highSpec_entail_taskSpec.

End VC_Correct.
