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

(*----- Function OsSortLinkResponseTimeConvertFreq -----*)

Definition OsSortLinkResponseTimeConvertFreq_return_wit_1 :=
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (n: Z) (oldFreq_pre: Z) (PreH1 : (oldFreq_pre <> 0)),
  (store_swtmr_sorted_dll sg (updateNodeTime (l2) (oldFreq_pre) (n)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
  **  (store_task_sorted_dll sg (updateNodeTime (l1) (oldFreq_pre) (n)) )
|--
  “ (oldFreq_pre <> 0) ”
  &&  (store_task_sorted_dll sg (updateNodeTime (l1) (oldFreq_pre) (n)) )
  **  (store_swtmr_sorted_dll sg (updateNodeTime (l2) (oldFreq_pre) (n)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
.

Definition OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1_pure :=
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (n: Z) (oldFreq_pre: Z) (PreH1 : (oldFreq_pre <> 0)),
  ((( &( "taskHead" ) )) # Ptr  |-> ( &( "g_taskSortLink" ) ))
  **  ((( &( "oldFreq" ) )) # UInt64  |-> oldFreq_pre)
  **  (store_task_sorted_dll sg l1 )
  **  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
|--
  “ (oldFreq_pre <> 0) ”
  &&  “ (( &( "g_taskSortLink" ) ) = ( &( "g_taskSortLink" ) )) ”
.

Definition OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1_aux :=
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (n: Z) (oldFreq_pre: Z) (PreH1 : (oldFreq_pre <> 0)),
  (store_task_sorted_dll sg l1 )
  **  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
|--
  “ (oldFreq_pre <> 0) ”
  &&  “ (( &( "g_taskSortLink" ) ) = ( &( "g_taskSortLink" ) )) ”
  &&  “ (oldFreq_pre <> 0) ”
  &&  (store_task_sorted_dll sg l1 )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
  **  (store_swtmr_sorted_dll sg l2 )
.

Definition OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1 := OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1_pure -> OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1_aux.

Definition OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2_pure :=
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (n: Z) (oldFreq_pre: Z) (PreH1 : (oldFreq_pre <> 0)),
  ((( &( "swtmrHead" ) )) # Ptr  |-> ( &( "g_swtmrSortLink" ) ))
  **  (store_task_sorted_dll sg (updateNodeTime (l1) (oldFreq_pre) (n)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
  **  ((( &( "taskHead" ) )) # Ptr  |-> ( &( "g_taskSortLink" ) ))
  **  ((( &( "oldFreq" ) )) # UInt64  |-> oldFreq_pre)
  **  (store_swtmr_sorted_dll sg l2 )
|--
  “ (oldFreq_pre <> 0) ”
  &&  “ (( &( "g_swtmrSortLink" ) ) = ( &( "g_swtmrSortLink" ) )) ”
.

Definition OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2_aux :=
forall (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (n: Z) (oldFreq_pre: Z) (PreH1 : (oldFreq_pre <> 0)),
  (store_task_sorted_dll sg (updateNodeTime (l1) (oldFreq_pre) (n)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
  **  (store_swtmr_sorted_dll sg l2 )
|--
  “ (oldFreq_pre <> 0) ”
  &&  “ (( &( "g_swtmrSortLink" ) ) = ( &( "g_swtmrSortLink" ) )) ”
  &&  “ (oldFreq_pre <> 0) ”
  &&  (store_swtmr_sorted_dll sg l2 )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)
  **  (store_task_sorted_dll sg (updateNodeTime (l1) (oldFreq_pre) (n)) )
.

Definition OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2 := OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2_pure -> OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2_aux.

(* Shallow FunAssertion specs for SortLinkNodeTimeUpdate. *)
Definition SortLinkNodeTimeUpdate_sig : FuncSig := ([ * struct "SortLinkAttribute"; u64], void)%ctype.

Definition SortLinkNodeTimeUpdate_swmtrSpec : Spec SortLinkNodeTimeUpdate_sig :=
  fun F =>
ALL (n: Z),
ALL (sg: StableGlobVars),
ALL (l: (@list (@DL_Node (@sortedLinkNode Z)))),
HoareFun ([ * struct "SortLinkAttribute"; u64], void)%ctype
  (fun '(sortLinkHead_pre, oldFreq_pre) =>
  (“ (oldFreq_pre <> 0) ”
  &&  “ (sortLinkHead_pre = ( &( "g_swtmrSortLink" ) )) ”
  &&  (store_swtmr_sorted_dll sg l )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)))
  (fun '(sortLinkHead_pre, oldFreq_pre) (_retval : unit) =>
  ((store_swtmr_sorted_dll sg (updateNodeTime (l) (oldFreq_pre) (n)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)))
  F.

Definition SortLinkNodeTimeUpdate_taskSpec : Spec SortLinkNodeTimeUpdate_sig :=
  fun F =>
ALL (n: Z),
ALL (sg: StableGlobVars),
ALL (l: (@list (@DL_Node (@sortedLinkNode Z)))),
HoareFun ([ * struct "SortLinkAttribute"; u64], void)%ctype
  (fun '(sortLinkHead_pre, oldFreq_pre) =>
  (“ (oldFreq_pre <> 0) ”
  &&  “ (sortLinkHead_pre = ( &( "g_taskSortLink" ) )) ”
  &&  (store_task_sorted_dll sg l )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)))
  (fun '(sortLinkHead_pre, oldFreq_pre) (_retval : unit) =>
  ((store_task_sorted_dll sg (updateNodeTime (l) (oldFreq_pre) (n)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)))
  F.

Definition SortLinkNodeTimeUpdate_highSpec : Spec SortLinkNodeTimeUpdate_sig :=
  fun F =>
ALL A : Type,
ALL (n: Z),
ALL (storeA: (Z -> (A -> Assertion))),
ALL (l: (@list (@DL_Node (@sortedLinkNode A)))),
HoareFun ([ * struct "SortLinkAttribute"; u64], void)%ctype
  (fun '(sortLinkHead_pre, oldFreq_pre) =>
  (“ (oldFreq_pre <> 0) ”
  &&  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)))
  (fun '(sortLinkHead_pre, oldFreq_pre) (_retval : unit) =>
  ((store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (updateNodeTime (l) (oldFreq_pre) (n)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n)))
  F.

Definition SortLinkNodeTimeUpdate_highSpec_entail_swmtrSpec :=
forall (sortLinkHead_pre: Z) (oldFreq_pre: Z) (n_swmtrSpec: Z) (sg_swmtrSpec: StableGlobVars) (l_swmtrSpec: (@list (@DL_Node (@sortedLinkNode Z)))),
  (“ (oldFreq_pre <> 0) ”
  &&  “ (sortLinkHead_pre = ( &( "g_swtmrSortLink" ) )) ”
  &&  (store_swtmr_sorted_dll sg_swmtrSpec l_swmtrSpec )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_swmtrSpec))
|--
EX (A: Type) ,
EX (n_highSpec: Z)(storeA_highSpec: (Z -> (A -> Assertion)))(l_highSpec: (@list (@DL_Node (@sortedLinkNode A)))),
  (“ (oldFreq_pre <> 0) ”
  &&  (store_sorted_dll storeA_highSpec &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l_highSpec )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_highSpec))
  **
  (  ((store_sorted_dll storeA_highSpec &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (updateNodeTime (l_highSpec) (oldFreq_pre) (n_highSpec)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_highSpec))
  -*
  ((store_swtmr_sorted_dll sg_swmtrSpec (updateNodeTime (l_swmtrSpec) (oldFreq_pre) (n_swmtrSpec)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_swmtrSpec)))
.

Definition SortLinkNodeTimeUpdate_highSpec_entail_taskSpec :=
forall (sortLinkHead_pre: Z) (oldFreq_pre: Z) (n_taskSpec: Z) (sg_taskSpec: StableGlobVars) (l_taskSpec: (@list (@DL_Node (@sortedLinkNode Z)))),
  (“ (oldFreq_pre <> 0) ”
  &&  “ (sortLinkHead_pre = ( &( "g_taskSortLink" ) )) ”
  &&  (store_task_sorted_dll sg_taskSpec l_taskSpec )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_taskSpec))
|--
EX (A: Type) ,
EX (n_highSpec: Z)(storeA_highSpec: (Z -> (A -> Assertion)))(l_highSpec: (@list (@DL_Node (@sortedLinkNode A)))),
  (“ (oldFreq_pre <> 0) ”
  &&  (store_sorted_dll storeA_highSpec &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l_highSpec )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_highSpec))
  **
  (  ((store_sorted_dll storeA_highSpec &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (updateNodeTime (l_highSpec) (oldFreq_pre) (n_highSpec)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_highSpec))
  -*
  ((store_task_sorted_dll sg_taskSpec (updateNodeTime (l_taskSpec) (oldFreq_pre) (n_taskSpec)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_taskSpec)))
.

Module Type VC_Correct.

Include los_sortlink_Strategy_Correct.

Axiom proof_of_OsSortLinkResponseTimeConvertFreq_return_wit_1 : OsSortLinkResponseTimeConvertFreq_return_wit_1.
Axiom proof_of_OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1_pure : OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1_pure.
Axiom proof_of_OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1 : OsSortLinkResponseTimeConvertFreq_partial_solve_wit_1.
Axiom proof_of_OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2_pure : OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2_pure.
Axiom proof_of_OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2 : OsSortLinkResponseTimeConvertFreq_partial_solve_wit_2.
Axiom proof_of_SortLinkNodeTimeUpdate_highSpec_entail_swmtrSpec : SortLinkNodeTimeUpdate_highSpec_entail_swmtrSpec.
Axiom proof_of_SortLinkNodeTimeUpdate_highSpec_entail_taskSpec : SortLinkNodeTimeUpdate_highSpec_entail_taskSpec.

End VC_Correct.
