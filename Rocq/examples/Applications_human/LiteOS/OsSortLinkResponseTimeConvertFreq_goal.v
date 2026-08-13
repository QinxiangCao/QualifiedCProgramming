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

(*----- Function OsSortLinkResponseTimeConvertFreq -----*)

Definition OsSortLinkResponseTimeConvertFreq_return_wit_1 := 
forall (oldFreq_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (n: Z) (PreH1 : (oldFreq_pre <> 0)) ,
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
forall (oldFreq_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (n: Z) (PreH1 : (oldFreq_pre <> 0)) ,
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
forall (oldFreq_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (n: Z) (PreH1 : (oldFreq_pre <> 0)) ,
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
forall (oldFreq_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (n: Z) (PreH1 : (oldFreq_pre <> 0)) ,
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
forall (oldFreq_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode Z)))) (l1: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (n: Z) (PreH1 : (oldFreq_pre <> 0)) ,
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

Definition SortLinkNodeTimeUpdate_derive_swmtrSpec_by_highSpec := 
forall (oldFreq_pre: Z) (sortLinkHead_pre: Z) (l_swmtrSpec: (@list (@DL_Node (@sortedLinkNode Z)))) (sg_swmtrSpec: StableGlobVars) (n_swmtrSpec: Z) ,
  “ (oldFreq_pre <> 0) ” 
  &&  “ (sortLinkHead_pre = ( &( "g_swtmrSortLink" ) )) ”
  &&  (store_swtmr_sorted_dll sg_swmtrSpec l_swmtrSpec )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_swmtrSpec)
|--
EX (A: Type) ,
EX (n_highSpec: Z) (storeA_highSpec: (Z -> (A -> Assertion))) (l_highSpec: (@list (@DL_Node (@sortedLinkNode A)))) ,
  (“ (oldFreq_pre <> 0) ”
  &&  (store_sorted_dll storeA_highSpec &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l_highSpec )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_highSpec))
  **
  (((store_sorted_dll storeA_highSpec &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (updateNodeTime (l_highSpec) (oldFreq_pre) (n_highSpec)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_highSpec))
  -*
  ((store_swtmr_sorted_dll sg_swmtrSpec (updateNodeTime (l_swmtrSpec) (oldFreq_pre) (n_swmtrSpec)) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_swmtrSpec)))
.

Definition SortLinkNodeTimeUpdate_derive_taskSpec_by_highSpec := 
forall (oldFreq_pre: Z) (sortLinkHead_pre: Z) (l_taskSpec: (@list (@DL_Node (@sortedLinkNode Z)))) (sg_taskSpec: StableGlobVars) (n_taskSpec: Z) ,
  “ (oldFreq_pre <> 0) ” 
  &&  “ (sortLinkHead_pre = ( &( "g_taskSortLink" ) )) ”
  &&  (store_task_sorted_dll sg_taskSpec l_taskSpec )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_taskSpec)
|--
EX (A: Type) ,
EX (n_highSpec: Z) (storeA_highSpec: (Z -> (A -> Assertion))) (l_highSpec: (@list (@DL_Node (@sortedLinkNode A)))) ,
  (“ (oldFreq_pre <> 0) ”
  &&  (store_sorted_dll storeA_highSpec &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l_highSpec )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> n_highSpec))
  **
  (((store_sorted_dll storeA_highSpec &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (updateNodeTime (l_highSpec) (oldFreq_pre) (n_highSpec)) )
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
Axiom proof_of_SortLinkNodeTimeUpdate_derive_swmtrSpec_by_highSpec : SortLinkNodeTimeUpdate_derive_swmtrSpec_by_highSpec.
Axiom proof_of_SortLinkNodeTimeUpdate_derive_taskSpec_by_highSpec : SortLinkNodeTimeUpdate_derive_taskSpec_by_highSpec.

End VC_Correct.
