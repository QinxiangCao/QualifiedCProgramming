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

(*----- Function OsAdd2SortLink -----*)

Definition OsAdd2SortLink_safety_wit_1 := 
forall (type_pre: Z) (waitTicks_pre: Z) (startTime_pre: Z) (node_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (g: Z) (t: Z) (a: Z) (pu: Z) (un: Z) (PreH1 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) <= ULLONG_MAX)) (PreH2 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) >= 0)) (PreH3 : ((waitTicks_pre * g ) <= ULLONG_MAX)) (PreH4 : ((waitTicks_pre * g ) >= 0)) ,
  ((( &( "sortLinkHead" ) )) # Ptr  |-> ( &( "g_taskSortLink" ) ))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (task_store sg &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "waitTicks" ) )) # UInt64  |-> waitTicks_pre)
  **  ((( &( "type" ) )) # Int  |-> type_pre)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> un)
  **  (store_task_sorted_dll sg l )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> g)
|--
  “ (100 <> 0) ”
.

Definition OsAdd2SortLink_safety_wit_2 := 
forall (type_pre: Z) (waitTicks_pre: Z) (startTime_pre: Z) (node_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (g: Z) (t: Z) (a: Z) (pu: Z) (un: Z) (PreH1 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) <= ULLONG_MAX)) (PreH2 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) >= 0)) (PreH3 : ((waitTicks_pre * g ) <= ULLONG_MAX)) (PreH4 : ((waitTicks_pre * g ) >= 0)) ,
  ((( &( "sortLinkHead" ) )) # Ptr  |-> ( &( "g_taskSortLink" ) ))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (task_store sg &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "waitTicks" ) )) # UInt64  |-> waitTicks_pre)
  **  ((( &( "type" ) )) # Int  |-> type_pre)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> un)
  **  (store_task_sorted_dll sg l )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> g)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition OsAdd2SortLink_return_wit_1 := 
forall (waitTicks_pre: Z) (startTime_pre: Z) (node_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (g: Z) (a: Z) (l1_2: (@list (@DL_Node (@sortedLinkNode Z)))) (l2_2: (@list (@DL_Node (@sortedLinkNode Z)))) (PreH1 : (l = (app (l1_2) (l2_2)))) (PreH2 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) <= ULLONG_MAX)) (PreH3 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) >= 0)) (PreH4 : ((waitTicks_pre * g ) <= ULLONG_MAX)) (PreH5 : ((waitTicks_pre * g ) >= 0)) ,
  (store_task_sorted_dll sg (app (l1_2) ((cons ((Build_DL_Node ((mksortedLinkNode (a) ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) )))) (node_pre))) (l2_2)))) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> g)
|--
  EX (l1: (@list (@DL_Node (@sortedLinkNode Z))))  (l2: (@list (@DL_Node (@sortedLinkNode Z)))) ,
  “ (l = (app (l1) (l2))) ”
  &&  ((( &( "g_sysClock" ) )) # UInt64  |-> g)
  **  (store_task_sorted_dll sg (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) )))) (node_pre))) (l2)))) )
.

Definition OsAdd2SortLink_partial_solve_wit_1 := 
forall (waitTicks_pre: Z) (startTime_pre: Z) (node_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (g: Z) (t: Z) (a: Z) (pu: Z) (un: Z) (PreH1 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) <= ULLONG_MAX)) (PreH2 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) >= 0)) (PreH3 : ((waitTicks_pre * g ) <= ULLONG_MAX)) (PreH4 : ((waitTicks_pre * g ) >= 0)) ,
  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> un)
  **  (storesortedLinkTaskNode task_store sg &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
  **  (store_task_sorted_dll sg l )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> g)
|--
  “ ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) <= ULLONG_MAX) ” 
  &&  “ ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) >= 0) ” 
  &&  “ ((waitTicks_pre * g ) <= ULLONG_MAX) ” 
  &&  “ ((waitTicks_pre * g ) >= 0) ”
  &&  (storesortedLinkTaskNode task_store sg &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> un)
  **  (store_task_sorted_dll sg l )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> g)
.

Definition OsAdd2SortLink_partial_solve_wit_2_pure := 
(
forall (type_pre: Z) (waitTicks_pre: Z) (startTime_pre: Z) (node_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (g: Z) (a: Z) (pu: Z) (un: Z) (PreH1 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) <= ULLONG_MAX)) (PreH2 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) >= 0)) (PreH3 : ((waitTicks_pre * g ) <= ULLONG_MAX)) (PreH4 : ((waitTicks_pre * g ) >= 0)) ,
  ((( &( "sortLinkHead" ) )) # Ptr  |-> ( &( "g_taskSortLink" ) ))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (task_store sg &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (unsigned_last_nbits ((startTime_pre + ((unsigned_last_nbits ((waitTicks_pre * g )) (64)) ÷ 100 ) )) (64)))
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "waitTicks" ) )) # UInt64  |-> waitTicks_pre)
  **  ((( &( "type" ) )) # Int  |-> type_pre)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> un)
  **  (store_task_sorted_dll sg l )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> g)
|--
  “ ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) = (startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) )) ” 
  &&  “ ((unsigned_last_nbits ((startTime_pre + ((unsigned_last_nbits ((waitTicks_pre * g )) (64)) ÷ 100 ) )) (64)) = (startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) )) ”
) \/
(
forall (type_pre: Z) (waitTicks_pre: Z) (startTime_pre: Z) (node_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (g: Z) (a: Z) (pu: Z) (un: Z) (PreH1 : (type_pre <= INT_MAX)) (PreH2 : (type_pre >= INT_MIN)) (PreH3 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) <= ULLONG_MAX)) (PreH4 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) >= 0)) (PreH5 : ((waitTicks_pre * g ) <= ULLONG_MAX)) (PreH6 : ((waitTicks_pre * g ) >= 0)) ,
  ((( &( "sortLinkHead" ) )) # Ptr  |-> ( &( "g_taskSortLink" ) ))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (task_store sg &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (unsigned_last_nbits ((startTime_pre + ((unsigned_last_nbits ((waitTicks_pre * g )) (64)) ÷ 100 ) )) (64)))
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "waitTicks" ) )) # UInt64  |-> waitTicks_pre)
  **  ((( &( "type" ) )) # Int  |-> type_pre)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> un)
  **  (store_task_sorted_dll sg l )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> g)
|--
  “ ((unsigned_last_nbits ((startTime_pre + ((unsigned_last_nbits ((waitTicks_pre * g )) (64)) ÷ 100 ) )) (64)) = (startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) )) ”
).

Definition OsAdd2SortLink_partial_solve_wit_2_pure_split_goal_1 := 
forall (type_pre: Z) (waitTicks_pre: Z) (startTime_pre: Z) (node_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (g: Z) (a: Z) (pu: Z) (un: Z) (PreH1 : (type_pre <= INT_MAX)) (PreH2 : (type_pre >= INT_MIN)) (PreH3 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) <= ULLONG_MAX)) (PreH4 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) >= 0)) (PreH5 : ((waitTicks_pre * g ) <= ULLONG_MAX)) (PreH6 : ((waitTicks_pre * g ) >= 0)) ,
  ((( &( "sortLinkHead" ) )) # Ptr  |-> ( &( "g_taskSortLink" ) ))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (task_store sg &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (unsigned_last_nbits ((startTime_pre + ((unsigned_last_nbits ((waitTicks_pre * g )) (64)) ÷ 100 ) )) (64)))
  **  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "waitTicks" ) )) # UInt64  |-> waitTicks_pre)
  **  ((( &( "type" ) )) # Int  |-> type_pre)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> un)
  **  (store_task_sorted_dll sg l )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> g)
|--
  “ ((unsigned_last_nbits ((startTime_pre + ((unsigned_last_nbits ((waitTicks_pre * g )) (64)) ÷ 100 ) )) (64)) = (startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) )) ”
.

Definition OsAdd2SortLink_partial_solve_wit_2_aux := 
forall (waitTicks_pre: Z) (startTime_pre: Z) (node_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (g: Z) (a: Z) (pu: Z) (un: Z) (PreH1 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) <= ULLONG_MAX)) (PreH2 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) >= 0)) (PreH3 : ((waitTicks_pre * g ) <= ULLONG_MAX)) (PreH4 : ((waitTicks_pre * g ) >= 0)) ,
  (task_store sg &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (unsigned_last_nbits ((startTime_pre + ((unsigned_last_nbits ((waitTicks_pre * g )) (64)) ÷ 100 ) )) (64)))
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> un)
  **  (store_task_sorted_dll sg l )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> g)
|--
  “ ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) = (startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) )) ” 
  &&  “ ((unsigned_last_nbits ((startTime_pre + ((unsigned_last_nbits ((waitTicks_pre * g )) (64)) ÷ 100 ) )) (64)) = (startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) )) ” 
  &&  “ ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) <= ULLONG_MAX) ” 
  &&  “ ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) >= 0) ” 
  &&  “ ((waitTicks_pre * g ) <= ULLONG_MAX) ” 
  &&  “ ((waitTicks_pre * g ) >= 0) ”
  &&  (task_store sg &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> (startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ))
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> un)
  **  (store_task_sorted_dll sg l )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> g)
.

Definition OsAdd2SortLink_partial_solve_wit_2 := OsAdd2SortLink_partial_solve_wit_2_pure -> OsAdd2SortLink_partial_solve_wit_2_aux.

Definition OsAdd2SortLink_partial_solve_wit_3_pure := 
forall (type_pre: Z) (waitTicks_pre: Z) (startTime_pre: Z) (node_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (g: Z) (a: Z) (pu: Z) (un: Z) (PreH1 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) <= ULLONG_MAX)) (PreH2 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) >= 0)) (PreH3 : ((waitTicks_pre * g ) <= ULLONG_MAX)) (PreH4 : ((waitTicks_pre * g ) >= 0)) ,
  ((( &( "startTime" ) )) # UInt64  |-> startTime_pre)
  **  ((( &( "waitTicks" ) )) # UInt64  |-> waitTicks_pre)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (storesortedLinkTaskNode task_store sg &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ))) )
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> ( &( "g_taskSortLink" ) ))
  **  ((( &( "type" ) )) # Int  |-> type_pre)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> un)
  **  (store_task_sorted_dll sg l )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> g)
|--
  “ (( &( "g_taskSortLink" ) ) = ( &( "g_taskSortLink" ) )) ”
.

Definition OsAdd2SortLink_partial_solve_wit_3_aux := 
forall (waitTicks_pre: Z) (startTime_pre: Z) (node_pre: Z) (l: (@list (@DL_Node (@sortedLinkNode Z)))) (sg: StableGlobVars) (g: Z) (a: Z) (pu: Z) (un: Z) (PreH1 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) <= ULLONG_MAX)) (PreH2 : ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) >= 0)) (PreH3 : ((waitTicks_pre * g ) <= ULLONG_MAX)) (PreH4 : ((waitTicks_pre * g ) >= 0)) ,
  (storesortedLinkTaskNode task_store sg &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ))) )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> un)
  **  (store_task_sorted_dll sg l )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> g)
|--
  “ (( &( "g_taskSortLink" ) ) = ( &( "g_taskSortLink" ) )) ” 
  &&  “ ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) <= ULLONG_MAX) ” 
  &&  “ ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ) >= 0) ” 
  &&  “ ((waitTicks_pre * g ) <= ULLONG_MAX) ” 
  &&  “ ((waitTicks_pre * g ) >= 0) ”
  &&  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> un)
  **  (store_task_sorted_dll sg l )
  **  (storesortedLinkTaskNode task_store sg &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((startTime_pre + ((waitTicks_pre * g ) ÷ 100 ) ))) )
  **  ((( &( "g_sysClock" ) )) # UInt64  |-> g)
.

Definition OsAdd2SortLink_partial_solve_wit_3 := OsAdd2SortLink_partial_solve_wit_3_pure -> OsAdd2SortLink_partial_solve_wit_3_aux.

Definition OsAdd2SortLink_which_implies_wit_1 := 
(
forall (sg: StableGlobVars) (t: Z) (a: Z) (node: Z) ,
  (storesortedLinkTaskNode task_store sg &((node)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (task_store sg &((node)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
) \/
(
forall (sg: StableGlobVars) (t: Z) (a: Z) (node: Z) ,
  (storesortedLinkTaskNode task_store sg &((node)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (task_store sg &((node)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
).

Definition OsAdd2SortLink_which_implies_wit_1_split_goal_spatial := 
forall (sg: StableGlobVars) (t: Z) (a: Z) (node: Z) ,
  (storesortedLinkTaskNode task_store sg &((node)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (task_store sg &((node)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
.

Definition OsAdd2SortLink_which_implies_wit_2 := 
(
forall (sg: StableGlobVars) (g: Z) (a: Z) (node: Z) (node_responseTime: Z) (startTime: Z) (waitTicks: Z) (PreH1 : (node_responseTime = (startTime + ((waitTicks * g ) ÷ 100 ) ))) ,
  (task_store sg &((node)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> node_responseTime)
|--
  (storesortedLinkTaskNode task_store sg &((node)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((startTime + ((waitTicks * g ) ÷ 100 ) ))) )
) \/
(
forall (sg: StableGlobVars) (g: Z) (a: Z) (node: Z) (node_responseTime: Z) (startTime: Z) (waitTicks: Z) (PreH1 : (node_responseTime = (startTime + ((waitTicks * g ) ÷ 100 ) ))) ,
  (task_store sg &((node)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> node_responseTime)
|--
  (storesortedLinkTaskNode task_store sg &((node)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((startTime + ((waitTicks * g ) ÷ 100 ) ))) )
).

Definition OsAdd2SortLink_which_implies_wit_2_split_goal_spatial := 
forall (sg: StableGlobVars) (g: Z) (a: Z) (node: Z) (node_responseTime: Z) (startTime: Z) (waitTicks: Z) (PreH1 : (node_responseTime = (startTime + ((waitTicks * g ) ÷ 100 ) ))) ,
  (task_store sg &((node)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> node_responseTime)
|--
  (storesortedLinkTaskNode task_store sg &((node)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((startTime + ((waitTicks * g ) ÷ 100 ) ))) )
.

Definition OsAddNode2SortLink_derive_taskSpec_by_highSpec := 
forall (sortList_pre: Z) (sortLinkHead_pre: Z) (l_taskSpec: (@list (@DL_Node (@sortedLinkNode Z)))) (sg_taskSpec: StableGlobVars) (t_taskSpec: Z) (a_taskSpec: Z) ,
  EX un pu,
  “ (sortLinkHead_pre = ( &( "g_taskSortLink" ) )) ”
  &&  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> pu)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> un)
  **  (store_task_sorted_dll sg_taskSpec l_taskSpec )
  **  (storesortedLinkTaskNode task_store sg_taskSpec &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a_taskSpec) (t_taskSpec)) )
|--
EX (A: Type) ,
EX (a_highSpec: A) (t_highSpec: Z) (storeA_highSpec: (Z -> (A -> Assertion))) (l_highSpec: (@list (@DL_Node (@sortedLinkNode A)))) ,
  (EX un_2 pu_2,
  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> pu_2)
  **  ((&((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> un_2)
  **  (store_sorted_dll storeA_highSpec &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l_highSpec )
  **  (storesortedLinkNode storeA_highSpec &((sortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a_highSpec) (t_highSpec)) ))
  **
  ((EX l1_2 l2_2,
  “ (l_highSpec = (app (l1_2) (l2_2))) ”
  &&  (store_sorted_dll storeA_highSpec &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (app (l1_2) ((cons ((Build_DL_Node ((mksortedLinkNode (a_highSpec) (t_highSpec))) (sortList_pre))) (l2_2)))) ))
  -*
  (EX l1 l2,
  “ (l_taskSpec = (app (l1) (l2))) ”
  &&  (store_task_sorted_dll sg_taskSpec (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a_taskSpec) (t_taskSpec))) (sortList_pre))) (l2)))) )))
.

Module Type VC_Correct.

Include los_sortlink_Strategy_Correct.

Axiom proof_of_OsAdd2SortLink_safety_wit_1 : OsAdd2SortLink_safety_wit_1.
Axiom proof_of_OsAdd2SortLink_safety_wit_2 : OsAdd2SortLink_safety_wit_2.
Axiom proof_of_OsAdd2SortLink_return_wit_1 : OsAdd2SortLink_return_wit_1.
Axiom proof_of_OsAdd2SortLink_partial_solve_wit_1 : OsAdd2SortLink_partial_solve_wit_1.
Axiom proof_of_OsAdd2SortLink_partial_solve_wit_2_pure : OsAdd2SortLink_partial_solve_wit_2_pure.
Axiom proof_of_OsAdd2SortLink_partial_solve_wit_2 : OsAdd2SortLink_partial_solve_wit_2.
Axiom proof_of_OsAdd2SortLink_partial_solve_wit_3_pure : OsAdd2SortLink_partial_solve_wit_3_pure.
Axiom proof_of_OsAdd2SortLink_partial_solve_wit_3 : OsAdd2SortLink_partial_solve_wit_3.
Axiom proof_of_OsAdd2SortLink_which_implies_wit_1 : OsAdd2SortLink_which_implies_wit_1.
Axiom proof_of_OsAdd2SortLink_which_implies_wit_2 : OsAdd2SortLink_which_implies_wit_2.
Axiom proof_of_OsAddNode2SortLink_derive_taskSpec_by_highSpec : OsAddNode2SortLink_derive_taskSpec_by_highSpec.

End VC_Correct.
