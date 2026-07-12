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

(*----- Function OsDeleteSortLink -----*)

Definition OsDeleteSortLink_safety_wit_1 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v: Z) (v_pstNext: Z) (v_2: Z) (PreH1 : (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH2 : (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH3 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )) ,
  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition OsDeleteSortLink_safety_wit_2 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v: Z) (v_pstNext: Z) (v_2: Z) (PreH1 : (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH2 : (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH3 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )) ,
  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition OsDeleteSortLink_return_wit_1 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v_pstNext: Z) (v_5: Z) (v_6: Z) (PreH1 : (v_6 = 0)) (PreH2 : (v_5 = 0)) (PreH3 : (t <= g)) (PreH4 : (t <> (unsigned_last_nbits ((-1)) (64)))) (PreH5 : (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH6 : (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH7 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )) ,
  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_6)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_5)
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  EX (v_4: Z)  (v_3: Z) ,
  “ (t <> (unsigned_last_nbits ((-1)) (64))) ” 
  &&  “ (t <= g) ” 
  &&  “ (v_3 = 0) ” 
  &&  “ (v_4 = 0) ”
  &&  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_3)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_4)
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_return_wit_2 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v_pstNext: Z) (v_5: Z) (v_6: Z) (PreH1 : (v_6 = 0)) (PreH2 : (v_5 = 0)) (PreH3 : (t > g)) (PreH4 : (t <> (unsigned_last_nbits ((-1)) (64)))) (PreH5 : (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH6 : (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH7 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )) ,
  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_6)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_5)
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  EX (v_2: Z)  (v: Z) ,
  “ (t <> (unsigned_last_nbits ((-1)) (64))) ” 
  &&  “ (t > g) ” 
  &&  “ (v = 0) ” 
  &&  “ (v_2 = 0) ”
  &&  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_2)
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) ((unsigned_last_nbits ((-1)) (64)))) )
  **  (store_sorted_dll storeA x (app (l1) (l2)) )
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_return_wit_3 := 
(
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v_5: Z) (v_pstNext: Z) (v_6: Z) (PreH1 : (t = (unsigned_last_nbits ((-1)) (64)))) (PreH2 : (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH3 : (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )) ,
  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_6)
  **  ((&((v_6)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_5)
  **  ((&((v_5)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v_5 x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_6 (map (sortedLinkNodeMapping) (l1)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  “ (t = (unsigned_last_nbits ((-1)) (64))) ”
  &&  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
) \/
(
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (v_pstPrev: Z) (v_5: Z) (v_pstNext: Z) (v_6: Z) (PreH1 : (t = (unsigned_last_nbits ((-1)) (64)))) (PreH2 : (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH3 : (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )) ,
  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_6)
  **  ((&((v_6)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_5)
  **  ((&((v_5)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v_5 x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_6 (map (sortedLinkNodeMapping) (l1)) )
|--
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
).

Definition OsDeleteSortLink_return_wit_3_split_goal_spatial := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (v_pstPrev: Z) (v_5: Z) (v_pstNext: Z) (v_6: Z) (PreH1 : (t = (unsigned_last_nbits ((-1)) (64)))) (PreH2 : (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH3 : (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )) ,
  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_6)
  **  ((&((v_6)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_5)
  **  ((&((v_5)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v_5 x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_6 (map (sortedLinkNodeMapping) (l1)) )
|--
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
.

Definition OsDeleteSortLink_partial_solve_wit_1 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) ,
  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
  **  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
|--
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_partial_solve_wit_2 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (PreH1 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )) ,
  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) ”
  &&  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_partial_solve_wit_3 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v: Z) (v_pstNext: Z) (v_2: Z) (PreH1 : (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH2 : (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH3 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )) ,
  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  “ (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) ”
  &&  (storesortedLinkNode storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_partial_solve_wit_4_pure := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v: Z) (v_pstNext: Z) (v_2: Z) (PreH1 : (t > g)) (PreH2 : (t <> (unsigned_last_nbits ((-1)) (64)))) (PreH3 : (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH5 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )) ,
  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) ” 
  &&  “ (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ”
.

Definition OsDeleteSortLink_partial_solve_wit_4_aux := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v: Z) (v_pstNext: Z) (v_2: Z) (PreH1 : (t > g)) (PreH2 : (t <> (unsigned_last_nbits ((-1)) (64)))) (PreH3 : (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH5 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )) ,
  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) ” 
  &&  “ (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (t > g) ” 
  &&  “ (t <> (unsigned_last_nbits ((-1)) (64))) ” 
  &&  “ (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) ”
  &&  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_partial_solve_wit_4 := OsDeleteSortLink_partial_solve_wit_4_pure -> OsDeleteSortLink_partial_solve_wit_4_aux.

Definition OsDeleteSortLink_partial_solve_wit_5_pure := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v: Z) (v_pstNext: Z) (v_2: Z) (PreH1 : (t <= g)) (PreH2 : (t <> (unsigned_last_nbits ((-1)) (64)))) (PreH3 : (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH5 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )) ,
  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) ” 
  &&  “ (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ”
.

Definition OsDeleteSortLink_partial_solve_wit_5_aux := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v: Z) (v_pstNext: Z) (v_2: Z) (PreH1 : (t <= g)) (PreH2 : (t <> (unsigned_last_nbits ((-1)) (64)))) (PreH3 : (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH5 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )) ,
  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) ” 
  &&  “ (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (t <= g) ” 
  &&  “ (t <> (unsigned_last_nbits ((-1)) (64))) ” 
  &&  “ (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) ”
  &&  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((node_pre)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v_2 (map (sortedLinkNodeMapping) (l1)) )
  **  (storeA &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_partial_solve_wit_5 := OsDeleteSortLink_partial_solve_wit_5_pure -> OsDeleteSortLink_partial_solve_wit_5_aux.

Definition OsDeleteSortLink_partial_solve_wit_6 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v_pstNext: Z) (PreH1 : (t <= g)) (PreH2 : (t <> (unsigned_last_nbits ((-1)) (64)))) (PreH3 : (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH5 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )) ,
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  “ (t <= g) ” 
  &&  “ (t <> (unsigned_last_nbits ((-1)) (64))) ” 
  &&  “ (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) ”
  &&  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> o)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_partial_solve_wit_7 := 
forall (A: Type) (node_pre: Z) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (g: Z) (o: Z) (t: Z) (x: Z) (v_pstPrev: Z) (v_pstNext: Z) (PreH1 : (t > g)) (PreH2 : (t <> (unsigned_last_nbits ((-1)) (64)))) (PreH3 : (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH5 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )) ,
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
|--
  “ (t > g) ” 
  &&  “ (t <> (unsigned_last_nbits ((-1)) (64))) ” 
  &&  “ (v_pstNext = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (v_pstPrev = &((node_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) ) ”
  &&  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node_pre))) (l2)))) )
  **  ((( &( "g_schedResponseTime" ) )) # UInt64  |-> g)
  **  ((( &( "OS_SCHED_MAX_RESPONSE_TIME" ) )) # UInt64  |-> o)
.

Definition OsDeleteSortLink_which_implies_wit_1 := 
(
forall (A: Type) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node: Z) ,
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node))) (l2)))) )
|--
  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node))) (l2)))) ) ”
  &&  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((node)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
) \/
(
forall (A: Type) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node: Z) ,
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node))) (l2)))) )
|--
  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node))) (l2)))) ) ”
  &&  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((node)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
).

Definition OsDeleteSortLink_which_implies_wit_1_split_goal_1 := 
forall (A: Type) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node: Z) ,
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node))) (l2)))) )
|--
  “ (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node))) (l2)))) ) ”
.

Definition OsDeleteSortLink_which_implies_wit_1_split_goal_spatial := 
forall (A: Type) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node: Z) ,
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node))) (l2)))) )
|--
  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((node)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
.

Definition OsDeleteSortLink_which_implies_wit_2 := 
(
forall (A: Type) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node: Z) ,
  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((node)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
|--
  EX (v_pstPrev: Z)  (v_2: Z)  (v_pstNext: Z)  (v: Z) ,
  “ (v_pstNext = &((node)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (v_pstPrev = &((node)  # "SortLinkList" ->ₛ "sortLinkNode")) ”
  &&  ((&((node)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v_2 x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v (map (sortedLinkNodeMapping) (l1)) )
  **  (storesortedLinkNode storeA &((node)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
) \/
(
forall (A: Type) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node: Z) ,
  (store_dll (storesortedLinkNode (storeA)) x (app ((map (sortedLinkNodeMapping) (l1))) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (&((node)  # "SortLinkList" ->ₛ "sortLinkNode")))) ((map (sortedLinkNodeMapping) (l2)))))) )
|--
  EX (v_2: Z)  (v: Z) ,
  ((&((node)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> &((node)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((&((node)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((node)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v_2 x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v (map (sortedLinkNodeMapping) (l1)) )
  **  (storesortedLinkNode storeA &((node)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
).

Definition OsDeleteSortLink_which_implies_wit_3 := 
(
forall (A: Type) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (node: Z) ,
  (storesortedLinkNode storeA &((node)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((node)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
) \/
(
forall (A: Type) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (node: Z) ,
  (storesortedLinkNode storeA &((node)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((node)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
).

Definition OsDeleteSortLink_which_implies_wit_3_split_goal_spatial := 
forall (A: Type) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (node: Z) ,
  (storesortedLinkNode storeA &((node)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )
|--
  (storeA &((node)  # "SortLinkList" ->ₛ "sortLinkNode") a )
  **  ((&((node)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
.

Definition OsDeleteSortLink_which_implies_wit_4 := 
(
forall (A: Type) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node: Z) (v: Z) (v_pstNext: Z) (v_2: Z) (v_pstPrev: Z) (PreH1 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node))) (l2)))) )) (PreH2 : (v_pstNext = &((node)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH3 : (v_pstPrev = &((node)  # "SortLinkList" ->ₛ "sortLinkNode"))) ,
  ((&((node)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  ((&((node)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v_2 x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v (map (sortedLinkNodeMapping) (l1)) )
  **  (storeA &((node)  # "SortLinkList" ->ₛ "sortLinkNode") a )
|--
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node))) (l2)))) )
) \/
(
forall (A: Type) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node: Z) (v: Z) (v_pstNext: Z) (v_2: Z) (v_pstPrev: Z) (PreH1 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node))) (l2)))) )) (PreH2 : (v_pstNext = &((node)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH3 : (v_pstPrev = &((node)  # "SortLinkList" ->ₛ "sortLinkNode"))) ,
  ((&((node)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  ((&((node)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v_2 x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v (map (sortedLinkNodeMapping) (l1)) )
  **  (storeA &((node)  # "SortLinkList" ->ₛ "sortLinkNode") a )
|--
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node))) (l2)))) )
).

Definition OsDeleteSortLink_which_implies_wit_4_split_goal_spatial := 
forall (A: Type) (l2: (@list (@DL_Node (@sortedLinkNode A)))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (a: A) (storeA: (Z -> (A -> Assertion))) (t: Z) (x: Z) (node: Z) (v: Z) (v_pstNext: Z) (v_2: Z) (v_pstPrev: Z) (PreH1 : (increasingSortedNode (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node))) (l2)))) )) (PreH2 : (v_pstNext = &((node)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH3 : (v_pstPrev = &((node)  # "SortLinkList" ->ₛ "sortLinkNode"))) ,
  ((&((node)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstPrev")) # Ptr  |-> v)
  **  ((&((v)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> v_pstNext)
  **  ((&((node)  # "SortLinkList" ->ₛ "sortLinkNode" .ₛ "pstNext")) # Ptr  |-> v_2)
  **  ((&((v_2)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> v_pstPrev)
  **  ((&((node)  # "SortLinkList" ->ₛ "responseTime")) # UInt64  |-> t)
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) v_2 x (map (sortedLinkNodeMapping) (l2)) )
  **  (dllseg_shift (storesortedLinkNode (storeA)) x v (map (sortedLinkNodeMapping) (l1)) )
  **  (storeA &((node)  # "SortLinkList" ->ₛ "sortLinkNode") a )
|--
  (store_sorted_dll storeA x (app (l1) ((cons ((Build_DL_Node ((mksortedLinkNode (a) (t))) (node))) (l2)))) )
.

Module Type VC_Correct.

Include los_sortlink_Strategy_Correct.

Axiom proof_of_OsDeleteSortLink_safety_wit_1 : OsDeleteSortLink_safety_wit_1.
Axiom proof_of_OsDeleteSortLink_safety_wit_2 : OsDeleteSortLink_safety_wit_2.
Axiom proof_of_OsDeleteSortLink_return_wit_1 : OsDeleteSortLink_return_wit_1.
Axiom proof_of_OsDeleteSortLink_return_wit_2 : OsDeleteSortLink_return_wit_2.
Axiom proof_of_OsDeleteSortLink_return_wit_3 : OsDeleteSortLink_return_wit_3.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_1 : OsDeleteSortLink_partial_solve_wit_1.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_2 : OsDeleteSortLink_partial_solve_wit_2.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_3 : OsDeleteSortLink_partial_solve_wit_3.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_4_pure : OsDeleteSortLink_partial_solve_wit_4_pure.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_4 : OsDeleteSortLink_partial_solve_wit_4.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_5_pure : OsDeleteSortLink_partial_solve_wit_5_pure.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_5 : OsDeleteSortLink_partial_solve_wit_5.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_6 : OsDeleteSortLink_partial_solve_wit_6.
Axiom proof_of_OsDeleteSortLink_partial_solve_wit_7 : OsDeleteSortLink_partial_solve_wit_7.
Axiom proof_of_OsDeleteSortLink_which_implies_wit_1 : OsDeleteSortLink_which_implies_wit_1.
Axiom proof_of_OsDeleteSortLink_which_implies_wit_2 : OsDeleteSortLink_which_implies_wit_2.
Axiom proof_of_OsDeleteSortLink_which_implies_wit_3 : OsDeleteSortLink_which_implies_wit_3.
Axiom proof_of_OsDeleteSortLink_which_implies_wit_4 : OsDeleteSortLink_which_implies_wit_4.

End VC_Correct.
