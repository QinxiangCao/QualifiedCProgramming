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

(*----- Function OsSortLinkGetNextExpireTime -----*)

Definition OsSortLinkGetNextExpireTime_safety_wit_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : (increasingSortedNode l )) (PreH4 : (SysTick <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval = 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ False ”
.

Definition OsSortLinkGetNextExpireTime_safety_wit_2 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 0)) (PreH3 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH4 : (increasingSortedNode l )) (PreH5 : (SysTick <> 0)) (PreH6 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH7 : (retval <> 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ False ”
.

Definition OsSortLinkGetNextExpireTime_safety_wit_3 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : (increasingSortedNode l )) (PreH4 : (SysTick <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval <> 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OsSortLinkGetNextExpireTime_entail_wit_1 := 
(
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (pt: Z) (h: Z) (PreH1 : (increasingSortedNode l )) (PreH2 : (SysTick <> 0)) (PreH3 : (( &( "g_archTickTimer" ) ) <> 0)) ,
  ((( &( "list" ) )) # Ptr  |-> h)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ ((obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ” 
  &&  “ (increasingSortedNode l ) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
) \/
(
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (SysTick: Z) (h: Z) (PreH1 : (increasingSortedNode l )) (PreH2 : (SysTick <> 0)) (PreH3 : (( &( "g_archTickTimer" ) ) <> 0)) ,
  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ”
  &&  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
).

Definition OsSortLinkGetNextExpireTime_entail_wit_1_split_goal_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (SysTick: Z) (h: Z) (PreH1 : (increasingSortedNode l )) (PreH2 : (SysTick <> 0)) (PreH3 : (( &( "g_archTickTimer" ) ) <> 0)) ,
  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ”
.

Definition OsSortLinkGetNextExpireTime_entail_wit_1_split_goal_spatial := 
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (SysTick: Z) (PreH1 : (increasingSortedNode l )) (PreH2 : (SysTick <> 0)) (PreH3 : (( &( "g_archTickTimer" ) ) <> 0)) ,
  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_entail_wit_2_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (retval_2: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval_2 = 1)) (PreH3 : (increasingSortedNode l )) (PreH4 : (SysTick <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval_2 = 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  EX (a: (@DL_Node (@sortedLinkNode A)))  (l1: (@list (@DL_Node (@sortedLinkNode A))))  (retval: Z) ,
  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ” 
  &&  “ (increasingSortedNode l ) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_entail_wit_2_2 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 0)) (PreH3 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH4 : (increasingSortedNode l )) (PreH5 : (SysTick <> 0)) (PreH6 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH7 : (retval = 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ” 
  &&  “ (increasingSortedNode l ) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_entail_wit_3_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : (increasingSortedNode l )) (PreH4 : (SysTick <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval <> 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (increasingSortedNode l ) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (retval <> 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_entail_wit_3_2 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval_2 = 0)) (PreH3 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH4 : (increasingSortedNode l )) (PreH5 : (SysTick <> 0)) (PreH6 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH7 : (retval_2 <> 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  EX (retval: Z) ,
  “ ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (increasingSortedNode l ) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (retval <> 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_return_wit_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick_4: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval_3: Z) (h: Z) (SysTick_5: Z) (retval_4: Z) (x_lSpec_pstNext: Z) (retval: Z) (PreH1 : ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) <= retval_4)) (PreH2 : (retval = 0)) (PreH3 : (x_lSpec_pstNext = &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (SysTick_5 <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval_4 = (tick_getcycle_ret (ts)))) (PreH7 : (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH8 : (&((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH9 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH10 : (retval_2 = 0)) (PreH11 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH12 : (increasingSortedNode l )) (PreH13 : (SysTick_4 <> 0)) (PreH14 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH15 : (retval_2 = 0)) ,
  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext)
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_5)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_5 (timebase_turnover (ts)) att )
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  (EX (SysTick_2: Z) ,
  “ (SysTick_2 <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (l <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ ((getFirstNodeResponseTime (l)) <= (tick_getcycle_ret (ts))) ” 
  &&  “ (retval = 0) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att ))
  ||
  (EX (SysTick_3: Z) ,
  “ (SysTick_3 <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (l = (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 0) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_3)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_3 ts att ))
.

Definition OsSortLinkGetNextExpireTime_return_wit_2 := 
(
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick_4: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval_3: Z) (h: Z) (SysTick_5: Z) (retval_4: Z) (x_lSpec_pstNext: Z) (retval: Z) (PreH1 : ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) > retval_4)) (PreH2 : (retval = ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) - retval_4 ))) (PreH3 : (x_lSpec_pstNext = &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (SysTick_5 <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval_4 = (tick_getcycle_ret (ts)))) (PreH7 : (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH8 : (&((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH9 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH10 : (retval_2 = 0)) (PreH11 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH12 : (increasingSortedNode l )) (PreH13 : (SysTick_4 <> 0)) (PreH14 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH15 : (retval_2 = 0)) ,
  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext)
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_5)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_5 (timebase_turnover (ts)) att )
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  EX (SysTick: Z) ,
  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (l <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ ((getFirstNodeResponseTime (l)) > (tick_getcycle_ret (ts))) ” 
  &&  “ (retval = ((getFirstNodeResponseTime (l)) - (tick_getcycle_ret (ts)) )) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick (timebase_turnover (ts)) att )
) \/
(
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick_4: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval_3: Z) (h: Z) (SysTick_5: Z) (retval_4: Z) (x_lSpec_pstNext: Z) (retval: Z) (PreH1 : ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) > retval_4)) (PreH2 : (retval = ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) - retval_4 ))) (PreH3 : (x_lSpec_pstNext = &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (SysTick_5 <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval_4 = (tick_getcycle_ret (ts)))) (PreH7 : (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH8 : (&((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH9 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH10 : (retval_2 = 0)) (PreH11 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH12 : (increasingSortedNode l )) (PreH13 : (SysTick_4 <> 0)) (PreH14 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH15 : (retval_2 = 0)) ,
  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_5 (timebase_turnover (ts)) att )
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  “ (retval = ((getFirstNodeResponseTime (l)) - (tick_getcycle_ret (ts)) )) ” 
  &&  “ ((getFirstNodeResponseTime (l)) > (tick_getcycle_ret (ts))) ” 
  &&  “ (l <> (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_5 (timebase_turnover (ts)) att )
).

Definition OsSortLinkGetNextExpireTime_return_wit_2_split_goal_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick_4: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval_3: Z) (h: Z) (SysTick_5: Z) (retval_4: Z) (x_lSpec_pstNext: Z) (retval: Z) (PreH1 : ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) > retval_4)) (PreH2 : (retval = ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) - retval_4 ))) (PreH3 : (x_lSpec_pstNext = &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (SysTick_5 <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval_4 = (tick_getcycle_ret (ts)))) (PreH7 : (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH8 : (&((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH9 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH10 : (retval_2 = 0)) (PreH11 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH12 : (increasingSortedNode l )) (PreH13 : (SysTick_4 <> 0)) (PreH14 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH15 : (retval_2 = 0)) ,
  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_5 (timebase_turnover (ts)) att )
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  “ (retval = ((getFirstNodeResponseTime (l)) - (tick_getcycle_ret (ts)) )) ”
.

Definition OsSortLinkGetNextExpireTime_return_wit_2_split_goal_2 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick_4: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval_3: Z) (h: Z) (SysTick_5: Z) (retval_4: Z) (x_lSpec_pstNext: Z) (retval: Z) (PreH1 : ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) > retval_4)) (PreH2 : (retval = ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) - retval_4 ))) (PreH3 : (x_lSpec_pstNext = &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (SysTick_5 <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval_4 = (tick_getcycle_ret (ts)))) (PreH7 : (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH8 : (&((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH9 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH10 : (retval_2 = 0)) (PreH11 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH12 : (increasingSortedNode l )) (PreH13 : (SysTick_4 <> 0)) (PreH14 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH15 : (retval_2 = 0)) ,
  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_5 (timebase_turnover (ts)) att )
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  “ ((getFirstNodeResponseTime (l)) > (tick_getcycle_ret (ts))) ”
.

Definition OsSortLinkGetNextExpireTime_return_wit_2_split_goal_3 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick_4: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval_3: Z) (h: Z) (SysTick_5: Z) (retval_4: Z) (x_lSpec_pstNext: Z) (retval: Z) (PreH1 : ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) > retval_4)) (PreH2 : (retval = ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) - retval_4 ))) (PreH3 : (x_lSpec_pstNext = &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (SysTick_5 <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval_4 = (tick_getcycle_ret (ts)))) (PreH7 : (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH8 : (&((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH9 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH10 : (retval_2 = 0)) (PreH11 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH12 : (increasingSortedNode l )) (PreH13 : (SysTick_4 <> 0)) (PreH14 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH15 : (retval_2 = 0)) ,
  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_5 (timebase_turnover (ts)) att )
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  “ (l <> (@nil (@DL_Node (@sortedLinkNode A)))) ”
.

Definition OsSortLinkGetNextExpireTime_return_wit_2_split_goal_spatial := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick_4: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval_3: Z) (h: Z) (SysTick_5: Z) (retval_4: Z) (x_lSpec_pstNext: Z) (retval: Z) (PreH1 : ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) > retval_4)) (PreH2 : (retval = ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) - retval_4 ))) (PreH3 : (x_lSpec_pstNext = &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (SysTick_5 <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval_4 = (tick_getcycle_ret (ts)))) (PreH7 : (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH8 : (&((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH9 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH10 : (retval_2 = 0)) (PreH11 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH12 : (increasingSortedNode l )) (PreH13 : (SysTick_4 <> 0)) (PreH14 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH15 : (retval_2 = 0)) ,
  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_5 (timebase_turnover (ts)) att )
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_5 (timebase_turnover (ts)) att )
.

Definition OsSortLinkGetNextExpireTime_return_wit_3 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick_4: Z) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : (increasingSortedNode l )) (PreH4 : (SysTick_4 <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval <> 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_4)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_4 ts att )
|--
  (EX (SysTick_2: Z) ,
  “ (SysTick_2 <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (l <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ ((getFirstNodeResponseTime (l)) <= (tick_getcycle_ret (ts))) ” 
  &&  “ (0 = 0) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att ))
  ||
  (EX (SysTick_3: Z) ,
  “ (SysTick_3 <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (l = (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (0 = 0) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_3)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_3 ts att ))
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_1 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (PreH1 : (SysTick <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)) ,
  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_2 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (pt: Z) (h: Z) (PreH1 : ((obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH2 : (increasingSortedNode l )) (PreH3 : (SysTick <> 0)) (PreH4 : (( &( "g_archTickTimer" ) ) <> 0)) ,
  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ (increasingSortedNode l ) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_3 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (PreH1 : (increasingSortedNode l )) (PreH2 : (SysTick <> 0)) (PreH3 : (( &( "g_archTickTimer" ) ) <> 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ (increasingSortedNode l ) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_4 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 0)) (PreH3 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH4 : (increasingSortedNode l )) (PreH5 : (SysTick <> 0)) (PreH6 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH7 : (retval = 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ” 
  &&  “ (increasingSortedNode l ) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_5 := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (PreH1 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH2 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH3 : (retval = 0)) (PreH4 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH5 : (increasingSortedNode l )) (PreH6 : (SysTick <> 0)) (PreH7 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH8 : (retval = 0)) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ” 
  &&  “ (increasingSortedNode l ) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_6_pure := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (h: Z) (PreH1 : (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH2 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH3 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH4 : (retval = 0)) (PreH5 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH6 : (increasingSortedNode l )) (PreH7 : (SysTick <> 0)) (PreH8 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH9 : (retval = 0)) ,
  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "listSorted" ) )) # Ptr  |-> retval_2)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_6_aux := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (h: Z) (PreH1 : (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH2 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH3 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH4 : (retval = 0)) (PreH5 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH6 : (increasingSortedNode l )) (PreH7 : (SysTick <> 0)) (PreH8 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH9 : (retval = 0)) ,
  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
|--
  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ” 
  &&  “ (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ” 
  &&  “ (increasingSortedNode l ) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (retval = 0) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick ts att )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_6 := OsSortLinkGetNextExpireTime_partial_solve_wit_6_pure -> OsSortLinkGetNextExpireTime_partial_solve_wit_6_aux.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_7_pure := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval: Z) (h: Z) (SysTick_2: Z) (retval_3: Z) (PreH1 : (SysTick_2 <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH3 : (retval_3 = (tick_getcycle_ret (ts)))) (PreH4 : (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH5 : (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH6 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH7 : (retval_2 = 0)) (PreH8 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH9 : (increasingSortedNode l )) (PreH10 : (SysTick <> 0)) (PreH11 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH12 : (retval_2 = 0)) ,
  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att )
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "listSorted" ) )) # Ptr  |-> retval)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  “ (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = &((retval)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ”
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_7_aux := 
forall (A: Type) (sortLinkHead_pre: Z) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (SysTick: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval: Z) (h: Z) (SysTick_2: Z) (retval_3: Z) (PreH1 : (SysTick_2 <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH3 : (retval_3 = (tick_getcycle_ret (ts)))) (PreH4 : (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH5 : (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH6 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH7 : (retval_2 = 0)) (PreH8 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH9 : (increasingSortedNode l )) (PreH10 : (SysTick <> 0)) (PreH11 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH12 : (retval_2 = 0)) ,
  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
|--
  “ (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = &((retval)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (SysTick_2 <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (retval_3 = (tick_getcycle_ret (ts))) ” 
  &&  “ (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ” 
  &&  “ (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ” 
  &&  “ (increasingSortedNode l ) ” 
  &&  “ (SysTick <> 0) ” 
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((retval)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> &((retval)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att )
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_7 := OsSortLinkGetNextExpireTime_partial_solve_wit_7_pure -> OsSortLinkGetNextExpireTime_partial_solve_wit_7_aux.

Definition OsSortLinkGetNextExpireTime_which_implies_wit_1 := 
(
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead: Z) ,
  (store_sorted_dll storeA &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") l )
|--
  EX (pt: Z)  (h: Z) ,
  “ (increasingSortedNode l ) ”
  &&  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
) \/
(
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead: Z) ,
  (store_sorted_dll storeA &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") l )
|--
  EX (pt: Z)  (h: Z) ,
  “ (increasingSortedNode l ) ”
  &&  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
).

Definition OsSortLinkGetNextExpireTime_which_implies_wit_2 := 
(
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (pt: Z) (h: Z) (sortLinkHead: Z) ,
  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
|--
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
) \/
(
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (pt: Z) (h: Z) (sortLinkHead: Z) ,
  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
|--
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
).

Definition OsSortLinkGetNextExpireTime_which_implies_wit_2_split_goal_spatial := 
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (pt: Z) (h: Z) (sortLinkHead: Z) ,
  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
|--
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
.

Definition OsSortLinkGetNextExpireTime_which_implies_wit_3 := 
(
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead: Z) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
|--
  EX (h: Z) ,
  “ (h = (obtian_first_pointer (&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ”
  &&  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) h &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
) \/
(
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead: Z) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
|--
  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((&(((obtian_first_pointer (&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) (obtian_first_pointer (&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
).

Definition OsSortLinkGetNextExpireTime_which_implies_wit_3_split_goal_spatial := 
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead: Z) ,
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
|--
  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((&(((obtian_first_pointer (&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) (obtian_first_pointer (&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
.

Definition OsSortLinkGetTargetExpireTime_derive_lSpec_by_highSpec := 
forall (A: Type) ,
forall (targetSortList_pre: Z) (currTime_pre: Z) (l_lSpec: (@list (@DL_Node (@sortedLinkNode A)))) (x_lSpec: Z) (storeA_lSpec: (Z -> (A -> Assertion))) ,
  EX x_lSpec_pstNext,
  “ (x_lSpec_pstNext = &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ” 
  &&  “ (l_lSpec <> nil) ”
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA_lSpec)) &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x_lSpec l_lSpec )
  **  ((&((x_lSpec)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext)
|--
EX (A: Type) ,
EX (storeA_highSpec: (Z -> (A -> Assertion))) (a_highSpec: A) (t_highSpec: Z) ,
  ((storesortedLinkNode storeA_highSpec &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a_highSpec) (t_highSpec)) ))
  **
  (((EX retval_2,
  “ (currTime_pre < t_highSpec) ” 
  &&  “ (retval_2 = (t_highSpec - currTime_pre )) ”
  &&  (storesortedLinkNode storeA_highSpec &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a_highSpec) (t_highSpec)) ))
  ||
  (EX retval_2,
  “ (currTime_pre >= t_highSpec) ” 
  &&  “ (retval_2 = 0) ”
  &&  (storesortedLinkNode storeA_highSpec &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a_highSpec) (t_highSpec)) )))
  -*
  ((EX x_lSpec_pstNext_2 retval,
  “ ((getFirstNodeResponseTime (l_lSpec)) <= currTime_pre) ” 
  &&  “ (retval = 0) ” 
  &&  “ (x_lSpec_pstNext_2 = &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ”
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA_lSpec)) &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x_lSpec l_lSpec )
  **  ((&((x_lSpec)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext_2))
  ||
  (EX x_lSpec_pstNext_3 retval,
  “ ((getFirstNodeResponseTime (l_lSpec)) > currTime_pre) ” 
  &&  “ (retval = ((getFirstNodeResponseTime (l_lSpec)) - currTime_pre )) ” 
  &&  “ (x_lSpec_pstNext_3 = &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ”
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA_lSpec)) &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x_lSpec l_lSpec )
  **  ((&((x_lSpec)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext_3))))
.

Definition LOS_ListEmpty_derive_getfirstSpec_by_highSpec := 
forall (A: Type) ,
forall (node_pre: Z) (l_getfirstSpec: (@list (@DL_Node A))) (storeA_getfirstSpec: (Z -> (A -> Assertion))) ,
  (store_dll storeA_getfirstSpec node_pre l_getfirstSpec )
|--
EX (A: Type) ,
EX (storeA_highSpec: (Z -> (A -> Assertion))) (l_highSpec: (@list (@DL_Node A))) ,
  ((store_dll storeA_highSpec node_pre l_highSpec ))
  **
  (((EX retval_2,
  “ (l_highSpec <> nil) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_dll storeA_highSpec node_pre l_highSpec ))
  ||
  (EX retval_2,
  “ (l_highSpec = nil) ” 
  &&  “ (retval_2 = 1) ”
  &&  (store_dll storeA_highSpec node_pre l_highSpec )))
  -*
  ((EX retval,
  “ (l_getfirstSpec = nil) ” 
  &&  “ (retval = 1) ”
  &&  (store_dll storeA_getfirstSpec node_pre l_getfirstSpec ))
  ||
  (EX a l1 retval,
  “ (l_getfirstSpec <> nil) ” 
  &&  “ (retval = 0) ” 
  &&  “ (l_getfirstSpec = (cons (a) (l1))) ”
  &&  (store_dll storeA_getfirstSpec node_pre (cons (a) (l1)) ))))
.

Module Type VC_Correct.

Include los_sortlink_Strategy_Correct.

Axiom proof_of_OsSortLinkGetNextExpireTime_safety_wit_1 : OsSortLinkGetNextExpireTime_safety_wit_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_safety_wit_2 : OsSortLinkGetNextExpireTime_safety_wit_2.
Axiom proof_of_OsSortLinkGetNextExpireTime_safety_wit_3 : OsSortLinkGetNextExpireTime_safety_wit_3.
Axiom proof_of_OsSortLinkGetNextExpireTime_entail_wit_1 : OsSortLinkGetNextExpireTime_entail_wit_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_entail_wit_2_1 : OsSortLinkGetNextExpireTime_entail_wit_2_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_entail_wit_2_2 : OsSortLinkGetNextExpireTime_entail_wit_2_2.
Axiom proof_of_OsSortLinkGetNextExpireTime_entail_wit_3_1 : OsSortLinkGetNextExpireTime_entail_wit_3_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_entail_wit_3_2 : OsSortLinkGetNextExpireTime_entail_wit_3_2.
Axiom proof_of_OsSortLinkGetNextExpireTime_return_wit_1 : OsSortLinkGetNextExpireTime_return_wit_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_return_wit_2 : OsSortLinkGetNextExpireTime_return_wit_2.
Axiom proof_of_OsSortLinkGetNextExpireTime_return_wit_3 : OsSortLinkGetNextExpireTime_return_wit_3.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_1 : OsSortLinkGetNextExpireTime_partial_solve_wit_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_2 : OsSortLinkGetNextExpireTime_partial_solve_wit_2.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_3 : OsSortLinkGetNextExpireTime_partial_solve_wit_3.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_4 : OsSortLinkGetNextExpireTime_partial_solve_wit_4.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_5 : OsSortLinkGetNextExpireTime_partial_solve_wit_5.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_6_pure : OsSortLinkGetNextExpireTime_partial_solve_wit_6_pure.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_6 : OsSortLinkGetNextExpireTime_partial_solve_wit_6.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_7_pure : OsSortLinkGetNextExpireTime_partial_solve_wit_7_pure.
Axiom proof_of_OsSortLinkGetNextExpireTime_partial_solve_wit_7 : OsSortLinkGetNextExpireTime_partial_solve_wit_7.
Axiom proof_of_OsSortLinkGetNextExpireTime_which_implies_wit_1 : OsSortLinkGetNextExpireTime_which_implies_wit_1.
Axiom proof_of_OsSortLinkGetNextExpireTime_which_implies_wit_2 : OsSortLinkGetNextExpireTime_which_implies_wit_2.
Axiom proof_of_OsSortLinkGetNextExpireTime_which_implies_wit_3 : OsSortLinkGetNextExpireTime_which_implies_wit_3.
Axiom proof_of_OsSortLinkGetTargetExpireTime_derive_lSpec_by_highSpec : OsSortLinkGetTargetExpireTime_derive_lSpec_by_highSpec.
Axiom proof_of_LOS_ListEmpty_derive_getfirstSpec_by_highSpec : LOS_ListEmpty_derive_getfirstSpec_by_highSpec.

End VC_Correct.
