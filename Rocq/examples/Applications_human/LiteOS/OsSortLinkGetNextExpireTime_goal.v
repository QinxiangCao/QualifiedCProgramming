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

(*----- Function OsSortLinkGetNextExpireTime -----*)

Definition OsSortLinkGetNextExpireTime_safety_wit_1 :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : (increasingSortedNode l )) (PreH4 : (SysTick_pre <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval = 0)),
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
|--
  “ False ”
.

Definition OsSortLinkGetNextExpireTime_safety_wit_2 :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 0)) (PreH3 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH4 : (increasingSortedNode l )) (PreH5 : (SysTick_pre <> 0)) (PreH6 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH7 : (retval <> 0)),
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
|--
  “ False ”
.

Definition OsSortLinkGetNextExpireTime_safety_wit_3 :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : (increasingSortedNode l )) (PreH4 : (SysTick_pre <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval <> 0)),
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OsSortLinkGetNextExpireTime_entail_wit_1 :=
(
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (pt: Z) (h: Z) (PreH1 : (increasingSortedNode l )) (PreH2 : (SysTick_pre <> 0)) (PreH3 : (( &( "g_archTickTimer" ) ) <> 0)),
  ((( &( "list" ) )) # Ptr  |-> h)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
|--
  “ ((obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ”
  &&  “ (increasingSortedNode l ) ”
  &&  “ (SysTick_pre <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
) \/
(
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (h: Z) (PreH1 : (increasingSortedNode l )) (PreH2 : (SysTick_pre <> 0)) (PreH3 : (( &( "g_archTickTimer" ) ) <> 0)),
  TT && emp 
|--
  “ (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ”
  &&  emp
).

Definition OsSortLinkGetNextExpireTime_entail_wit_1_split_goal_1 :=
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (h: Z) (PreH1 : (increasingSortedNode l )) (PreH2 : (SysTick_pre <> 0)) (PreH3 : (( &( "g_archTickTimer" ) ) <> 0)),
  (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
.

Definition OsSortLinkGetNextExpireTime_entail_wit_2_1 :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (retval_2: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval_2 = 1)) (PreH3 : (increasingSortedNode l )) (PreH4 : (SysTick_pre <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval_2 = 0)),
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
|--
  EX (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z),
  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  “ (retval = 0) ”
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ”
  &&  “ (increasingSortedNode l ) ”
  &&  “ (SysTick_pre <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (retval = 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
.

Definition OsSortLinkGetNextExpireTime_entail_wit_2_2 :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 0)) (PreH3 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH4 : (increasingSortedNode l )) (PreH5 : (SysTick_pre <> 0)) (PreH6 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH7 : (retval = 0)),
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
|--
  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  “ (retval = 0) ”
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ”
  &&  “ (increasingSortedNode l ) ”
  &&  “ (SysTick_pre <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (retval = 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
.

Definition OsSortLinkGetNextExpireTime_entail_wit_3_1 :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : (increasingSortedNode l )) (PreH4 : (SysTick_pre <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval <> 0)),
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
|--
  “ ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  “ (retval = 1) ”
  &&  “ (increasingSortedNode l ) ”
  &&  “ (SysTick_pre <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (retval <> 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
.

Definition OsSortLinkGetNextExpireTime_entail_wit_3_2 :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval_2 = 0)) (PreH3 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH4 : (increasingSortedNode l )) (PreH5 : (SysTick_pre <> 0)) (PreH6 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH7 : (retval_2 <> 0)),
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
|--
  EX (retval: Z),
  “ ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  “ (retval = 1) ”
  &&  “ (increasingSortedNode l ) ”
  &&  “ (SysTick_pre <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (retval <> 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
.

Definition OsSortLinkGetNextExpireTime_return_wit_1 :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval_3: Z) (h: Z) (SysTick_4: Z) (retval_4: Z) (x_lSpec_pstNext: Z) (retval: Z) (PreH1 : ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) <= retval_4)) (PreH2 : (retval = 0)) (PreH3 : (x_lSpec_pstNext = &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (SysTick_4 <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval_4 = (tick_getcycle_ret (ts)))) (PreH7 : (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH8 : (&((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH9 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH10 : (retval_2 = 0)) (PreH11 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH12 : (increasingSortedNode l )) (PreH13 : (SysTick_pre <> 0)) (PreH14 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH15 : (retval_2 = 0)),
  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext)
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_4)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_4 (timebase_turnover (ts)) att )
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  (EX (SysTick_2: Z),
  “ (SysTick_2 <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (l <> (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  “ ((getFirstNodeResponseTime (l)) <= (tick_getcycle_ret (ts))) ”
  &&  “ (retval = 0) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att ))
  ||
  (EX (SysTick_3: Z),
  “ (SysTick_3 <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (l = (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  “ (retval = 0) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_3)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_3 ts att ))
.

Definition OsSortLinkGetNextExpireTime_return_wit_2 :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval_3: Z) (h: Z) (SysTick_4: Z) (retval_4: Z) (x_lSpec_pstNext: Z) (retval: Z) (PreH1 : ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) > retval_4)) (PreH2 : (retval = ((getFirstNodeResponseTime ((map (sortedLinkNodeMapping) (l)))) - retval_4 ))) (PreH3 : (x_lSpec_pstNext = &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode"))) (PreH4 : (SysTick_4 <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval_4 = (tick_getcycle_ret (ts)))) (PreH7 : (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH8 : (&((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH9 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH10 : (retval_2 = 0)) (PreH11 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH12 : (increasingSortedNode l )) (PreH13 : (SysTick_pre <> 0)) (PreH14 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH15 : (retval_2 = 0)),
  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((retval_3)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext)
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_4)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_4 (timebase_turnover (ts)) att )
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
|--
  (EX (SysTick: Z),
  “ (SysTick <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (l <> (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  “ ((getFirstNodeResponseTime (l)) > (tick_getcycle_ret (ts))) ”
  &&  “ (retval = ((getFirstNodeResponseTime (l)) - (tick_getcycle_ret (ts)) )) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick (timebase_turnover (ts)) att ))
  ||
  (EX (SysTick_2: Z),
  “ (SysTick_2 <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (l <> (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  “ ((getFirstNodeResponseTime (l)) <= (tick_getcycle_ret (ts))) ”
  &&  “ (retval = 0) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att ))
  ||
  (EX (SysTick_3: Z),
  “ (SysTick_3 <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (l = (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  “ (retval = 0) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_3)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_3 ts att ))
.

Definition OsSortLinkGetNextExpireTime_return_wit_3 :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) = (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 1)) (PreH3 : (increasingSortedNode l )) (PreH4 : (SysTick_pre <> 0)) (PreH5 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH6 : (retval <> 0)),
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
|--
  (EX (SysTick: Z),
  “ (SysTick <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (l <> (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  “ ((getFirstNodeResponseTime (l)) > (tick_getcycle_ret (ts))) ”
  &&  “ (0 = ((getFirstNodeResponseTime (l)) - (tick_getcycle_ret (ts)) )) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick (timebase_turnover (ts)) att ))
  ||
  (EX (SysTick_2: Z),
  “ (SysTick_2 <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (l <> (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  “ ((getFirstNodeResponseTime (l)) <= (tick_getcycle_ret (ts))) ”
  &&  “ (0 = 0) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_2)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_2 (timebase_turnover (ts)) att ))
  ||
  (EX (SysTick_3: Z),
  “ (SysTick_3 <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (l = (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  “ (0 = 0) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_3)
  **  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_3 ts att ))
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_1 :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (PreH1 : (SysTick_pre <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)),
  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
|--
  “ (SysTick_pre <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  (store_sorted_dll storeA &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") l )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_2 :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (pt: Z) (h: Z) (PreH1 : ((obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH2 : (increasingSortedNode l )) (PreH3 : (SysTick_pre <> 0)) (PreH4 : (( &( "g_archTickTimer" ) ) <> 0)),
  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
|--
  “ (increasingSortedNode l ) ”
  &&  “ (SysTick_pre <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_3 :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (PreH1 : (increasingSortedNode l )) (PreH2 : (SysTick_pre <> 0)) (PreH3 : (( &( "g_archTickTimer" ) ) <> 0)),
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
|--
  “ (increasingSortedNode l ) ”
  &&  “ (SysTick_pre <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_4 :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (PreH1 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH2 : (retval = 0)) (PreH3 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH4 : (increasingSortedNode l )) (PreH5 : (SysTick_pre <> 0)) (PreH6 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH7 : (retval = 0)),
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
|--
  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  “ (retval = 0) ”
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ”
  &&  “ (increasingSortedNode l ) ”
  &&  “ (SysTick_pre <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (retval = 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_5 :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (PreH1 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH2 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH3 : (retval = 0)) (PreH4 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH5 : (increasingSortedNode l )) (PreH6 : (SysTick_pre <> 0)) (PreH7 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH8 : (retval = 0)),
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (cons (a) (l1)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
|--
  “ (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ”
  &&  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  “ (retval = 0) ”
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ”
  &&  “ (increasingSortedNode l ) ”
  &&  “ (SysTick_pre <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (retval = 0) ”
  &&  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_6_pure :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (h: Z) (PreH1 : (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH2 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH3 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH4 : (retval = 0)) (PreH5 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH6 : (increasingSortedNode l )) (PreH7 : (SysTick_pre <> 0)) (PreH8 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH9 : (retval = 0)),
  ((( &( "sortLinkHead" ) )) # Ptr  |-> sortLinkHead_pre)
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "listSorted" ) )) # Ptr  |-> retval_2)
  **  ((( &( "list" ) )) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((( &( "head" ) )) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
|--
  “ (SysTick_pre <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_6_aux :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval: Z) (retval_2: Z) (h: Z) (PreH1 : (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH2 : (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH3 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH4 : (retval = 0)) (PreH5 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH6 : (increasingSortedNode l )) (PreH7 : (SysTick_pre <> 0)) (PreH8 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH9 : (retval = 0)),
  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
|--
  “ (SysTick_pre <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ”
  &&  “ (&((retval_2)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ”
  &&  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  “ (retval = 0) ”
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ”
  &&  “ (increasingSortedNode l ) ”
  &&  “ (SysTick_pre <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (retval = 0) ”
  &&  ((( &( "SysTick" ) )) # Ptr  |-> SysTick_pre)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick_pre ts att )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_6 := OsSortLinkGetNextExpireTime_partial_solve_wit_6_pure -> OsSortLinkGetNextExpireTime_partial_solve_wit_6_aux.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_7_pure :=
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval: Z) (h: Z) (SysTick: Z) (retval_3: Z) (PreH1 : (SysTick <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH3 : (retval_3 = (tick_getcycle_ret (ts)))) (PreH4 : (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH5 : (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH6 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH7 : (retval_2 = 0)) (PreH8 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH9 : (increasingSortedNode l )) (PreH10 : (SysTick_pre <> 0)) (PreH11 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH12 : (retval_2 = 0)),
  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick (timebase_turnover (ts)) att )
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
forall (A: Type) (att: archTickTimer) (ts: tickState) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead_pre: Z) (SysTick_pre: Z) (a: (@DL_Node (@sortedLinkNode A))) (l1: (@list (@DL_Node (@sortedLinkNode A)))) (retval_2: Z) (retval: Z) (h: Z) (SysTick: Z) (retval_3: Z) (PreH1 : (SysTick <> 0)) (PreH2 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH3 : (retval_3 = (tick_getcycle_ret (ts)))) (PreH4 : (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH5 : (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))) (PreH6 : ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A))))) (PreH7 : (retval_2 = 0)) (PreH8 : ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1)))) (PreH9 : (increasingSortedNode l )) (PreH10 : (SysTick_pre <> 0)) (PreH11 : (( &( "g_archTickTimer" ) ) <> 0)) (PreH12 : (retval_2 = 0)),
  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick (timebase_turnover (ts)) att )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) h &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
|--
  “ (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = &((retval)  # "SortLinkList" ->ₛ "sortLinkNode")) ”
  &&  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  “ (SysTick <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (retval_3 = (tick_getcycle_ret (ts))) ”
  &&  “ (h = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ”
  &&  “ (&((retval)  # "SortLinkList" ->ₛ "sortLinkNode") = (obtian_first_pointer (&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ”
  &&  “ ((map (sortedLinkNodeMapping) (l)) <> (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  “ (retval_2 = 0) ”
  &&  “ ((map (sortedLinkNodeMapping) (l)) = (cons (a) (l1))) ”
  &&  “ (increasingSortedNode l ) ”
  &&  “ (SysTick_pre <> 0) ”
  &&  “ (( &( "g_archTickTimer" ) ) <> 0) ”
  &&  “ (retval_2 = 0) ”
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((retval)  # "SortLinkList" ->ₛ "sortLinkNode") &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
  **  ((&((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> &((retval)  # "SortLinkList" ->ₛ "sortLinkNode"))
  **  ((( &( "SysTick" ) )) # Ptr  |-> SysTick)
  **  (storeTick ( &( "g_archTickTimer" ) ) SysTick (timebase_turnover (ts)) att )
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead_pre)  # "SortLinkAttribute" ->ₛ "sortLink"))
.

Definition OsSortLinkGetNextExpireTime_partial_solve_wit_7 := OsSortLinkGetNextExpireTime_partial_solve_wit_7_pure -> OsSortLinkGetNextExpireTime_partial_solve_wit_7_aux.

Definition OsSortLinkGetNextExpireTime_which_implies_wit_1 :=
(
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead: Z),
  (store_sorted_dll storeA &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") l )
|--
  EX (pt: Z) (h: Z),
  “ (increasingSortedNode l ) ”
  &&  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
) \/
(
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead: Z),
  (store_sorted_dll storeA &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") l )
|--
  EX (pt: Z) (h: Z),
  “ (increasingSortedNode l ) ”
  &&  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
).

Definition OsSortLinkGetNextExpireTime_which_implies_wit_2 :=
(
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (pt: Z) (h: Z) (sortLinkHead: Z),
  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
|--
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
) \/
(
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (pt: Z) (h: Z) (sortLinkHead: Z),
  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
|--
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
).

Definition OsSortLinkGetNextExpireTime_which_implies_wit_2_split_goal_spatial :=
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (pt: Z) (h: Z) (sortLinkHead: Z),
  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstPrev")) # Ptr  |-> pt)
  **  (dllseg (storesortedLinkNode (storeA)) h &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") pt (map (sortedLinkNodeMapping) (l)) )
|--
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
.

Definition OsSortLinkGetNextExpireTime_which_implies_wit_3 :=
(
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead: Z),
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
|--
  EX (h: Z),
  “ (h = (obtian_first_pointer (&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l))))) ”
  &&  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> h)
  **  ((&((h)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) h &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
) \/
(
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead: Z),
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
|--
  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((&(((obtian_first_pointer (&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) (obtian_first_pointer (&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
).

Definition OsSortLinkGetNextExpireTime_which_implies_wit_3_split_goal_spatial :=
forall (A: Type) (l: (@list (@DL_Node (@sortedLinkNode A)))) (storeA: (Z -> (A -> Assertion))) (sortLinkHead: Z),
  (store_dll (storesortedLinkNode (storeA)) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
|--
  ((&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink" .ₛ "pstNext")) # Ptr  |-> (obtian_first_pointer (&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))
  **  ((&(((obtian_first_pointer (&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))))  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink"))
  **  (dllseg_shift_rev (storesortedLinkNode (storeA)) (obtian_first_pointer (&((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink")) ((map (sortedLinkNodeMapping) (l)))) &((sortLinkHead)  # "SortLinkAttribute" ->ₛ "sortLink") (map (sortedLinkNodeMapping) (l)) )
.

(* Shallow FunAssertion specs for OsSortLinkGetTargetExpireTime. *)
Definition OsSortLinkGetTargetExpireTime_sig : FuncSig := ([u64;  * struct "SortLinkList"], u64)%ctype.

Definition OsSortLinkGetTargetExpireTime_lSpec : Spec OsSortLinkGetTargetExpireTime_sig :=
  fun F =>
ALL A : Type,
ALL (storeA: (Z -> (A -> Assertion))),
ALL (x: Z),
ALL (l: (@list (@DL_Node (@sortedLinkNode A)))),
HoareFun ([u64;  * struct "SortLinkList"], u64)%ctype
  (fun '(currTime_pre, targetSortList_pre) =>
  (EX (x_pstNext: Z),
  “ (x_pstNext = &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ”
  &&  “ (l <> (@nil (@DL_Node (@sortedLinkNode A)))) ”
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x l )
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> x_pstNext)))
  (fun '(currTime_pre, targetSortList_pre) retval =>
(orp
  (EX (x_pstNext_2: Z),
  “ ((getFirstNodeResponseTime (l)) <= currTime_pre) ”
  &&  “ (retval = 0) ”
  &&  “ (x_pstNext_2 = &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ”
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x l )
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> x_pstNext_2))
  (EX (x_pstNext_3: Z),
  “ ((getFirstNodeResponseTime (l)) > currTime_pre) ”
  &&  “ (retval = ((getFirstNodeResponseTime (l)) - currTime_pre )) ”
  &&  “ (x_pstNext_3 = &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ”
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA)) &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x l )
  **  ((&((x)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> x_pstNext_3))))
  F.

Definition OsSortLinkGetTargetExpireTime_highSpec : Spec OsSortLinkGetTargetExpireTime_sig :=
  fun F =>
ALL A : Type,
ALL (storeA: (Z -> (A -> Assertion))),
ALL (a: A),
ALL (t: Z),
HoareFun ([u64;  * struct "SortLinkList"], u64)%ctype
  (fun '(currTime_pre, targetSortList_pre) =>
  ((storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) )))
  (fun '(currTime_pre, targetSortList_pre) retval =>
(orp
  (“ (currTime_pre < t) ”
  &&  “ (retval = (t - currTime_pre )) ”
  &&  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) ))
  (“ (currTime_pre >= t) ”
  &&  “ (retval = 0) ”
  &&  (storesortedLinkNode storeA &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a) (t)) ))))
  F.

Definition OsSortLinkGetTargetExpireTime_highSpec_entail_lSpec :=
forall (A: Type),
forall (currTime_pre: Z) (targetSortList_pre: Z) (storeA_lSpec: (Z -> (A -> Assertion))) (x_lSpec: Z) (l_lSpec: (@list (@DL_Node (@sortedLinkNode A)))),
  (EX (x_lSpec_pstNext: Z),
  “ (x_lSpec_pstNext = &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ”
  &&  “ (l_lSpec <> nil) ”
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA_lSpec)) &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x_lSpec l_lSpec )
  **  ((&((x_lSpec)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext))
|--
EX (A_2: Type) ,
EX (storeA_highSpec: (Z -> (A_2 -> Assertion)))(a_highSpec: A_2)(t_highSpec: Z),
  ((storesortedLinkNode storeA_highSpec &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a_highSpec) (t_highSpec)) ))
  **
  (ALL (retval: Z),
(orp
  (“ (currTime_pre < t_highSpec) ”
  &&  “ (retval = (t_highSpec - currTime_pre )) ”
  &&  (storesortedLinkNode storeA_highSpec &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a_highSpec) (t_highSpec)) ))
  (“ (currTime_pre >= t_highSpec) ”
  &&  “ (retval = 0) ”
  &&  (storesortedLinkNode storeA_highSpec &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") (mksortedLinkNode (a_highSpec) (t_highSpec)) )))
  -*
(orp
  (EX (x_lSpec_pstNext_2: Z),
  “ ((getFirstNodeResponseTime (l_lSpec)) <= currTime_pre) ”
  &&  “ (retval = 0) ”
  &&  “ (x_lSpec_pstNext_2 = &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ”
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA_lSpec)) &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x_lSpec l_lSpec )
  **  ((&((x_lSpec)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext_2))
  (EX (x_lSpec_pstNext_3: Z),
  “ ((getFirstNodeResponseTime (l_lSpec)) > currTime_pre) ”
  &&  “ (retval = ((getFirstNodeResponseTime (l_lSpec)) - currTime_pre )) ”
  &&  “ (x_lSpec_pstNext_3 = &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode")) ”
  &&  (dllseg_shift_rev (storesortedLinkNode (storeA_lSpec)) &((targetSortList_pre)  # "SortLinkList" ->ₛ "sortLinkNode") x_lSpec l_lSpec )
  **  ((&((x_lSpec)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> x_lSpec_pstNext_3))))
.

(* Shallow FunAssertion specs for LOS_ListEmpty. *)
Definition LOS_ListEmpty_sig : FuncSig := ([ * struct "LOS_DL_LIST"], i32)%ctype.

Definition LOS_ListEmpty_getfirstSpec : Spec LOS_ListEmpty_sig :=
  fun F =>
ALL A : Type,
ALL (storeA: (Z -> (A -> Assertion))),
ALL (l: (@list (@DL_Node A))),
HoareFun ([ * struct "LOS_DL_LIST"], i32)%ctype
  (fun node_pre =>
  ((store_dll storeA node_pre l )))
  (fun node_pre retval =>
(orp
  (“ (l = (@nil (@DL_Node A))) ”
  &&  “ (retval = 1) ”
  &&  (store_dll storeA node_pre l ))
  (EX (a: (@DL_Node A)) (l1: (@list (@DL_Node A))),
  “ (l <> (@nil (@DL_Node A))) ”
  &&  “ (retval = 0) ”
  &&  “ (l = (cons (a) (l1))) ”
  &&  (store_dll storeA node_pre (cons (a) (l1)) ))))
  F.

Definition LOS_ListEmpty_highSpec : Spec LOS_ListEmpty_sig :=
  fun F =>
ALL A : Type,
ALL (storeA: (Z -> (A -> Assertion))),
ALL (l: (@list (@DL_Node A))),
HoareFun ([ * struct "LOS_DL_LIST"], i32)%ctype
  (fun node_pre =>
  ((store_dll storeA node_pre l )))
  (fun node_pre retval =>
(orp
  (“ (l <> (@nil (@DL_Node A))) ”
  &&  “ (retval = 0) ”
  &&  (store_dll storeA node_pre l ))
  (“ (l = (@nil (@DL_Node A))) ”
  &&  “ (retval = 1) ”
  &&  (store_dll storeA node_pre l ))))
  F.

Definition LOS_ListEmpty_highSpec_entail_getfirstSpec :=
forall (A: Type),
forall (node_pre: Z) (storeA_getfirstSpec: (Z -> (A -> Assertion))) (l_getfirstSpec: (@list (@DL_Node A))),
  ((store_dll storeA_getfirstSpec node_pre l_getfirstSpec ))
|--
EX (A_2: Type) ,
EX (storeA_highSpec: (Z -> (A_2 -> Assertion)))(l_highSpec: (@list (@DL_Node A_2))),
  ((store_dll storeA_highSpec node_pre l_highSpec ))
  **
  (ALL (retval: Z),
(orp
  (“ (l_highSpec <> nil) ”
  &&  “ (retval = 0) ”
  &&  (store_dll storeA_highSpec node_pre l_highSpec ))
  (“ (l_highSpec = nil) ”
  &&  “ (retval = 1) ”
  &&  (store_dll storeA_highSpec node_pre l_highSpec )))
  -*
(orp
  (“ (l_getfirstSpec = nil) ”
  &&  “ (retval = 1) ”
  &&  (store_dll storeA_getfirstSpec node_pre l_getfirstSpec ))
  (EX (a: (@DL_Node A)) (l1: (@list (@DL_Node A))),
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
Axiom proof_of_OsSortLinkGetTargetExpireTime_highSpec_entail_lSpec : OsSortLinkGetTargetExpireTime_highSpec_entail_lSpec.
Axiom proof_of_LOS_ListEmpty_highSpec_entail_getfirstSpec : LOS_ListEmpty_highSpec_entail_getfirstSpec.

End VC_Correct.
