Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
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
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.Los_Verify_State_def.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.

Local Open Scope Z_scope.
Inductive link_type : Set :=
|  TASKLink : link_type
|  SWTMRLink : link_type
|  Other: link_type
.


Definition InvalidTime : Z := 2^64 - 1.
Definition MaxTime : Z := 2^64 - 1.
Definition LOSCFG_BASE_CORE_SWTMR : Z := 0.

Definition g_sysClock: Z := 1.
Definition g_schedResponseTime: Z := 1.


Definition set_sortlist_value {A: Type} (sln : sortedLinkNode A) (value : ResponseTime) : sortedLinkNode A :=
  mksortedLinkNode sln.(sl_data) value.


Definition get_sortlist_value {A: Type} (sln : sortedLinkNode A): ResponseTime :=
    sln.(responseTime).


Definition TimeConvert(time oldFreq newFreq : Z) : Z :=
    if Z.geb oldFreq newFreq then time / (oldFreq / newFreq)
    else time * (newFreq / oldFreq).

Fixpoint increasing_aux {A: Type} (a: DL_Node(sortedLinkNode A)) (l: list (DL_Node(sortedLinkNode A))): Prop :=
    match l with
        | nil => True
        | cons b l0 => (a.(dll_data).(responseTime) <= b.(dll_data).(responseTime)) /\ increasing_aux b l0
    end.


Definition increasing {A: Type} (l: list (DL_Node(sortedLinkNode A))): Prop :=
    match l with
        | nil => True
        | cons a l0 => increasing_aux a l0
    end.

Definition increasingSortedNode {A: Type} (l: list (DL_Node(sortedLinkNode A))): Prop :=
    match l with
        | nil => True
        | cons a l0 => increasing_aux a l0
    end.

Definition updateNodeTime {A: Type} (l: list (DL_Node(sortedLinkNode A)))(oldFreq newFreq: Z): list (DL_Node(sortedLinkNode A)) :=
    map (fun h => 
        let updatedTime := TimeConvert h.(dll_data).(responseTime) oldFreq newFreq in
        {| DLL.data := {| responseTime := updatedTime; sl_data := h.(dll_data).(sl_data) |};
           ptr := h.(ptr) |}
    ) l.


Definition getFirstNodeResponseTime {A: Type} (l : list (DL_Node(sortedLinkNode A))) : Z :=
    match l with
        | nil => 0              
        | h :: _ => (h.(dll_data).(responseTime)) 
    end.

Definition getNodeExpireTime {A: Type} (a: DL_Node(sortedLinkNode A))(startTime tickPrecision: Z) : Z := 
    if Z.leb a.(dll_data).(responseTime) (startTime+tickPrecision) then
        (startTime+tickPrecision)
    else
        a.(dll_data).(responseTime).
    
Definition getFirstNodeExpireTime {A: Type}  (l : list  (DL_Node(sortedLinkNode A)))(startTime tickPrecision: Z) :  Z :=
    match l with
        | nil => MaxTime - tickPrecision              
        | h :: _ => getNodeExpireTime h startTime tickPrecision
    end.
  
Definition getminExpireTime {A: Type}  (l1 : list  (DL_Node(sortedLinkNode A)))(l2 : list  (DL_Node(sortedLinkNode A)))(startTime tickPrecision: Z) :  Z :=
    if Z.ltb (getFirstNodeExpireTime l1 startTime tickPrecision) (getFirstNodeExpireTime l2 startTime tickPrecision) then
    (getFirstNodeExpireTime l1 startTime tickPrecision) 
    else
    (getFirstNodeExpireTime l2 startTime tickPrecision).

Definition task_store (sg: StableGlobVars)(x: addr)(a: TaskID): Assertion :=
    “ x = &((sg.(g_taskCBArray) # "LosTaskCB" + a) ->ₛ "sortList") ” 
    && emp.
    
Definition storesortedLinkTaskNode (task_storeA: StableGlobVars -> addr -> TaskID -> Assertion) (sg: StableGlobVars) (x: addr) (a: sortedLinkNode TaskID): Assertion :=
    EX y, “ x = &(y # "SortLinkList" ->ₛ "sortLinkNode") ” && task_storeA sg x a.(sl_data) ** 
    &(y # "SortLinkList" ->ₛ "responseTime") # UInt64 |-> a.(responseTime).
    
Definition storesortedLinkNode {A: Type} (storeA: addr -> A -> Assertion) (x: addr) (a: sortedLinkNode A): Assertion :=
    EX y, “ x = &(y # "SortLinkList" ->ₛ "sortLinkNode") ” && storeA x a.(sl_data) ** 
    &(y # "SortLinkList" ->ₛ "responseTime") # UInt64 |-> a.(responseTime).

Definition sortedLinkNodeMapping{A: Type} (x : DL_Node(sortedLinkNode A)) : DL_Node(sortedLinkNode A) :=
    Build_DL_Node x.(dll_data) (&(((x.(ptr))) # "SortLinkList" ->ₛ "sortLinkNode")).

Definition store_sorted_dll {A: Type} (storeA: addr -> A -> Assertion) (x: addr) (l: list (DL_Node(sortedLinkNode A))): Assertion :=
    “ increasing l ” &&
    store_dll (storesortedLinkNode storeA) x (map sortedLinkNodeMapping l).

Definition store_task_sorted_dll (sg: StableGlobVars)(l: list (DL_Node(sortedLinkNode TaskID))): Assertion :=
    EX y, “ y = (&("g_taskSortLink")) ” &&
    store_sorted_dll 
      (fun p (taskID: TaskID) =>
         “ p = &((sg.(g_taskCBArray) # "LosTaskCB" + taskID) ->ₛ "sortList") ” 
         && emp)
    (&(y # "SortLinkAttribute" ->ₛ "sortLink")) l. 
  
Definition store_swtmr_sorted_dll (sg: StableGlobVars)(l: list (DL_Node(sortedLinkNode SwtmrID))): Assertion :=
    EX y, “ y = (&("g_swtmrSortLink")) ” &&
    store_sorted_dll 
     (fun p (swmtrID: SwtmrID) =>
        “ p = &((sg.(g_swtmrCBArray) # "SWTMR_CTRL_S" + swmtrID % 5) ->ₛ "stSortList") ” 
        && emp)
     (&(y # "SortLinkAttribute" ->ₛ "sortLink")) l. 

Definition obtian_first_pointer {A: Type} (x: addr)(l: list (DL_Node(sortedLinkNode A))): addr :=
    match l with
        | nil => x            
        | a :: l0 => a.(ptr)
    end.

Module ListSortDelSpec_ForStoreDLL.
Definition Pre 
			{A: Type} (storeA: addr -> A -> Assertion)
             (x u: addr)
             (l1: list (DL_Node(sortedLinkNode A))) (a: DL_Node(sortedLinkNode A))(l2: list (DL_Node(sortedLinkNode A))): Assertion :=
    store_sorted_dll storeA x (l1++a :: l2).

Definition Post
             {A: Type} (storeA: addr -> A -> Assertion)
             (x u: addr) 
             (l1: list (DL_Node(sortedLinkNode A))) (a: DL_Node(sortedLinkNode A))(l2: list (DL_Node(sortedLinkNode A))): Assertion :=
  storeA u a.(dll_data).(sl_data) **
  &(u # "LOS_DL_LIST" ->ₛ  "pstPrev") # Ptr |-> 0 **
  &(u # "LOS_DL_LIST" ->ₛ  "pstNext") # Ptr |-> 0 **
  &(u # "SortLinkList" ->ₛ  "responseTime") # Int |-> InvalidTime **
  store_sorted_dll storeA x (l1++l2).
End ListSortDelSpec_ForStoreDLL.



Module ListSortAddSpec_ForStoreDLL.
Definition Pre
             {A: Type} (storeA: addr -> A -> Assertion)
             (x u: addr) (l: list (DL_Node(sortedLinkNode A))) (a: DL_Node(sortedLinkNode A)) : Assertion :=
  (EX __, &(u # "LOS_DL_LIST" ->ₛ  "pstPrev") # Ptr |-> __) ** 
  (EX __, &(u # "LOS_DL_LIST" ->ₛ  "pstNext") # Ptr |-> __) **
  storesortedLinkNode storeA u a.(dll_data) **
  store_sorted_dll storeA x l.

Definition Post
             {A: Type}  (storeA: addr -> A -> Assertion)
             (x u: addr) (l: list (DL_Node(sortedLinkNode A))) (a: DL_Node(sortedLinkNode A)): Assertion :=
    EX l1 : list (DL_Node(sortedLinkNode A)),
    EX l2 : list (DL_Node(sortedLinkNode A)),
    “ l=l1++l2 ” **
    store_sorted_dll storeA x (l1++a::l2).

End ListSortAddSpec_ForStoreDLL.


Module GetNodeRemainTimeSpec.
Definition Pre 
			{A: Type} (storeA: addr -> A -> Assertion)
            (x: addr)(currTime: Z)(__return: Z): Assertion :=
    EX a: DL_Node((sortedLinkNode A)),
    storesortedLinkNode storeA x a.(dll_data).

Definition Post
             {A: Type} (storeA: addr -> A -> Assertion)
             (x: addr)(currTime: Z)(__return: Z): Assertion :=
    EX a: DL_Node((sortedLinkNode A)),
    “ (currTime >= a.(dll_data).(responseTime) /\ __return = 0) \/ (currTime < a.(dll_data).(responseTime) /\ __return = a.(dll_data).(responseTime) - currTime) ” **
    storesortedLinkNode storeA x a.(dll_data).

End GetNodeRemainTimeSpec.

        
Module GetLinkExpireTimeSpec.
Definition Pre 
			{A: Type} (storeA: addr -> A -> Assertion)
            (head: addr)(startTime tickPrecision: Z)(l: list (DL_Node(sortedLinkNode A)))(__return: Z): Assertion :=
        store_sorted_dll storeA head l.

Definition Post
           {A: Type} (storeA: addr -> A -> Assertion)
            (head: addr)(startTime tickPrecision: Z)(l: list (DL_Node(sortedLinkNode A)))(__return: Z): Assertion :=
        “ __return = getFirstNodeExpireTime l startTime tickPrecision ” **
        store_sorted_dll storeA head l.

End GetLinkExpireTimeSpec.


Module OsGetNextExpireTimeSpec.
Definition Pre 
            (sg: StableGlobVars)(startTime tickPrecision: Z)(l1: list (DL_Node(sortedLinkNode TaskID)))(l2: list (DL_Node(sortedLinkNode SwtmrID)))(__return: Z): Assertion :=
        store_task_sorted_dll sg l1 **
        store_swtmr_sorted_dll sg l2.


Definition Post
            (sg: StableGlobVars)(startTime tickPrecision: Z)(l1: list (DL_Node(sortedLinkNode TaskID)))(l2: list (DL_Node(sortedLinkNode SwtmrID)))(__return: Z): Assertion :=
        “ (LOSCFG_BASE_CORE_SWTMR = 0 /\ __return = getFirstNodeExpireTime l1 startTime tickPrecision) \/ (LOSCFG_BASE_CORE_SWTMR = 1 /\ __return = getminExpireTime l1 l2 startTime tickPrecision) ” **
        store_task_sorted_dll sg l1 **
        store_swtmr_sorted_dll sg l2.

End OsGetNextExpireTimeSpec.


Module UpdateTimeSpec.
Definition Pre 
			{A: Type} (storeA: addr -> A -> Assertion)
            (head: addr)(oldFreq: Z)(l: list (DL_Node(sortedLinkNode A)))(__return: Z): Assertion :=
        “ oldFreq <> 0 ” **
        store_sorted_dll storeA head l.

Definition Post
          {A: Type} (storeA: addr -> A -> Assertion)
            (head: addr)(oldFreq: Z)(l: list (DL_Node(sortedLinkNode A)))(__return: Z): Assertion :=
        store_sorted_dll storeA head (updateNodeTime l oldFreq g_sysClock).

End UpdateTimeSpec.


Module OsTimeConvertSpec.
Definition Pre 
            (sg: StableGlobVars)(oldFreq: Z)(l1: list (DL_Node(sortedLinkNode TaskID)))(l2: list (DL_Node(sortedLinkNode SwtmrID))): Assertion :=
        store_task_sorted_dll sg l1 **
        store_swtmr_sorted_dll sg l2.

Definition Post
            (sg: StableGlobVars)(oldFreq: Z)(l1: list (DL_Node(sortedLinkNode TaskID)))(l2: list (DL_Node(sortedLinkNode SwtmrID))): Assertion :=
        store_task_sorted_dll sg (updateNodeTime l1 oldFreq g_sysClock) **
        (if Z.eq_dec LOSCFG_BASE_CORE_SWTMR 1
         then store_task_sorted_dll sg (updateNodeTime l2 oldFreq g_sysClock)
         else store_swtmr_sorted_dll sg l2). 

End OsTimeConvertSpec. 


Module GetAttributeSpec.
Definition Pre 
        (sg: StableGlobVars)(type: link_type)(l1: list (DL_Node(sortedLinkNode TaskID)))(l2: list (DL_Node(sortedLinkNode SwtmrID)))(__return: addr): Assertion :=
        store_task_sorted_dll sg l1 **
        store_swtmr_sorted_dll sg l2.

Definition Post
        (sg: StableGlobVars)(type: link_type)(l1: list (DL_Node(sortedLinkNode TaskID)))(l2: list (DL_Node(sortedLinkNode SwtmrID)))(__return: addr): Assertion :=
    “ (type = TASKLink /\ __return = &("g_taskSortLink")) \/ (type = SWTMRLink /\ LOSCFG_BASE_CORE_SWTMR = 1 /\ __return = &("g_swtmrSortLink")) \/ 
       (type = SWTMRLink /\ LOSCFG_BASE_CORE_SWTMR = 0 /\ __return = &("null")) \/ (type = Other  /\ __return = &("null")) ” **
    store_task_sorted_dll sg l1 **
    store_swtmr_sorted_dll sg l2.

End GetAttributeSpec.


Module GetNodeExpireTimeSpec.
Definition Pre 
			{A: Type} (storeA: addr -> A -> Assertion)
            (x: addr)(currTime: Z): Assertion :=
    EX a: DL_Node(sortedLinkNode A),
    storeA x a.(dll_data).(sl_data).

Definition Post
             {A: Type} (storeA: addr -> A -> Assertion)
             (x: addr)(currTime: Z)(__return: Z): Assertion :=
    EX a: DL_Node(sortedLinkNode A),
    “ (currTime >= a.(dll_data).(responseTime) /\ __return = 0) \/ (currTime < a.(dll_data).(responseTime) /\ __return = a.(dll_data).(responseTime) - currTime) ” **
    storesortedLinkNode storeA x a.(dll_data).

End GetNodeExpireTimeSpec.


Module GetNextExpireTimeSpec.
Definition Pre 
			{A: Type} (storeA: addr -> A -> Assertion)
            (head: addr)(l: list (DL_Node(sortedLinkNode A))): Assertion :=
    store_sorted_dll storeA head l.

Definition Post
             {A: Type} (storeA: addr -> A -> Assertion)
            (head: addr)(l: list (DL_Node(sortedLinkNode A)))(__return: Z): Assertion :=
    EX OsCurrSchedTimeCycle: Z ,
    match l with
    | nil => “ __return = 0 ”
    | h :: _ => 
        match Z.leb h.(dll_data).(responseTime) OsCurrSchedTimeCycle with
        | true => “ __return = 0 ”
        | false => “ __return = h.(dll_data).(responseTime) - OsCurrSchedTimeCycle ” **
        store_sorted_dll storeA head l 
        end
    end.
End GetNextExpireTimeSpec.


Lemma dllseg_sortedLinkNode_head_insert:
  forall (A: Type) (storeA: Z -> A -> Assertion) 
         (py y z x pt sortList: Z) (a: A) (t: Z) (l: list (DL_Node(sortedLinkNode A))),
    y = &( sortList # "SortLinkList" ->ₛ "sortLinkNode") ->
    dllseg (storesortedLinkNode storeA) z y x pt (map sortedLinkNodeMapping l) **
    storesortedLinkNode storeA y ({| sl_data := a; responseTime := t |}) **
    &(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py **
     &(y # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z |--
    dllseg (storesortedLinkNode storeA) y py x pt 
           (map sortedLinkNodeMapping ((Build_DL_Node (mksortedLinkNode a t) sortList) :: l)).
Proof.
    intros.
    simpl.
    Exists z.
    entailer!.
Qed.


Lemma storesortedLinkNode_split : 
    forall (A : Type) (storeA : Z -> A -> Assertion) (y y0 : Z) (a : A) (t : Z),
    y = &( y0 # "SortLinkList" ->ₛ "sortLinkNode") ->
    storeA y (sl_data {| sl_data := a; responseTime := t |}) **
    &( y0 # "SortLinkList" ->ₛ "responseTime") # UInt64 |-> responseTime {| sl_data := a; responseTime := t |}|--
    storesortedLinkNode storeA y {| sl_data := a; responseTime := t |}.
Proof.
    intros.
    simpl.
    unfold storesortedLinkNode.
    Exists y0.
    entailer!.
Qed.


Lemma store_sorted_dll_split:
    forall(A: Type) (x: Z)(t: Z) (storeA: Z -> A -> Assertion) (a: A) (l1 l2: list (DL_Node(sortedLinkNode A))) (sortList: Z),
    store_sorted_dll storeA x (l1 ++ (Build_DL_Node (mksortedLinkNode a t) sortList) :: l2) |-- 
    EX h pt y y0 py z,
    “ increasing (l1 ++ {| data := {| sl_data := a; responseTime := t |}; ptr := sortList |} :: l2) ” &&
    storeA y (sl_data {| sl_data := a; responseTime := t |}) **
    (&( y0 # "SortLinkList" ->ₛ "responseTime") # UInt64 |-> responseTime {| sl_data := a; responseTime := t |} **
    (&( y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py **
    (&( y # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z **
    (dllseg (storesortedLinkNode storeA) z y x pt (map sortedLinkNodeMapping l2) **
        (&( x # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> pt **
        (&( x # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> h **
        dllseg (storesortedLinkNode storeA) h x y py (map sortedLinkNodeMapping l1))))))).
Proof.
    unfold store_sorted_dll.
    intros.
    Intros.
    unfold store_dll.
    Intros h0 pt0.
    rewrite map_app.
    rewrite map_cons.
    sep_apply(dllseg_split (storesortedLinkNode(storeA))).
    Intros y1 py0.
    simpl dllseg.
    Intros z0.
    unfold storesortedLinkNode at 1.
    Intros y.
    Exists h0 pt0 y1 y py0.
    Exists z0.
    entailer!.
Qed.


Lemma store_sorted_dll_concat:
forall(A: Type) (x : Z) (h pt y py z: Z)(t: Z) (storeA: Z -> A -> Assertion) (a: A) 
      (l1 l2: list (DL_Node(sortedLinkNode A))) (sortList: Z),
    y = &( sortList # "SortLinkList" ->ₛ "sortLinkNode") ->
    increasing(l1 ++ {| data := {| sl_data := a; responseTime := t |}; ptr := sortList |} :: l2) ->
    storeA y (sl_data {| sl_data := a; responseTime := t |}) **
    (&( sortList # "SortLinkList" ->ₛ "responseTime") # UInt64 |-> responseTime {| sl_data := a; responseTime := t |} **
    (&( y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py **
    (&( y # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z **
    (dllseg (storesortedLinkNode storeA) z y x pt (map sortedLinkNodeMapping l2) **
        (&( x # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> pt **
        (&( x # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> h **
        dllseg (storesortedLinkNode storeA) h x y py (map sortedLinkNodeMapping l1))))))) |-- 
    store_sorted_dll storeA x (l1 ++ (Build_DL_Node (mksortedLinkNode a t) sortList) :: l2).
Proof.
    pre_process.
    unfold store_sorted_dll.
    unfold store_dll.
    rewrite map_app.
    rewrite map_cons.
    pose proof storesortedLinkNode_split _ (storeA) y sortList a t.
    pose proof dllseg_head_insert _ (storesortedLinkNode storeA) py y z x pt (mksortedLinkNode a t) (map sortedLinkNodeMapping l2). (* sortList a t l2 H.*)
    sep_apply(H1).
    sep_apply(H2).
    pose proof dllseg_concat (storesortedLinkNode(storeA)) h x y py x pt.
    sep_apply(H4).
    - 
    Exists h pt.
    unfold sortedLinkNodeMapping at 4.
    simpl.
    rewrite H.
    entailer!.
    -
    apply(H).
Qed.