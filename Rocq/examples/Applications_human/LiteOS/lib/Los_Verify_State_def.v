Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.
From SimpleC.SL Require Import ConAssertion CriticalSTS NestedCriticalSTS.


Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs.

Module EventStateDef.
  Definition maxEventNum : Z := 32. 
  Definition EventID := Z.

  Definition EventIDList := list EventID.
  Definition EventMask := list EventID.

  Inductive EventMode : Type :=
  | LOS_WAITMODE_AND
  | LOS_WAITMODE_OR.

  Definition ClearMode := bool.

  Record EventReadAbstractState := mkEventReadAbstractState {
    eventMask : EventMask;
    eventMode : EventMode;
    clearMode : ClearMode;
  }.

  Record EventWriteAbstractState := mkEventWriteAbstractState {
    eventIDList : EventIDList;
    eventTaskList : list TaskID;
  }.

  Record EventAbstractState := mkEventAbstractState {
    eventReadState : EventReadAbstractState;
    eventWriteState : EventWriteAbstractState;
  }.
  
End EventStateDef.

Export EventStateDef.

Module MuxStateDef.
  Definition MuxID: Type := Z.

  Record MuxAbstractState :=  {
    muxCount: Z;  (* 锁被持有的次数 *)
    muxList: list TaskID;  (* 等待写入的任务列表 *)
    owner: addr; (* 执行任务控制块的指针 *)
    priority: Z; (* 优先级 *)
  }.

  Record Glob_MuxAbstractState: Type := {
    inUsedMuxStates: MuxID -> option MuxAbstractState;
    (* 所有互斥锁的高层状态表示为从muxID到互斥锁抽象状态的映射 *)
    (* Option表示可选的互斥锁状态，创建时被设置为Some，删除时被设置为none *)
    unUsedMuxStates: list MuxID
  }.

  Inductive mux_ret: Type :=
    | LOS_ERRNO_MUX_NO_MEMORY
    | LOS_ERRNO_MUX_INVALID
    | LOS_ERRNO_MUX_PTR_NULL
    | LOS_ERRNO_MUX_ALL_BUSY
    | LOS_ERRNO_MUX_UNAVAILABLE
    | LOS_ERRNO_MUX_PEND_INTERR
    | LOS_ERRNO_MUX_PEND_IN_LOCK
    | LOS_ERRNO_MUX_TIMEOUT
    | LOS_ERRNO_MUX_PENDED
    | LOS_OK.

End MuxStateDef.

Export MuxStateDef.

Module MemboxStateDef.
	Definition startAddr := addr. (* 内存池块起始地址 *)
  Definition uwBlkSize := Z.  (* 内存池块大小 *)
  Definition magicNum := Z. (* 内存块存储魔法字 *)

  Record FreeMemBoxNode : Type := mkFreeMemBoxNode{
        fnstartAddr : startAddr; (* 内存池块起始地址 *)
        fnuwBlkSize : uwBlkSize; (* 内存池块大小 *)
  }.

	Definition FreeList := list FreeMemBoxNode.  (* 未分配内存池块列表 *)

  Record AllocMemBoxNode : Type := mkAllocMemBoxNode{
        anstartAddr : startAddr; (* 内存池块起始地址 *)
        anuwBlkSize : uwBlkSize; (* 内存池块大小 *)
        anmagicNum : magicNum; (* 内存块存储魔法字 *)
  }.
  
  Definition AllocList := list AllocMemBoxNode. (* 已分配内存池块列表 *)


  Record MemBox : Type := mkMemBox{
        mstartAddr: startAddr; (* 内存池起始地址 *)
        muwBlkSize : uwBlkSize; (* 内存池块大小 *)
        mFreeList : FreeList; (* 未分配内存池块列表 *)
        mAllocList: AllocList; (* 已分配内存池块列表 *)
  }.

  Definition MemBoxList := list MemBox.

  Record MemboxAbstractState := mkMemboxAbstractState {
        mboxList : MemBoxList;  (* 内存池列表 *)
  }.

	Definition sizeof_Z := 4. 

End MemboxStateDef.

Export MemboxStateDef.

Module QueueStateDef.
  Definition QID := Z.  (* 队列ID *)
  Definition QSize := Z.  (* 节点大小 *)
  Definition MsgContent := list Z.
  Definition QueueContent := list MsgContent.  (* 队列内容，假设为值的列表 *)

  Record QueueAbstractState := mkQueueAbstractState {
    qSize : QSize;  (* 节点大小 *)
    qContent : QueueContent;  (* 队列内容 *)
    qReadList : list TaskID;  (* 等待读取的任务列表 *)
    qWriteList : list TaskID;  (* 等待写入的任务列表 *)
  }.

  Definition QueueMap := QID -> option QueueAbstractState. 
  (*Module Import M := FMapAVL.Make(Z_as_OT).
  Definition QueueMap := M.t (option QueueAbstractState).*)
  (*QueueID -> option QueueAbstractState*)
  (* option表示可选的队列状态，创建时被设置为Some，删除时被设置为none *)


  Record Glob_QueueAbstractState := {
      gfreeList :  list QID; (* 空闲消息节点 list of QueueID*)
      qMap : QueueMap;
  }.

End QueueStateDef.

Export QueueStateDef.

Module SchedStateDef.

  Parameter SchedAbstractState: Type.

End SchedStateDef.

Export SchedStateDef.

Module SemStateDef.

  Definition SemID: Type := Z.

  Definition semMaxNum:=6.

  Record SemAbstractState :=  {
    semCount: Z;  (* 表示可用信号量的个数 *)
    maxSemCount: Z;  (* 表示可用信号量的最大容量 *)
    semList: list TaskID;  (* 等待写入的任务列表 *)
  }.

  Inductive sem_addr_ret: Type :=
    | LOS_ERRNO_SEM_NO_MEMORY
    | LOS_ERRNO_SEM_INVALID
    | LOS_ERRNO_SEM_PTR_NULL
    | LOS_ERRNO_SEM_ALL_BUSY
    | LOS_ERRNO_SEM_UNAVAILABLE
    | LOS_ERRNO_SEM_PEND_INTERR
    | LOS_ERRNO_SEM_PEND_IN_LOCK
    | LOS_ERRNO_SEM_TIMEOUT
    | LOS_ERRNO_SEM_PENDED
    | LOS_OK.

  Record Glob_SemAbstractState: Type := {
    inUsedSemStates: SemID -> option SemAbstractState;
    (* 所有消息队列的高层状态表示为从队列ID到队列状态的映射 *)
    (* Option表示可选的信号量状态，创建时被设置为Some，删除时被设置为none *)
    unUsedSemStates: list SemID
  }.

End SemStateDef.

Export SemStateDef.

Module SwtmrStateDef.

  Definition SwtmrID: Type := Z.
  Definition SWTMRCbID: Type := Z.

  Inductive SWTMRStatus : Type :=
  | created
  | ticking.

  Record SWTMRAbstractState := mkSWTMR {
    ID : SwtmrID;
    interval : Z;  (* 间隔 *)
    startTime : Z;  (* 开始时间 *)
    mode : Z;  (* 定时器模式: ONCE, NO_SELFDELETE, PERIOD. (OPP not used..) *) 
    (* Overrun省略，不涉及对其进行判断的语句 *)
    status : Z;  (* 定时器状态 0: UNUSED; 1: CREATED; 2: TICKING *)
  }.
  Record Glob_SWTMRAbstractState: Type := mkSWTMRAbstractState {
    inUseStates: SWTMRCbID -> option SWTMRAbstractState;
    unUsedStates: list SwtmrID;
    sortlink: list (DL_Node (sortedLinkNode SwtmrID));
    queue: Glob_QueueAbstractState;
    SWTMRHandlerQID : Z;
  }.

End SwtmrStateDef.

Export SwtmrStateDef.

Module TaskStateDef.

Record TaskAbstractState := mkTaskAbstractState {
    status : Z;
    tPrio : Z;
    tStackPointer : addr;
    tTimeSlice : Z;
    tWaitTimes : Z;
    tStartTime : Z;
    tStackSize : Z;
    tTopOfStack : Z;
    tTaskEntry : addr;   (* it is in fact a function pointer, how to model it? *)
    tTaskSem : addr;
    tTaskMux : addr;
    tArg : Z;
    tTaskName : addr;
    tJoinList : list TaskID;  (* task 模块中任务的 join 机制存在 bug, 深开鸿已确认，验证暂时忽略 join 机制相关代码 *)
    tJoinRetval : Z;
    tEvent : Z * list TaskID;
    tEventMask : Z;
    tEventMode : Z;
    tMsg : addr;
}.

(* low level abstract state of recycle task *)
Record RecycleTaskAbstractState := mkRecycleTaskAbstractState {
  recycle_tID : TaskID;
  recycle_status : Z;
  recycle_tStackPointer : addr;
  recycle_tTopOfStack : Z;
}.

(* 问题： 任务创建过程，没有完成初始化 *) 
Record TcbGlobalState := mkTcbGlobalState {
    usedTask : TaskID -> option TaskAbstractState;     (* map from taskid to low level abstract state， usedtask taskid == None means the taskid does finish its initialization. *)
    freeTask : list TaskID;        (* task status is exactly unused, pended in g_losFreeTask *)
    recycleList : list  RecycleTaskAbstractState ;     (* task status is exits, running, and unused status, waited for reclaiming resources, pended in g_taskRecycleList, store (taskid, status, stackPointer, topOfStack) *)
    runTask : TaskID;              (* g_losTask.runTask  *)
    newTask : TaskID;       (* g_losTask.newTask  *)
    losTaskLock : Z;               (* another lock that indicates whether sched is locked  *)
    ghostTaskInfo : TaskID * Z * Z * addr (* tcb ghostTaskId stores the previously deleted running task's taskid, taskStatus, topOfStack, and taskName *)
}.

End TaskStateDef.

Import TaskStateDef.

Module TickStateDef.

Record tickState := mkTickState {
  ts_period : Z;                  (* 此轮计时周期数，等于SysTick寄存器中的load *)
  ts_val : Z;                     (* 存储在硬件寄存器中，当前计数值 *)
  ts_ctrl : Z;                    (* 存储在硬件寄存器中，当前控制位 *)
  ts_startTime : Z;               (* 时钟启动时间 *)
  ts_timeBase : Z;                (* 系统基准时间 *)
  ts_oldTimeBase : Z;             (* 旧的系统基准时间 *)
  ts_timeBaseUpdate : Z;          (* 系统基准时间是否需要更新 *)
}.

(* 定义arm-cortex-m4时钟初始化后的赋值 *)
Record archTickTimer := mkArchTickTimer {
  freqNum : Z;
  irqNum : Z;  
  periodMax : Z;
}.

Record TickAbstractState := mkTickAbstractState {
  tgs_ts : tickState;
  tgs_att : archTickTimer;
}.

(* 定义CPUTick数值 *)
Record cpuTickvalue := mkCPUTick {
  loNum : Z;
  hiNum : Z; 
}.

End TickStateDef.

Export TickStateDef.


Record Los_Verify_State : Type := {
  TskState : TcbGlobalState;
  EvtState : EventAbstractState;
  MuxState : Glob_MuxAbstractState;
  SemState : Glob_SemAbstractState;
  SwtmrState : Glob_SWTMRAbstractState;
  QueueState : Glob_QueueAbstractState;
  TickState : TickAbstractState;
  MemboxState : MemboxAbstractState;
  SchedState : SchedAbstractState;
}.

Definition replace_tskS (ts : TcbGlobalState) (os : Los_Verify_State) : Los_Verify_State := {| 
  TskState := ts;
  EvtState := os.(EvtState);
  MuxState := os.(MuxState);
  SemState := os.(SemState);
  SwtmrState := os.(SwtmrState);
  QueueState := os.(QueueState);
  TickState := os.(TickState);
  MemboxState := os.(MemboxState);
  SchedState := os.(SchedState);
|}.

Definition replace_evtS (es : EventAbstractState) (os : Los_Verify_State) : Los_Verify_State := {| 
  TskState := os.(TskState);
  EvtState := es;
  MuxState := os.(MuxState);
  SemState := os.(SemState);
  SwtmrState := os.(SwtmrState);
  QueueState := os.(QueueState);
  TickState := os.(TickState);
  MemboxState := os.(MemboxState);
  SchedState := os.(SchedState);
|}.


Definition replace_muxS (ms : Glob_MuxAbstractState) (os : Los_Verify_State) : Los_Verify_State := {| 
  TskState := os.(TskState);
  EvtState := os.(EvtState);
  MuxState := ms;
  SemState := os.(SemState);
  SwtmrState := os.(SwtmrState);
  QueueState := os.(QueueState);
  TickState := os.(TickState);
  MemboxState := os.(MemboxState);
  SchedState := os.(SchedState);
|}.

Definition replace_semS (ss : Glob_SemAbstractState) (os : Los_Verify_State) : Los_Verify_State := {| 
  TskState := os.(TskState);
  EvtState := os.(EvtState);
  MuxState := os.(MuxState);
  SemState := ss;
  SwtmrState := os.(SwtmrState);
  QueueState := os.(QueueState);
  TickState := os.(TickState);
  MemboxState := os.(MemboxState);
  SchedState := os.(SchedState);
|}.

Definition replace_swtmrS (ss : Glob_SWTMRAbstractState) (os : Los_Verify_State) : Los_Verify_State := {| 
  TskState := os.(TskState);
  EvtState := os.(EvtState);
  MuxState := os.(MuxState);
  SemState := os.(SemState);
  SwtmrState := ss;
  QueueState := os.(QueueState);
  TickState := os.(TickState);
  MemboxState := os.(MemboxState);
  SchedState := os.(SchedState);
|}.

Definition replace_queueS (qs : Glob_QueueAbstractState) (os : Los_Verify_State) : Los_Verify_State := {| 
  TskState := os.(TskState);
  EvtState := os.(EvtState);
  MuxState := os.(MuxState);
  SemState := os.(SemState);
  SwtmrState := os.(SwtmrState);
  QueueState := qs;
  TickState := os.(TickState);
  MemboxState := os.(MemboxState);
  SchedState := os.(SchedState);
|}.

Definition replace_tickS (ts : TickAbstractState) (os : Los_Verify_State) : Los_Verify_State := {| 
  TskState := os.(TskState);
  EvtState := os.(EvtState);
  MuxState := os.(MuxState);
  SemState := os.(SemState);
  SwtmrState := os.(SwtmrState);
  QueueState := os.(QueueState);
  TickState := ts;
  MemboxState := os.(MemboxState);
  SchedState := os.(SchedState);
|}.

Definition replace_memboxS (ms : MemboxAbstractState) (os : Los_Verify_State) : Los_Verify_State := {| 
  TskState := os.(TskState);
  EvtState := os.(EvtState);
  MuxState := os.(MuxState);
  SemState := os.(SemState);
  SwtmrState := os.(SwtmrState);
  QueueState := os.(QueueState);
  TickState := os.(TickState);
  MemboxState := ms;
  SchedState := os.(SchedState);
|}.

Definition replace_schedS (ss : SchedAbstractState) (os : Los_Verify_State) : Los_Verify_State := {| 
  TskState := os.(TskState);
  EvtState := os.(EvtState);
  MuxState := os.(MuxState);
  SemState := os.(SemState);
  SwtmrState := os.(SwtmrState);
  QueueState := os.(QueueState);
  TickState := os.(TickState);
  MemboxState := os.(MemboxState);
  SchedState := ss;
|}.

Lemma replace_tskS_TskState: forall ts os, (replace_tskS ts os).(TskState) = ts.
Proof.
  intros. destruct os; auto.
Qed.

Lemma replace_evtS_evtState: forall es os, (replace_evtS es os).(EvtState) = es.
Proof.
  intros. destruct os; auto.
Qed.

Lemma replace_muxS_muxState: forall ms os, (replace_muxS ms os).(MuxState) = ms.
Proof.
  intros. destruct os; auto.
Qed.

Lemma replace_semS_semState: forall ss os, (replace_semS ss os).(SemState) = ss.
Proof.
  intros. destruct os; auto.
Qed.

Lemma replace_swtmrS_swtmrState: forall ss os, (replace_swtmrS ss os).(SwtmrState) = ss.
Proof.
  intros. destruct os; auto.
Qed.

Lemma replace_queueS_queueState: forall qs os, (replace_queueS qs os).(QueueState) = qs.
Proof.
  intros. destruct os; auto.
Qed.

Lemma replace_tickS_tickState: forall ts os, (replace_tickS ts os).(TickState) = ts.
Proof.
  intros. destruct os; auto.
Qed.

Lemma replace_memboxS_memboxState: forall ms os, (replace_memboxS ms os).(MemboxState) = ms.
Proof.
  intros. destruct os; auto.
Qed.

Lemma replace_schedS_schedState: forall ss os, (replace_schedS ss os).(SchedState) = ss.
Proof.
  intros. destruct os; auto.
Qed.

Lemma dup_replace_tskS: forall ts os, replace_tskS ts (replace_tskS ts os) = replace_tskS ts os.
Proof.
  intros. destruct os; auto.
Qed.

Lemma dup_replace_evtS: forall es os, replace_evtS es (replace_evtS es os) = replace_evtS es os.
Proof.
  intros. destruct os; auto.
Qed.

Lemma dup_replace_muxS: forall ms os, replace_muxS ms (replace_muxS ms os) = replace_muxS ms os.
Proof.
  intros. destruct os; auto.
Qed.

Lemma dup_replace_semS: forall ss os, replace_semS ss (replace_semS ss os) = replace_semS ss os.
Proof.
  intros. destruct os; auto.
Qed.

Lemma dup_replace_swtmrS: forall ss os, replace_swtmrS ss (replace_swtmrS ss os) = replace_swtmrS ss os.
Proof.
  intros. destruct os; auto.
Qed.

Lemma dup_replace_queueS: forall qs os, replace_queueS qs (replace_queueS qs os) = replace_queueS qs os.
Proof.
  intros. destruct os; auto.
Qed.

Lemma dup_replace_tickS: forall ts os, replace_tickS ts (replace_tickS ts os) = replace_tickS ts os.
Proof.
  intros. destruct os; auto.
Qed.

Lemma dup_replace_memboxS: forall ms os, replace_memboxS ms (replace_memboxS ms os) = replace_memboxS ms os.
Proof.
  intros. destruct os; auto.
Qed.

Lemma dup_replace_schedS: forall ss os, replace_schedS ss (replace_schedS ss os) = replace_schedS ss os.
Proof.
  intros. destruct os; auto.
Qed.
