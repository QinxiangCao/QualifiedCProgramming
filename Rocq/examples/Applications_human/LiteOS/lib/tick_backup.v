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
Import naive_C_Rules.
Local Open Scope sac.
Local Open Scope string.
Local Open Scope list.

Definition TicksPerSec : Z := 100. (* 根据 LOSCFG_BASE_CORE_TICK_PER_SECOND 的值 *)
Definition Sys_Clock: Z := 1000000. (* 根据 OS_SYS_CLOCK 设定时钟频率*)
Definition Tick_Wtimer : Z := 0.   (*根据 LOSCFG_BASE_CORE_TICK_WTIMER 定义是否为高精度计时器*)
Definition MsPerSec : Z := 1000.
Definition UsPerSec : Z := 1000000.
Definition NsPerSec : Z := 1000000000.
Definition NsPerUs : Z := 1000.
Definition NsPerMs : Z := 1000000.
Definition irqMaxNum : Z := 32.


  (* 定义64位时钟的抽象状态 硬件架构设定为 arm-cortex-m4 *)
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
Definition arch_init_timer : archTickTimer :={|
  freqNum := 1000000;
  irqNum := 8;  
  periodMax := 0;
|}.

(* 定义一些时钟通常不变的全局变量 *)
Record tickSetting := mkTickSetting {
  tickClock : Z;
  cyclePTick : Z;
  tickInit : Z;
  tickTimer : addr;
}.

Notation "x '.(ts_period)'" := (ts_period x) (at level 1).
Notation "x '.(ts_val)'" := (ts_val x) (at level 1).
Notation "x '.(ts_ctrl)'" := (ts_ctrl x) (at level 1).
Notation "x '.(ts_startTime)'" := (ts_startTime x) (at level 1).
Notation "x '.(ts_timeBase)'" := (ts_timeBase x) (at level 1).
Notation "x '.(ts_oldTimeBase)'" := (ts_oldTimeBase x) (at level 1).
Notation "x '.(ts_timeBaseUpdate)'" := (ts_timeBaseUpdate x) (at level 1).
Notation "x '.(freqNum)'" := (freqNum x) (at level 1).
Notation "x '.(irqNum)'" := (irqNum x) (at level 1).
Notation "x '.(periodMax)'" := (periodMax x) (at level 1).


  (* 定义系统时钟的可能错误码 *)
Inductive tick_ret : Set :=
  | ErrTickPerSecTooSmall : tick_ret
  | ErrClockInvalid : tick_ret
  | ErrCfgInvalid : tick_ret
  | ErrPtrNone : tick_ret
  | ErrTimerAddrFault : tick_ret
  | TickRunning : tick_ret
  | TickOk : tick_ret.

(* arm-cortex-m4硬件：时钟初始化后，存到某个时钟结构体的地址 *)
Definition storeArchTick (gt: Z) (att : archTickTimer): Assertion :=
  &(gt # "ArchTickTimer" ->ₛ "freq") # UInt |-> att.(freqNum) **
  &(gt # "ArchTickTimer" ->ₛ "irqNum") # Int |-> att.(irqNum) **
  &(gt # "ArchTickTimer" ->ₛ "periodMax") # UInt64 |-> att.(periodMax).

(* arm-cortex-m4硬件：时钟初始化前存，某个时钟结构体的地址随机存内容 *)
Definition storeUndefArchTick (gt: Z): Assertion :=
  &(gt # "ArchTickTimer" ->ₛ "freq") # UInt |->_ **
  &(gt # "ArchTickTimer" ->ₛ "irqNum") # Int |->_ **
  &(gt # "ArchTickTimer" ->ₛ "periodMax") # UInt64 |->_.

(* arm-cortex-m4硬件：时钟周期数、控制位、计数值存到某个地址 *)
Definition storeCoreTimer (ct : Z) (ts : tickState) : Assertion :=
  &(ct # "CORE_TIM_TYPE" ->ₛ "ctrl") # UInt |-> ts.(ts_ctrl) **
  &(ct # "CORE_TIM_TYPE" ->ₛ "load") # UInt |-> ts.(ts_period) **
  &(ct # "CORE_TIM_TYPE" ->ₛ "val") # UInt |-> ts.(ts_val).

(* arm-cortex-m4硬件：时钟周期数、控制位、计数值的存储地址随机存内容 *)
Definition storeUndefCoreTimer (ct : Z) : Assertion :=
  &(ct # "CORE_TIM_TYPE" ->ₛ "ctrl") # UInt |->_ **
  &(ct # "CORE_TIM_TYPE" ->ₛ "load") # UInt |->_ **
  &(ct # "CORE_TIM_TYPE" ->ₛ "val") # UInt |->_.

(* 全局变量，系统基准时间表示谓词 *)
Definition storeTimerBase (ts : tickState) : Assertion :=
  &("g_tickTimerBase") # UInt64 |-> ts.(ts_timeBase) **
  &("g_oldTickTimerBase") # UInt64 |-> ts.(ts_oldTimeBase) **
  &("g_tickTimerBaseUpdate") # UInt |-> ts.(ts_timeBaseUpdate).

(* 全局变量，系统基准时间表示谓词 *)
Definition storeUndefTimerBase : Assertion :=
  &("g_tickTimerBase") # UInt64 |->_ **
  &("g_oldTickTimerBase") # UInt64 |->_ **
  &("g_tickTimerBaseUpdate") # UInt |->_.

(* 全局变量，通常不变的时钟设定 *)
Definition storeTickSetting (tset : tickSetting) : Assertion :=
  &("g_sysClock") # UInt |-> tset.(tickClock) **
  &("g_cyclesPerTick") # UInt |-> tset.(cyclePTick) **
  &("g_sysTimerIsInit") # UInt |-> tset.(tickInit) **
  &("g_sysTickTimer") # Ptr |-> tset.(tickTimer).

(* 全局变量，通常不变的时钟设定 *)
Definition storeUndefTickSetting : Assertion :=
  &("g_sysClock") # UInt |->_ **
  &("g_cyclesPerTick") # UInt |->_ **
  &("g_sysTimerIsInit") # UInt |-> 0 **
  &("g_sysTickTimer") # Ptr |->_.

(* 全局的变量，时钟开始时间表示谓词 *)
Definition storeStartTime (ts : tickState) : Assertion :=
  &("g_tickTimerStartTime") # UInt64 |-> ts.(ts_startTime).

(* 全局的变量，时钟开始时间表示谓词 *)
Definition storeUndefStartTime : Assertion :=
  &("g_tickTimerStartTime") # UInt64 |->_.

(* 时钟抽象状态存到某个地址 *)
Definition storeTick (gt ct : Z) (ts : tickState) (att : archTickTimer): Assertion :=
  storeArchTick gt att **
  storeCoreTimer ct ts **
  storeTimerBase ts **
  storeStartTime ts.

(* 时钟抽象状态随机存到某个地址 *)
Definition storeUndefTick (gt ct : Z): Assertion :=
  storeUndefArchTick gt **
  storeUndefCoreTimer ct **
  storeUndefTimerBase **
  storeUndefStartTime.

(* OSUpdateSysTimeBase函数的if条件判定函数 *)
Definition timebase_update (ts : tickState) : Z :=
  if Z.eq_dec ts.(ts_timeBaseUpdate) 0 then unsigned_last_nbits (ts.(ts_timeBase) + ts.(ts_period)) 64
  else ts.(ts_timeBase).

(* OsTickTimerInit函数的if条件判定函数-返回值 *)
Definition tick_init_ret (att : archTickTimer) : Z :=
  if Z_lt_dec att.(freqNum) 100 then 5
  else if Z_le_gt_dec att.(irqNum) 32 then 0
  else 1.

(* OsTickTimerInit函数的if条件判定函数-返回tickSetting *)
Definition tick_init_tset (att : archTickTimer) (archTickAddr : addr) : Assertion :=
  if Z_lt_dec att.(freqNum) 100 then 
    &("g_sysClock") # UInt |->_ **
    &("g_cyclesPerTick") # UInt |->_ **
    &("g_sysTimerIsInit") # UInt |-> 0 **
    &("g_sysTickTimer") # Ptr |-> archTickAddr
  else if Z_le_gt_dec att.(irqNum) 32 then storeTickSetting (mkTickSetting att.(freqNum) (att.(freqNum)/100) 1 archTickAddr)
  else &("g_sysClock") # UInt |->_ **
       &("g_cyclesPerTick") # UInt |->_ **
       &("g_sysTimerIsInit") # UInt |-> 0 **
       &("g_sysTickTimer") # Ptr |-> archTickAddr.

(* los_tick_LOS_SysCycleGet函数的if条件判定函数-返回tickState *)

Definition timebase_turnover (ts : tickState) : tickState :=
  if Z_lt_dec (unsigned_last_nbits (ts.(ts_timeBase)+(ts.(ts_period)-ts.(ts_val))) 64) ts.(ts_oldTimeBase) 
  then mkTickState (ts.(ts_period))
                   (ts.(ts_val)) 
                   (ts.(ts_ctrl)) 
                   (ts.(ts_startTime)) 
                   (unsigned_last_nbits (ts.(ts_timeBase)+ts.(ts_period)) 64) 
                   (unsigned_last_nbits ((unsigned_last_nbits (ts.(ts_timeBase)+ts.(ts_period)) 64)+(ts.(ts_period)-ts.(ts_val))) 64) 
                   1
  else  mkTickState (ts.(ts_period)) 
                    (ts.(ts_val)) 
                    (ts.(ts_ctrl)) 
                    (ts.(ts_startTime)) 
                    (ts.(ts_timeBase)) 
                    (unsigned_last_nbits (ts.(ts_timeBase)+(ts.(ts_period)-ts.(ts_val))) 64) 
                    (ts.(ts_timeBaseUpdate)).

Definition tick_getcycle_ret (ts : tickState) : Z :=
  if Z_lt_dec (unsigned_last_nbits (ts.(ts_timeBase)+(ts.(ts_period)-ts.(ts_val))) 64) ts.(ts_oldTimeBase) 
  then (unsigned_last_nbits ((unsigned_last_nbits (ts.(ts_timeBase)+ts.(ts_period)) 64)+(ts.(ts_period)-ts.(ts_val))) 64)
  else (unsigned_last_nbits (ts.(ts_timeBase)+(ts.(ts_period)-ts.(ts_val))) 64).

Definition timercheck_ret(att: archTickTimer) (tset: tickSetting) : Z :=
  if Z_lt_dec att.(freqNum) 100 then 5
  else if Z_le_gt_dec att.(irqNum) 32 
       then if Z.eq_dec att.(periodMax) 0 then 1
            else if Z.eq_dec tset.(tickInit) 0 then 0
                 else 9
       else 1.

Definition ms2tick_ret(ms : Z) : Z :=
  if Z.eq_dec ms (0xFFFFFFFF) then (0xFFFFFFFF)
  else (unsigned_last_nbits ((unsigned_last_nbits (ms*100) 64) / 1000) 32).
(* Search Z.eq sumbool. *)

Definition systickreload_ret(nextres: Z) (att: archTickTimer) : Z :=
  if Z_lt_dec att.(periodMax) nextres then att.(periodMax)
  else nextres.

Definition systickreload_ts(nextres: Z) (att: archTickTimer) (ts: tickState) : tickState :=
  mkTickState ((systickreload_ret nextres att)-1)
              0
              (ts.(ts_ctrl)) 
              (ts.(ts_startTime))
              (ts.(ts_timeBase))
              (ts.(ts_oldTimeBase))
              (ts.(ts_timeBaseUpdate)).

Definition update_ts_timebase(ts: tickState) (tb: Z) : tickState :=
  mkTickState (ts.(ts_period))
              (ts.(ts_val)) 
              (ts.(ts_ctrl)) 
              (ts.(ts_startTime))
              tb
              (ts.(ts_oldTimeBase))
              (ts.(ts_timeBaseUpdate)).
            
Definition tickreload_ts(nextres: Z) (att: archTickTimer) (ts: tickState): tickState :=
  mkTickState ((systickreload_ret nextres att)-1)
              0 
              ((timebase_turnover ts).(ts_ctrl)) 
              ((timebase_turnover ts).(ts_startTime))
              (tick_getcycle_ret ts)
              ((timebase_turnover ts).(ts_oldTimeBase))
              ((timebase_turnover ts).(ts_timeBaseUpdate)).