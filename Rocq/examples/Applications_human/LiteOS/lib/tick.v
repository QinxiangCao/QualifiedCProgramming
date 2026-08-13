Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import ListNotations.
From SimpleC.SL Require Import ConAssertion CriticalSTS NestedCriticalSTS.

Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.Los_Verify_State_def.
Import TickStateDef.
Local Open Scope sac.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Import DLL.

(******************************** tick模块表示谓词 *******************************)

Definition storeUndefTickSetting: Assertion :=
  &("g_sysClock") # UInt |->_ **
  &("g_cyclesPerTick") # UInt |->_ **
  &("g_sysTimerIsInit") # UInt |-> 0 **
  &("g_sysTickTimer") # Ptr |->_ **
  &("SysTick") # Ptr |->_.

Definition storeUndefArchTick (gt: Z): Assertion :=
  &(gt # "ArchTickTimer" ->ₛ "freq") # UInt |->_ **
  &(gt # "ArchTickTimer" ->ₛ "irqNum") # Int |->_ **
  &(gt # "ArchTickTimer" ->ₛ "periodMax") # UInt64 |->_.

Definition storeUndefCoreTimer (ct : Z) : Assertion :=
  &(ct # "CORE_TIM_TYPE" ->ₛ "ctrl") # UInt |->_ **
  &(ct # "CORE_TIM_TYPE" ->ₛ "load") # UInt |->_ **
  &(ct # "CORE_TIM_TYPE" ->ₛ "val") # UInt |->_.

Definition storeUndefTimerBase : Assertion :=
  &("g_tickTimerBase") # UInt64 |->_ **
  &("g_oldTickTimerBase") # UInt64 |->_ **
  &("g_tickTimerBaseUpdate") # UInt |->_.

Definition storeUndefStartTime : Assertion :=
  &("g_tickTimerStartTime") # UInt64 |->_.

Definition storeUndefCPUTick (cta : Z) : Assertion :=
  &(cta # "CpuTick" ->ₛ "cntLo") # UInt |->_ **
  &(cta # "CpuTick" ->ₛ "cntHi") # UInt |->_.

Definition storeUndefTick (gt ct : Z): Assertion :=
  storeUndefArchTick gt **
  storeUndefCoreTimer ct **
  storeUndefTimerBase **
  storeUndefStartTime **
  storeUndefTickSetting.

Definition storeTickSetting (sg: StableGlobVars) : Assertion :=
  &("g_sysClock") # UInt |-> sg.(g_sysClock) **
  &("g_cyclesPerTick") # UInt |-> sg.(g_cyclesPerTick) **
  &("g_sysTimerIsInit") # UInt |-> sg.(g_sysTimerIsInit) **
  &("g_sysTickTimer") # Ptr |-> sg.(g_sysTickTimer) **
  &("SysTick") # Ptr |-> sg.(SysTick).

Definition storeArchTick (gt: Z) (att : archTickTimer): Assertion :=
  &(gt # "ArchTickTimer" ->ₛ "freq") # UInt |-> att.(freqNum) **
  &(gt # "ArchTickTimer" ->ₛ "irqNum") # Int |-> att.(irqNum) **
  &(gt # "ArchTickTimer" ->ₛ "periodMax") # UInt64 |-> att.(periodMax).

Definition storeCoreTimer (ct : Z) (ts : tickState) : Assertion :=
  &(ct # "CORE_TIM_TYPE" ->ₛ "ctrl") # UInt |-> ts.(ts_ctrl) **
  &(ct # "CORE_TIM_TYPE" ->ₛ "load") # UInt |-> ts.(ts_period) **
  &(ct # "CORE_TIM_TYPE" ->ₛ "val") # UInt |-> ts.(ts_val).

Definition storeTimerBase (ts : tickState) : Assertion :=
  &("g_tickTimerBase") # UInt64 |-> ts.(ts_timeBase) **
  &("g_oldTickTimerBase") # UInt64 |-> ts.(ts_oldTimeBase) **
  &("g_tickTimerBaseUpdate") # UInt |-> ts.(ts_timeBaseUpdate).

Definition storeStartTime (ts : tickState) : Assertion :=
  &("g_tickTimerStartTime") # UInt64 |-> ts.(ts_startTime).

Definition storeCPUTick (cta : Z) (ctv : cpuTickvalue) : Assertion :=
  (“ cta = 0 ” && emp) ||
  (“ cta <> 0 ” &&
  &(cta # "CpuTick" ->ₛ "cntLo") # UInt |-> ctv.(loNum) **
  &(cta # "CpuTick" ->ₛ "cntHi") # UInt |-> ctv.(hiNum)).

Definition storeTick (sg: StableGlobVars) (gt : Z) (tgs : TickAbstractState): Assertion :=
  storeArchTick gt tgs.(tgs_att) **
  storeCoreTimer sg.(SysTick) tgs.(tgs_ts) **
  storeTimerBase tgs.(tgs_ts) **
  storeStartTime tgs.(tgs_ts) **
  storeTickSetting sg.

Definition validArchTick(att : archTickTimer): Prop :=
  att.(freqNum) = 1000000 /\
  att.(irqNum) = 8 /\
  att.(periodMax) = 0xFFFFFF.

Definition validCoreTimer(ts : tickState) (att : archTickTimer): Prop :=
  0 < ts.(ts_period) <= (att.(periodMax)-1) /\
  0 <= ts.(ts_val) <= ts.(ts_period).

Definition validTimerBase(ts : tickState): Prop :=
  0 <= ts.(ts_startTime) /\
  0 <= ts.(ts_timeBase) /\
  0 <= ts.(ts_oldTimeBase) /\
  0 <= ts.(ts_timeBaseUpdate) <= 1.

Definition validTickSetting(sg: StableGlobVars): Prop :=
  sg.(g_sysClock) = 1000000 /\
  sg.(g_cyclesPerTick) = 10000 /\
  sg.(g_sysTimerIsInit) = 1.

Record tick_vaild_cond_prop (sg: StableGlobVars) (tgs : TickAbstractState) : Prop :=
  {
    tick_cond1 : validArchTick tgs.(tgs_att);
    tick_cond2 : validCoreTimer tgs.(tgs_ts) tgs.(tgs_att);
    tick_cond3 : validTimerBase tgs.(tgs_ts);
    tick_cond4 : validTickSetting sg ;
  }.

Definition inv_tick (sg: StableGlobVars) (tgs : TickAbstractState): Assertion :=
  “ tick_vaild_cond_prop sg tgs ” &&
  storeTick sg &("g_archTickTimer") tgs.

Definition os_inv (sg: StableGlobVars) (ls : Los_Verify_State): Assertion :=
  inv_tick sg ls.(TickState).

(******************************** 各函数抽象程序 *******************************)

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
  else if Z_le_gt_dec att.(irqNum) 32 then 
    &("g_sysClock") # UInt |-> att.(freqNum) **
    &("g_cyclesPerTick") # UInt |-> (att.(freqNum)/100) **
    &("g_sysTimerIsInit") # UInt |-> 1 **
    &("g_sysTickTimer") # Ptr |-> archTickAddr
  else 
    &("g_sysClock") # UInt |->_ **
    &("g_cyclesPerTick") # UInt |->_ **
    &("g_sysTimerIsInit") # UInt |-> 0 **
    &("g_sysTickTimer") # Ptr |-> archTickAddr.

Definition timercheck_ret(att: archTickTimer) (sg: StableGlobVars) : Z :=
  if Z_lt_dec att.(freqNum) 100 then 5
  else if Z_le_gt_dec att.(irqNum) 32 
        then if Z.eq_dec att.(periodMax) 0 then 1
            else if Z.eq_dec sg.(g_sysTimerIsInit) 0 then 0
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

Definition tickreload_ts(nextres: Z) (att: archTickTimer) (ts: tickState): tickState :=
  mkTickState ((systickreload_ret nextres att)-1)
              0 
              ((timebase_turnover ts).(ts_ctrl)) 
              ((timebase_turnover ts).(ts_startTime))
              (tick_getcycle_ret ts)
              ((timebase_turnover ts).(ts_oldTimeBase))
              ((timebase_turnover ts).(ts_timeBaseUpdate)).

Definition cpuTick2MS_ret (cta mhi mlo : Z) (sg: StableGlobVars) : Z :=
  if Z.eq_dec cta 0 then 4
  else if Z.eq_dec mhi 0 then 4
       else if Z.eq_dec mlo 0 then 4
            else if Z.eq_dec sg.(g_sysClock) 0 then 5
                 else 0.

Definition cpuTick2MS_lh (cta mhi mlo mhi_v mlo_v : Z) (sg: StableGlobVars) (ctv : cpuTickvalue): Assertion :=
  if Z.eq_dec cta 0 then 
    mhi # UInt |-> mhi_v **
    mlo # UInt |-> mlo_v
  else if Z.eq_dec mhi 0 then 
      mhi # UInt |-> mhi_v **
      mlo # UInt |-> mlo_v
      else if Z.eq_dec mlo 0 then 
          mhi # UInt |-> mhi_v **
          mlo # UInt |-> mlo_v
          else if Z.eq_dec sg.(g_sysClock) 0 then 
              mhi # UInt |-> mhi_v **
              mlo # UInt |-> mlo_v
              else 
                  mhi # UInt |-> unsigned_last_nbits (Z.shiftr (Z.lor (unsigned_last_nbits (Z.shiftl ctv.(hiNum) 32) 64) ctv.(loNum) ÷ (sg.(g_sysClock) ÷ 1000)) 32) 32 **
                  mlo # UInt |-> unsigned_last_nbits (Z.lor (unsigned_last_nbits (Z.shiftl ctv.(hiNum) 32) 64) ctv.(loNum) ÷ (sg.(g_sysClock) ÷ 1000)) 32.

Definition cpuTick2US_ret (cta mhi mlo : Z) (sg: StableGlobVars) : Z :=
  if Z.eq_dec cta 0 then 4
  else if Z.eq_dec mhi 0 then 4
        else if Z.eq_dec mlo 0 then 4
            else if Z.eq_dec sg.(g_sysClock) 0 then 5
                  else 0.

Definition cpuTick2US_lh (cta mhi mlo mhi_v mlo_v : Z) (sg: StableGlobVars) (ctv : cpuTickvalue): Assertion :=
  if Z.eq_dec cta 0 then 
    mhi # UInt |-> mhi_v **
    mlo # UInt |-> mlo_v
  else if Z.eq_dec mhi 0 then 
      mhi # UInt |-> mhi_v **
      mlo # UInt |-> mlo_v
      else if Z.eq_dec mlo 0 then 
          mhi # UInt |-> mhi_v **
          mlo # UInt |-> mlo_v
          else if Z.eq_dec sg.(g_sysClock) 0 then 
              mhi # UInt |-> mhi_v **
              mlo # UInt |-> mlo_v
              else 
                  mhi # UInt |-> unsigned_last_nbits (Z.shiftr (Z.lor (unsigned_last_nbits (Z.shiftl ctv.(hiNum) 32) 64) ctv.(loNum) ÷ (sg.(g_sysClock) ÷ 1000000)) 32) 32 **
                  mlo # UInt |-> unsigned_last_nbits (Z.lor (unsigned_last_nbits (Z.shiftl ctv.(hiNum) 32) 64) ctv.(loNum) ÷ (sg.(g_sysClock) ÷ 1000000)) 32.
