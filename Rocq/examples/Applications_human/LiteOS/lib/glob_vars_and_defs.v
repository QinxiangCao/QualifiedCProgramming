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

Record StableGlobVars: Type := {
  g_taskCBArray: addr;
  g_swtmrCBArray: addr;
  g_swtmrFreeList: addr;
  g_swtmrSortLink: addr;
  g_taskSortLink: addr;
  g_allSem: addr;
  g_allQueue: addr;
  g_allMux: addr;
  g_priQueueList : addr;
  g_sysTickTimer: addr;
  SysTick: Z;
  g_cyclesPerTick: Z;
  g_sysClock: Z;
  g_sysTimerIsInit: Z;
  idleTaskID : Z;
  swtmrTaskID : Z;
}.

(**
  以下变量为结构体全局变量，只需使用它们的地址，而不是值，因此不计入StableGlobVars
    g_losFreeTask;
    g_taskRecycleList;
    g_unusedSemList;
    g_freeQueueList;
*)

Notation "x '.(g_taskCBArray)'" := (g_taskCBArray x) (at level 1).
Notation "x '.(g_swtmrCBArray)'" := (g_swtmrCBArray x) (at level 1).
Notation "x '.(g_allSem)'" := (g_allSem x) (at level 1).
Notation "x '.(g_allQueue)'" := (g_allQueue x) (at level 1).
Notation "x '.(g_priQueueList)'" := (g_priQueueList x) (at level 1).
Notation "x '.(g_sysTickTimer)'" := (g_sysTickTimer x) (at level 1).
Notation "x '.(g_cyclesPerTick)'" := (g_cyclesPerTick x) (at level 1).
Notation "x '.(g_sysClock)'" := (g_sysClock x) (at level 1).
Notation "x '.(g_sysTimerIsInit)'" := (g_sysTimerIsInit x) (at level 1).
Notation "x '.(SysTick)'" := (SysTick x) (at level 1).
Notation "x '.(idleTaskID)'" := (idleTaskID x) (at level 1).
Notation "x '.(swtmrTaskID)'" := (swtmrTaskID x) (at level 1).

Notation "x '.(g_taskCBArray)'" := (g_taskCBArray x)
  (in custom lvalue_expr_entry at level 1).
Notation "x '.(g_swtmrCBArray)'" := (g_swtmrCBArray x)
  (in custom lvalue_expr_entry at level 1).
Notation "x '.(g_allSem)'" := (g_allSem x)
  (in custom lvalue_expr_entry at level 1).
Notation "x '.(g_allQueue)'" := (g_allQueue x)
  (in custom lvalue_expr_entry at level 1).
Notation "x '.(g_priQueueList)'" := (g_priQueueList x)
  (in custom lvalue_expr_entry at level 1).
Notation "x '.(g_sysTickTimer)'" := (g_sysTickTimer x)
  (in custom lvalue_expr_entry at level 1).
Notation "x '.(g_cyclesPerTick)'" := (g_cyclesPerTick x)
  (in custom lvalue_expr_entry at level 1).
Notation "x '.(g_sysClock)'" := (g_sysClock x)
  (in custom lvalue_expr_entry at level 1).
Notation "x '.(g_sysTimerIsInit)'" := (g_sysTimerIsInit x)
  (in custom lvalue_expr_entry at level 1).
Notation "x '.(SysTick)'" := (SysTick x)
  (in custom lvalue_expr_entry at level 1).
Notation "x '.(idleTaskID)'" := (idleTaskID x)
  (in custom lvalue_expr_entry at level 1).
Notation "x '.(swtmrTaskID)'" := (swtmrTaskID x)
  (in custom lvalue_expr_entry at level 1).

Notation "x '.(g_taskCBArray)'" := (g_taskCBArray x)
  (in custom rvalue_expr_entry at level 1).
Notation "x '.(g_swtmrCBArray)'" := (g_swtmrCBArray x)
  (in custom rvalue_expr_entry at level 1).
Notation "x '.(g_allSem)'" := (g_allSem x)
  (in custom rvalue_expr_entry at level 1).
Notation "x '.(g_allQueue)'" := (g_allQueue x)
  (in custom rvalue_expr_entry at level 1).
Notation "x '.(g_priQueueList)'" := (g_priQueueList x)
  (in custom rvalue_expr_entry at level 1).
Notation "x '.(g_sysTickTimer)'" := (g_sysTickTimer x)
  (in custom rvalue_expr_entry at level 1).
Notation "x '.(g_cyclesPerTick)'" := (g_cyclesPerTick x)
  (in custom rvalue_expr_entry at level 1).
Notation "x '.(g_sysClock)'" := (g_sysClock x)
  (in custom rvalue_expr_entry at level 1).
Notation "x '.(g_sysTimerIsInit)'" := (g_sysTimerIsInit x)
  (in custom rvalue_expr_entry at level 1).
Notation "x '.(SysTick)'" := (SysTick x)
  (in custom rvalue_expr_entry at level 1).
Notation "x '.(idleTaskID)'" := (idleTaskID x)
  (in custom rvalue_expr_entry at level 1).
Notation "x '.(swtmrTaskID)'" := (swtmrTaskID x)
  (in custom rvalue_expr_entry at level 1).

Definition TaskID := Z.  (* 任务ID *)
Definition SwtmrID: Type := Z.
(* Definition g_taskSortLink: Type := addr. *)
(* Definition g_swtmrSortLink: Type := addr. *)

Module DLL.

Record DL_Node (A: Type): Type :=
  Build_DL_Node {
    data: A;
    ptr: addr;
  }.

Arguments data {A} _.
Arguments ptr {A} _.
Arguments Build_DL_Node {A} _ _.

End DLL.

Export DLL.
Notation "x '.(dll_data)'" := (DLL.data x) (at level 1).
Notation "x '.(ptr)'" := (DLL.ptr x) (at level 1).

Definition ResponseTime := Z.

Module SDLL.

Record sortedLinkNode (A: Type) : Type := mksortedLinkNode {
    sl_data : A;
    responseTime : ResponseTime;
}.

Arguments responseTime {A} _.
Arguments sl_data {A} _.
Arguments mksortedLinkNode {A} _ _.

End SDLL.
Export SDLL.

Notation "x '.(response_time)'" := (DLL.data (SDLL.responseTime x)) (at level 1).
Notation "x '.(sdll_data)'" := (DLL.data (SDLL.sl_data x)) (at level 1).
Notation "'ULLONG_MAX'" := (2^64 - 1).