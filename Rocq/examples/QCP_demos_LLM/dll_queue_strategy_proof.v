Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import dll_queue_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import dll_queue_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma dll_queue_strategy0_correctness : dll_queue_strategy0.
Proof.
  pre_process_default.
  Intros_p H.
  subst l1.
  cancel.
Qed.

Lemma dll_queue_strategy1_correctness : dll_queue_strategy1.
Proof.
  pre_process_default.
  Intros_p H.
  subst l1.
  cancel.
Qed.
