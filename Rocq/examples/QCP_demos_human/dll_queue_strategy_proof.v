From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.EE.QCP_demos_human Require Import dll_queue_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import dll_queue_lib.
Import naive_C_Rules.
Local Open Scope sac.
Local Open Scope string.

Lemma dll_queue_strategy0_correctness : dll_queue_strategy0.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma dll_queue_strategy1_correctness : dll_queue_strategy1.
  pre_process_default.
  Intros; subst; entailer!.
Qed.
