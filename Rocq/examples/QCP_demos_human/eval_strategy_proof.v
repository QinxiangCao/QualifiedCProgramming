From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.EE.QCP_demos_human Require Import eval_strategy_goal.
Import naive_C_Rules.

From SimpleC.EE.QCP_demos_human Require Import eval_lib.
Local Open Scope sac.
Local Open Scope string.

Lemma eval_strategy0_correctness : eval_strategy0.
  pre_process_default.
  Intros; subst.
  entailer!.
Qed.

Lemma eval_strategy1_correctness : eval_strategy1.
  pre_process_default.
  Intros; subst.
  entailer!.
Qed.
