From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple4_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_tutorial.swap_simple1_lib.
Local Open Scope sac.
Local Open Scope string.

Lemma swap_simple4_strategy0_correctness : swap_simple4_strategy0.
Proof.
  pre_process_default.
Qed.

Lemma swap_simple4_strategy1_correctness : swap_simple4_strategy1.
Proof.
  pre_process_default.
Qed.
