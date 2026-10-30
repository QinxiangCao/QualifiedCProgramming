From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.StdLib Require Import string_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Local Open Scope sac.
Local Open Scope string.

Lemma string_strategy1_correctness : string_strategy1.
  pre_process_default.
Qed.

Lemma string_strategy2_correctness : string_strategy2.
  pre_process_default.
Qed.
