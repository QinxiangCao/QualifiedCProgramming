From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.EE.Applications_human.minigmp Require Import gmp_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minigmp.GmpAux SimpleC.EE.Applications_human.minigmp.GmpNumber.
Import Aux.
Local Open Scope sac.
Local Open Scope string.

Lemma gmp_strategy1_correctness : gmp_strategy1.
  pre_process_default.
Admitted.

Lemma gmp_strategy2_correctness : gmp_strategy2.
  pre_process_default.
Admitted.

Lemma gmp_strategy3_correctness : gmp_strategy3.
  pre_process_default.
Admitted.

Lemma gmp_strategy4_correctness : gmp_strategy4.
  pre_process_default.
Admitted.
