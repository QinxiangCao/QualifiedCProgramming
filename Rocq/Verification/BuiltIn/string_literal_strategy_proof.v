From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.Verification.BuiltIn Require Import string_literal_strategy_goal.
Import naive_C_Rules.
Local Open Scope sac.

Lemma string_literal_strategy1_correctness : string_literal_strategy1.
  pre_process_default.
Admitted.

Lemma string_literal_strategy3_correctness : string_literal_strategy3.
  pre_process_default.
Admitted.

Lemma string_literal_strategy5_correctness : string_literal_strategy5.
  pre_process_default.
Admitted.

Lemma string_literal_strategy6_correctness : string_literal_strategy6.
  pre_process_default.
Admitted.

Lemma string_literal_strategy7_correctness : string_literal_strategy7.
  pre_process_default.
Admitted.

Lemma string_literal_strategy8_correctness : string_literal_strategy8.
  pre_process_default.
Admitted.

Lemma string_literal_strategy2_correctness : string_literal_strategy2.
  pre_process_default.
Admitted.

Lemma string_literal_strategy4_correctness : string_literal_strategy4.
  pre_process_default.
Admitted.
