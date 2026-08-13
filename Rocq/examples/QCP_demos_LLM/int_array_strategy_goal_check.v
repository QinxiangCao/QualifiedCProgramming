From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal int_array_strategy_proof.

Module int_array_Strategy_Correctness : int_array_Strategy_Correct.
  Include int_array_strategy_proof.
End int_array_Strategy_Correctness.
