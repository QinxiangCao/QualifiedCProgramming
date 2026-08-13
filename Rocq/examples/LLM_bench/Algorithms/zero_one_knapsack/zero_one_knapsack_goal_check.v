From SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack Require Import zero_one_knapsack_goal zero_one_knapsack_proof_auto zero_one_knapsack_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include zero_one_knapsack_proof_auto.
  Include zero_one_knapsack_proof_manual.
End VC_Correctness.
