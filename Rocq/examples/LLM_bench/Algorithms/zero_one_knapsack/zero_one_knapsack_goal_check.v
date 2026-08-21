From SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack Require Import zero_one_knapsack_goal zero_one_knapsack_proof_auto zero_one_knapsack_proof_manual.

Module VC_Correctness : VC_Correct.
  Include zero_one_knapsack_proof_auto.
  Include zero_one_knapsack_proof_manual.
End VC_Correctness.
