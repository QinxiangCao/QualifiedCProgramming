From SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack Require Import multiple_knapsack_goal multiple_knapsack_proof_auto multiple_knapsack_proof_manual.

Module VC_Correctness : VC_Correct.
  Include multiple_knapsack_proof_auto.
  Include multiple_knapsack_proof_manual.
End VC_Correctness.
