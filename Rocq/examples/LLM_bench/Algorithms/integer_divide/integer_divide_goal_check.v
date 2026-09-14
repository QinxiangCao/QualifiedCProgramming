From SimpleC.EE.LLM_bench.Algorithms.integer_divide Require Import integer_divide_goal integer_divide_proof_auto integer_divide_proof_manual.

Module VC_Correctness : VC_Correct.
  Include integer_divide_proof_auto.
  Include integer_divide_proof_manual.
End VC_Correctness.
