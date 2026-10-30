From SimpleC.EE.LLM_bench.Algorithms.catalan_numbers Require Import catalan_numbers_goal catalan_numbers_proof_auto catalan_numbers_proof_manual.

Module VC_Correctness : VC_Correct.
  Include catalan_numbers_proof_auto.
  Include catalan_numbers_proof_manual.
End VC_Correctness.
