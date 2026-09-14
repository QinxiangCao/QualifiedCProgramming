From SimpleC.EE.LLM_bench.Algorithms.modular_mul Require Import modular_mul_goal modular_mul_proof_auto modular_mul_proof_manual.

Module VC_Correctness : VC_Correct.
  Include modular_mul_proof_auto.
  Include modular_mul_proof_manual.
End VC_Correctness.
