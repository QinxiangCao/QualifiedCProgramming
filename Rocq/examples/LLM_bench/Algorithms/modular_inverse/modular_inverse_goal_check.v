From SimpleC.EE.LLM_bench.Algorithms.modular_inverse Require Import modular_inverse_goal modular_inverse_proof_auto modular_inverse_proof_manual.

Module VC_Correctness : VC_Correct.
  Include modular_inverse_proof_auto.
  Include modular_inverse_proof_manual.
End VC_Correctness.
