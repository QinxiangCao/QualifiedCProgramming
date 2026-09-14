From SimpleC.EE.LLM_bench.Algorithms.modular_power Require Import modular_power_goal modular_power_proof_auto modular_power_proof_manual.

Module VC_Correctness : VC_Correct.
  Include modular_power_proof_auto.
  Include modular_power_proof_manual.
End VC_Correctness.
