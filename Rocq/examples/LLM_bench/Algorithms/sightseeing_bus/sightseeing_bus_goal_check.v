From SimpleC.EE.LLM_bench.Algorithms.sightseeing_bus Require Import sightseeing_bus_goal sightseeing_bus_proof_auto sightseeing_bus_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sightseeing_bus_proof_auto.
  Include sightseeing_bus_proof_manual.
End VC_Correctness.
