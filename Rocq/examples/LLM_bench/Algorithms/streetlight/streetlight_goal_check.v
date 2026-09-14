From SimpleC.EE.LLM_bench.Algorithms.streetlight Require Import streetlight_goal streetlight_proof_auto streetlight_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array2_strategy_proof.
  Include int_array_strategy_proof.
  Include streetlight_proof_auto.
  Include streetlight_proof_manual.
End VC_Correctness.
