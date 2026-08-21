From SimpleC.EE.LLM_bench.Algorithms.sort_point Require Import sort_point_goal sort_point_proof_auto sort_point_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sort_point_proof_auto.
  Include sort_point_proof_manual.
End VC_Correctness.
