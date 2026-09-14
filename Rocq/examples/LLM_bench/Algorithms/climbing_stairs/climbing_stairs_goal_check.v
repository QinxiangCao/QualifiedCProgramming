From SimpleC.EE.LLM_bench.Algorithms.climbing_stairs Require Import climbing_stairs_goal climbing_stairs_proof_auto climbing_stairs_proof_manual.

Module VC_Correctness : VC_Correct.
  Include climbing_stairs_proof_auto.
  Include climbing_stairs_proof_manual.
End VC_Correctness.
