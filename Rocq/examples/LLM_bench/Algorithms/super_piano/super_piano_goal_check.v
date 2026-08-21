From SimpleC.EE.LLM_bench.Algorithms.super_piano Require Import super_piano_goal super_piano_proof_auto super_piano_proof_manual.

Module VC_Correctness : VC_Correct.
  Include super_piano_proof_auto.
  Include super_piano_proof_manual.
End VC_Correctness.
