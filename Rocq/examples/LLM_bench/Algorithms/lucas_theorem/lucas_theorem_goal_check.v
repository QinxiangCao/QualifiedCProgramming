From SimpleC.EE.LLM_bench.Algorithms.lucas_theorem Require Import lucas_theorem_goal lucas_theorem_proof_auto lucas_theorem_proof_manual.

Module VC_Correctness : VC_Correct.
  Include lucas_theorem_proof_auto.
  Include lucas_theorem_proof_manual.
End VC_Correctness.
