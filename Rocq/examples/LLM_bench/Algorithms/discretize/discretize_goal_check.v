From SimpleC.EE.LLM_bench.Algorithms.discretize Require Import discretize_goal discretize_proof_auto discretize_proof_manual.

Module VC_Correctness : VC_Correct.
  Include discretize_proof_auto.
  Include discretize_proof_manual.
End VC_Correctness.
