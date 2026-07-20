From SimpleC.EE.LLM_bench.Algorithms.convex_hull_float Require Import convex_hull_float_goal convex_hull_float_proof_auto convex_hull_float_proof_manual.

Module VC_Correctness : VC_Correct.
  Include pointf_array_strategy_proof.
  Include convex_hull_float_proof_auto.
  Include convex_hull_float_proof_manual.
End VC_Correctness.
