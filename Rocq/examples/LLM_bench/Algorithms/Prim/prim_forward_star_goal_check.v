From SimpleC.EE.LLM_bench.Algorithms.Prim Require Import prim_forward_star_goal prim_forward_star_proof_auto prim_forward_star_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexec_strategy_proof.
  Include prim_forward_star_proof_auto.
  Include prim_forward_star_proof_manual.
End VC_Correctness.
