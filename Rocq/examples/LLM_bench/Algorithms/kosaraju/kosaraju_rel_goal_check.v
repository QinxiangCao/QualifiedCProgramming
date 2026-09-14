From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import kosaraju_rel_goal kosaraju_rel_proof_auto kosaraju_rel_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexecE_strategy_proof.
  Include kosaraju_rel_proof_auto.
  Include kosaraju_rel_proof_manual.
End VC_Correctness.
