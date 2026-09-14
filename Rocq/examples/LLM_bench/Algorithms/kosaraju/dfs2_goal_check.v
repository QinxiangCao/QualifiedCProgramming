From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import dfs2_goal dfs2_proof_auto dfs2_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexecE_strategy_proof.
  Include dfs2_proof_auto.
  Include dfs2_proof_manual.
End VC_Correctness.
