From SimpleC.EE.LLM_bench.Algorithms.kosaraju Require Import dfs1_goal dfs1_proof_auto dfs1_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexecE_strategy_proof.
  Include dfs1_proof_auto.
  Include dfs1_proof_manual.
End VC_Correctness.
