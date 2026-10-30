From SimpleC.EE.LLM_bench.Algorithms.DFS Require Import DFS_adjacency_list_goal DFS_adjacency_list_proof_auto DFS_adjacency_list_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexec_strategy_proof.
  Include sll_strategy_proof.
  Include DFS_adjacency_list_proof_auto.
  Include DFS_adjacency_list_proof_manual.
End VC_Correctness.
