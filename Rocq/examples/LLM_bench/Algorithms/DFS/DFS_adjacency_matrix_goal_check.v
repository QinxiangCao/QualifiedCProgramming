From SimpleC.EE.LLM_bench.Algorithms.DFS Require Import DFS_adjacency_matrix_goal DFS_adjacency_matrix_proof_auto DFS_adjacency_matrix_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexec_strategy_proof.
  Include array2_strategy_proof.
  Include int_array_strategy_proof.
  Include int_ptr_array2_strategy_proof.
  Include graph_matrix_strategy_proof.
  Include DFS_adjacency_matrix_proof_auto.
  Include DFS_adjacency_matrix_proof_manual.
End VC_Correctness.
