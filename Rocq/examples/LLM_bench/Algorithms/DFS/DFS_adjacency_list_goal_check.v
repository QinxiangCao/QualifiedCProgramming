From SimpleC.EE.LLM_bench.Algorithms.DFS Require Import DFS_adjacency_list_goal DFS_adjacency_list_proof_auto DFS_adjacency_list_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexec_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include sll_strategy_proof.
  Include DFS_adjacency_list_proof_auto.
  Include DFS_adjacency_list_proof_manual.
End VC_Correctness.
