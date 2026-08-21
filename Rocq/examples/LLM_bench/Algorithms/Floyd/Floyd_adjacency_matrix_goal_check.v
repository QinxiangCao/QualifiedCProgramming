From SimpleC.EE.LLM_bench.Algorithms.Floyd Require Import Floyd_adjacency_matrix_goal Floyd_adjacency_matrix_proof_auto Floyd_adjacency_matrix_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexec_strategy_proof.
  Include array2_strategy_proof.
  Include int_array_strategy_proof.
  Include int_ptr_array2_strategy_proof.
  Include graph_matrix_strategy_proof.
  Include Floyd_adjacency_matrix_proof_auto.
  Include Floyd_adjacency_matrix_proof_manual.
End VC_Correctness.
