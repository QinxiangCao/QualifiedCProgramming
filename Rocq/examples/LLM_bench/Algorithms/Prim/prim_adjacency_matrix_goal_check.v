From SimpleC.EE.LLM_bench.Algorithms.Prim Require Import prim_adjacency_matrix_goal prim_adjacency_matrix_proof_auto prim_adjacency_matrix_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_ptr_array2_strategy_proof.
  Include int_array_strategy_proof.
  Include array2_strategy_proof.
  Include graph_matrix_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include safeexec_strategy_proof.
  Include prim_adjacency_matrix_proof_auto.
  Include prim_adjacency_matrix_proof_manual.
End VC_Correctness.
