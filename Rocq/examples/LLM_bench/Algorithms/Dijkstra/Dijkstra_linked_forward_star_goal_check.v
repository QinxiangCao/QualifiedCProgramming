From SimpleC.EE.LLM_bench.Algorithms.Dijkstra Require Import Dijkstra_linked_forward_star_goal Dijkstra_linked_forward_star_proof_auto Dijkstra_linked_forward_star_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexec_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include Dijkstra_linked_forward_star_proof_auto.
  Include Dijkstra_linked_forward_star_proof_manual.
End VC_Correctness.
