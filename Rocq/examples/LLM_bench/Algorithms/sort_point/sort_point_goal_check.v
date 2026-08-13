From SimpleC.EE.LLM_bench.Algorithms.sort_point Require Import sort_point_goal sort_point_proof_auto sort_point_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include sort_point_proof_auto.
  Include sort_point_proof_manual.
End VC_Correctness.
