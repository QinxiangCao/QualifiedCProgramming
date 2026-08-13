From SimpleC.EE.LLM_bench.Algorithms.split_array_largest_sum Require Import split_array_largest_sum_goal split_array_largest_sum_proof_auto split_array_largest_sum_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include split_array_largest_sum_proof_auto.
  Include split_array_largest_sum_proof_manual.
End VC_Correctness.
