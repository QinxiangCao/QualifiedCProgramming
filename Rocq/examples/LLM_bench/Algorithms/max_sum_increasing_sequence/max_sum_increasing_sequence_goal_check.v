From SimpleC.EE.LLM_bench.Algorithms.max_sum_increasing_sequence Require Import max_sum_increasing_sequence_goal max_sum_increasing_sequence_proof_auto max_sum_increasing_sequence_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include max_sum_increasing_sequence_proof_auto.
  Include max_sum_increasing_sequence_proof_manual.
End VC_Correctness.
