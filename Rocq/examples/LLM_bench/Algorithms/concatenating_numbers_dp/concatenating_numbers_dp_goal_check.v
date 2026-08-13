From SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp Require Import concatenating_numbers_dp_goal concatenating_numbers_dp_proof_auto concatenating_numbers_dp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include concatenating_numbers_dp_proof_auto.
  Include concatenating_numbers_dp_proof_manual.
End VC_Correctness.
