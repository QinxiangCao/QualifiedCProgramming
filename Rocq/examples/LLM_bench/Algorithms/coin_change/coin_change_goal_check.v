From SimpleC.EE.LLM_bench.Algorithms.coin_change Require Import coin_change_goal coin_change_proof_auto coin_change_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include coin_change_proof_auto.
  Include coin_change_proof_manual.
End VC_Correctness.
