From SimpleC.EE.LLM_bench.Algorithms.merging_stones Require Import merging_stones_goal merging_stones_proof_auto merging_stones_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array2_strategy_proof.
  Include int_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include merging_stones_proof_auto.
  Include merging_stones_proof_manual.
End VC_Correctness.
