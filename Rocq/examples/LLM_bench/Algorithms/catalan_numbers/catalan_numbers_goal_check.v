From SimpleC.EE.LLM_bench.Algorithms.catalan_numbers Require Import catalan_numbers_goal catalan_numbers_proof_auto catalan_numbers_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include catalan_numbers_proof_auto.
  Include catalan_numbers_proof_manual.
End VC_Correctness.
