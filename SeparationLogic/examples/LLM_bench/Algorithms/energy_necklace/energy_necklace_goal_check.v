From SimpleC.EE.LLM_bench.Algorithms.energy_necklace Require Import energy_necklace_goal energy_necklace_proof_auto energy_necklace_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include energy_necklace_proof_auto.
  Include energy_necklace_proof_manual.
End VC_Correctness.
