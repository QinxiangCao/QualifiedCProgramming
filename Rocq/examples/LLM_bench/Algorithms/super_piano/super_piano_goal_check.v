From SimpleC.EE.LLM_bench.Algorithms.super_piano Require Import super_piano_goal super_piano_proof_auto super_piano_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include super_piano_proof_auto.
  Include super_piano_proof_manual.
End VC_Correctness.
