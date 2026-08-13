From SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum Require Import sliding_window_maximum_goal sliding_window_maximum_proof_auto sliding_window_maximum_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include sliding_window_maximum_proof_auto.
  Include sliding_window_maximum_proof_manual.
End VC_Correctness.
