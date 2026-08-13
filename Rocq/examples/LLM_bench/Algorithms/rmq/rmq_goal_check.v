From SimpleC.EE.LLM_bench.Algorithms.rmq Require Import rmq_goal rmq_proof_auto rmq_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include rmq_proof_auto.
  Include rmq_proof_manual.
End VC_Correctness.
