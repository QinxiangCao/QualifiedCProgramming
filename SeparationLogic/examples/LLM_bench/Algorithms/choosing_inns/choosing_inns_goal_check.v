From SimpleC.EE.LLM_bench.Algorithms.choosing_inns Require Import choosing_inns_goal choosing_inns_proof_auto choosing_inns_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include choosing_inns_proof_auto.
  Include choosing_inns_proof_manual.
End VC_Correctness.
