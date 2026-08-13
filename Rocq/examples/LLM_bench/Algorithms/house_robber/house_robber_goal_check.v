From SimpleC.EE.LLM_bench.Algorithms.house_robber Require Import house_robber_goal house_robber_proof_auto house_robber_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include house_robber_proof_auto.
  Include house_robber_proof_manual.
End VC_Correctness.
