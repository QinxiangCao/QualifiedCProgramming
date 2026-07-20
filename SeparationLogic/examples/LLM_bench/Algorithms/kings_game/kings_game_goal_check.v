From SimpleC.EE.LLM_bench.Algorithms.kings_game Require Import kings_game_goal kings_game_proof_auto kings_game_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include kings_game_proof_auto.
  Include kings_game_proof_manual.
End VC_Correctness.
