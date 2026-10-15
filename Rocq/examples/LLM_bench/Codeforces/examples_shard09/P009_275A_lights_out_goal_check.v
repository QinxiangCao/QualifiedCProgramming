From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P009_275A_lights_out_goal P009_275A_lights_out_proof_auto P009_275A_lights_out_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array2_strategy_proof.
  Include array2_char_strategy_proof.
  Include int_array_strategy_proof.
  Include char_array_strategy_proof.
  Include array2_ext_strategy_proof.
  Include P009_275A_lights_out_proof_auto.
  Include P009_275A_lights_out_proof_manual.
End VC_Correctness.
