From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P013_1744C_traffic_light_goal P013_1744C_traffic_light_proof_auto P013_1744C_traffic_light_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include P013_1744C_traffic_light_proof_auto.
  Include P013_1744C_traffic_light_proof_manual.
End VC_Correctness.
