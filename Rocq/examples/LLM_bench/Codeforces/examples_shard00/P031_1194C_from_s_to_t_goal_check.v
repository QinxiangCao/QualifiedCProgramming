From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P031_1194C_from_s_to_t_goal P031_1194C_from_s_to_t_proof_auto P031_1194C_from_s_to_t_proof_manual.

Module VC_Correctness : VC_Correct.
  Include string_strategy_proof.
  Include P031_1194C_from_s_to_t_proof_auto.
  Include P031_1194C_from_s_to_t_proof_manual.
End VC_Correctness.
