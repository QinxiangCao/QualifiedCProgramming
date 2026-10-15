From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P018_1146B_hate_a_goal P018_1146B_hate_a_proof_auto P018_1146B_hate_a_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include P018_1146B_hate_a_proof_auto.
  Include P018_1146B_hate_a_proof_manual.
End VC_Correctness.
