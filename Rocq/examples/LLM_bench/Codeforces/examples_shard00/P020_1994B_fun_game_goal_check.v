From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P020_1994B_fun_game_goal P020_1994B_fun_game_proof_auto P020_1994B_fun_game_proof_manual.

Module VC_Correctness : VC_Correct.
  Include string_strategy_proof.
  Include P020_1994B_fun_game_proof_auto.
  Include P020_1994B_fun_game_proof_manual.
End VC_Correctness.
