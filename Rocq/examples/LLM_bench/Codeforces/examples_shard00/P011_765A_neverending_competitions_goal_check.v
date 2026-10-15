From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P011_765A_neverending_competitions_goal P011_765A_neverending_competitions_proof_auto P011_765A_neverending_competitions_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array2_strategy_proof.
  Include array2_char_strategy_proof.
  Include int_array_strategy_proof.
  Include char_array_strategy_proof.
  Include array2_ext_strategy_proof.
  Include P011_765A_neverending_competitions_proof_auto.
  Include P011_765A_neverending_competitions_proof_manual.
End VC_Correctness.
