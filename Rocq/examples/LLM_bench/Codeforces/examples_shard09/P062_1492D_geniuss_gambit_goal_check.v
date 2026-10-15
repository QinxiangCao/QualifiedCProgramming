From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P062_1492D_geniuss_gambit_goal P062_1492D_geniuss_gambit_proof_auto P062_1492D_geniuss_gambit_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include P062_1492D_geniuss_gambit_proof_auto.
  Include P062_1492D_geniuss_gambit_proof_manual.
End VC_Correctness.
