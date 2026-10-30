From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P025_1384A_common_prefixes_goal P025_1384A_common_prefixes_proof_auto P025_1384A_common_prefixes_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array2_strategy_proof.
  Include array2_char_strategy_proof.
  Include array2_ext_strategy_proof.
  Include P025_1384A_common_prefixes_proof_auto.
  Include P025_1384A_common_prefixes_proof_manual.
End VC_Correctness.
