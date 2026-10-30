From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P037_1266C_diverse_matrix_goal P037_1266C_diverse_matrix_proof_auto P037_1266C_diverse_matrix_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array2_strategy_proof.
  Include array2_char_strategy_proof.
  Include array2_ext_strategy_proof.
  Include P037_1266C_diverse_matrix_proof_auto.
  Include P037_1266C_diverse_matrix_proof_manual.
End VC_Correctness.
