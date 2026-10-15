From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P064_223C_partial_sums_goal P064_223C_partial_sums_proof_auto P064_223C_partial_sums_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P064_223C_partial_sums_proof_auto.
  Include P064_223C_partial_sums_proof_manual.
End VC_Correctness.
