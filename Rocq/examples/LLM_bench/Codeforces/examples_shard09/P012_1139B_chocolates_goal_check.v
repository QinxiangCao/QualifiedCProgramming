From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P012_1139B_chocolates_goal P012_1139B_chocolates_proof_auto P012_1139B_chocolates_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P012_1139B_chocolates_proof_auto.
  Include P012_1139B_chocolates_proof_manual.
End VC_Correctness.
