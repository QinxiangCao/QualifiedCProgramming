From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P082_623B_array_gcd_goal P082_623B_array_gcd_proof_auto P082_623B_array_gcd_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P082_623B_array_gcd_proof_auto.
  Include P082_623B_array_gcd_proof_manual.
End VC_Correctness.
