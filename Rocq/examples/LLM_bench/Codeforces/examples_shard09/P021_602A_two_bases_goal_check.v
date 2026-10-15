From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P021_602A_two_bases_goal P021_602A_two_bases_proof_auto P021_602A_two_bases_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P021_602A_two_bases_proof_auto.
  Include P021_602A_two_bases_proof_manual.
End VC_Correctness.
