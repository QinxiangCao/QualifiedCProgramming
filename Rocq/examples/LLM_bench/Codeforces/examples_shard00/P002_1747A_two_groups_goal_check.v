From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P002_1747A_two_groups_goal P002_1747A_two_groups_proof_auto P002_1747A_two_groups_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P002_1747A_two_groups_proof_auto.
  Include P002_1747A_two_groups_proof_manual.
End VC_Correctness.
