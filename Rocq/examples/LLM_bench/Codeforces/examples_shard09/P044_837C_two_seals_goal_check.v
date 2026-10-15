From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P044_837C_two_seals_goal P044_837C_two_seals_proof_auto P044_837C_two_seals_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P044_837C_two_seals_proof_auto.
  Include P044_837C_two_seals_proof_manual.
End VC_Correctness.
