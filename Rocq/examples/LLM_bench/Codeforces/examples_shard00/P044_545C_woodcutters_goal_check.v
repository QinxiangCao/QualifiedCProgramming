From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P044_545C_woodcutters_goal P044_545C_woodcutters_proof_auto P044_545C_woodcutters_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P044_545C_woodcutters_proof_auto.
  Include P044_545C_woodcutters_proof_manual.
End VC_Correctness.
