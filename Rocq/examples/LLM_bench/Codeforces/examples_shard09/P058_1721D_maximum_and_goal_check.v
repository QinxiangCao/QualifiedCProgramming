From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P058_1721D_maximum_and_goal P058_1721D_maximum_and_proof_auto P058_1721D_maximum_and_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P058_1721D_maximum_and_proof_auto.
  Include P058_1721D_maximum_and_proof_manual.
End VC_Correctness.
