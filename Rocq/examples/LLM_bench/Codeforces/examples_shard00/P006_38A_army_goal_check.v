From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P006_38A_army_goal P006_38A_army_proof_auto P006_38A_army_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P006_38A_army_proof_auto.
  Include P006_38A_army_proof_manual.
End VC_Correctness.
