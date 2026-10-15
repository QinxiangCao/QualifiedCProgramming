From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P040_81A_plug_in_goal P040_81A_plug_in_proof_auto P040_81A_plug_in_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P040_81A_plug_in_proof_auto.
  Include P040_81A_plug_in_proof_manual.
End VC_Correctness.
