From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P058_132C_logo_turtle_goal P058_132C_logo_turtle_proof_auto P058_132C_logo_turtle_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include P058_132C_logo_turtle_proof_auto.
  Include P058_132C_logo_turtle_proof_manual.
End VC_Correctness.
