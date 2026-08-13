From SimpleC.EE.LLM_bench.Engineering.string Require Import strcat_goal strcat_proof_auto strcat_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include strcat_proof_auto.
  Include strcat_proof_manual.
End VC_Correctness.
