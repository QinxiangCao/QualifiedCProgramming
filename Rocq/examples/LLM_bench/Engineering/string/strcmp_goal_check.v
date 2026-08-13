From SimpleC.EE.LLM_bench.Engineering.string Require Import strcmp_goal strcmp_proof_auto strcmp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include strcmp_proof_auto.
  Include strcmp_proof_manual.
End VC_Correctness.
