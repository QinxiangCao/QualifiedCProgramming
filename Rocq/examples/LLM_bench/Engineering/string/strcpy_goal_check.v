From SimpleC.EE.LLM_bench.Engineering.string Require Import strcpy_goal strcpy_proof_auto strcpy_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include strcpy_proof_auto.
  Include strcpy_proof_manual.
End VC_Correctness.
