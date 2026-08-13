From SimpleC.EE.LLM_bench.Engineering.string Require Import memchr_goal memchr_proof_auto memchr_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include memchr_proof_auto.
  Include memchr_proof_manual.
End VC_Correctness.
