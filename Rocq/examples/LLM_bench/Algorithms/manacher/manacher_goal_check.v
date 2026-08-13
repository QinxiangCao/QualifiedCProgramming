From SimpleC.EE.LLM_bench.Algorithms.manacher Require Import manacher_goal manacher_proof_auto manacher_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include manacher_proof_auto.
  Include manacher_proof_manual.
End VC_Correctness.
