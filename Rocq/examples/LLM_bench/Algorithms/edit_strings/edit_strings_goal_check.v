From SimpleC.EE.LLM_bench.Algorithms.edit_strings Require Import edit_strings_goal edit_strings_proof_auto edit_strings_proof_manual.

Module VC_Correctness : VC_Correct.
  Include edit_strings_proof_auto.
  Include edit_strings_proof_manual.
End VC_Correctness.
