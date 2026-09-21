From SimpleC.EE.LLM_bench.Algorithms.magic_items Require Import magic_items_goal magic_items_proof_auto magic_items_proof_manual.

Module VC_Correctness : VC_Correct.
  Include magic_items_proof_auto.
  Include magic_items_proof_manual.
End VC_Correctness.
