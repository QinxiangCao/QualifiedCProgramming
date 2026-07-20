From SimpleC.EE.LLM_bench.Algorithms.insertion_sort Require Import insertion_sort_goal insertion_sort_proof_auto insertion_sort_proof_manual.

Module VC_Correctness : VC_Correct.
  Include insertion_sort_proof_auto.
  Include insertion_sort_proof_manual.
End VC_Correctness.
