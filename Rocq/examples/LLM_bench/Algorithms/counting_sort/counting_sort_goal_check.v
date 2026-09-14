From SimpleC.EE.LLM_bench.Algorithms.counting_sort Require Import counting_sort_goal counting_sort_proof_auto counting_sort_proof_manual.

Module VC_Correctness : VC_Correct.
  Include counting_sort_proof_auto.
  Include counting_sort_proof_manual.
End VC_Correctness.
