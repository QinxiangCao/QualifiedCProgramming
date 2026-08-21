From SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_fill_index2 Require Import quicksort_goal quicksort_proof_auto quicksort_proof_manual.

Module VC_Correctness : VC_Correct.
  Include quicksort_proof_auto.
  Include quicksort_proof_manual.
End VC_Correctness.
