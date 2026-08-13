From SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index2 Require Import quicksort_goal quicksort_proof_auto quicksort_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include quicksort_proof_auto.
  Include quicksort_proof_manual.
End VC_Correctness.
