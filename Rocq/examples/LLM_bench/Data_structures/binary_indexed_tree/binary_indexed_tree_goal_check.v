From SimpleC.EE.LLM_bench.Data_structures.binary_indexed_tree Require Import binary_indexed_tree_goal binary_indexed_tree_proof_auto binary_indexed_tree_proof_manual.

Module VC_Correctness : VC_Correct.
  Include binary_indexed_tree_proof_auto.
  Include binary_indexed_tree_proof_manual.
End VC_Correctness.
