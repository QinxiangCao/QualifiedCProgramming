From SimpleC.EE.LLM_bench.Algorithms.Kruskal Require Import kruskal_union_find_goal kruskal_union_find_proof_auto kruskal_union_find_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexec_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include kruskal_union_find_proof_auto.
  Include kruskal_union_find_proof_manual.
End VC_Correctness.
