From SimpleC.EE.LLM_bench.Algorithms.Kruskal Require Import kruskal_union_find_goal kruskal_union_find_proof_auto kruskal_union_find_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexec_strategy_proof.
  Include kruskal_union_find_proof_auto.
  Include kruskal_union_find_proof_manual.
End VC_Correctness.
