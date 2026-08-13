From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import glibc_slist_merge_rel_goal glibc_slist_merge_rel_proof_auto glibc_slist_merge_rel_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexecE_strategy_proof.
  Include sll_strategy_proof.
  Include glibc_slist_merge_rel_proof_auto.
  Include glibc_slist_merge_rel_proof_manual.
End VC_Correctness.
