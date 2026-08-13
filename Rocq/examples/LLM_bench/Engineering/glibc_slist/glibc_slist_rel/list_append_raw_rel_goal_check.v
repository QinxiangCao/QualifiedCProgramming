From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import list_append_raw_rel_goal list_append_raw_rel_proof_auto list_append_raw_rel_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexecE_strategy_proof.
  Include sll_strategy_proof.
  Include list_append_raw_rel_proof_auto.
  Include list_append_raw_rel_proof_manual.
End VC_Correctness.
