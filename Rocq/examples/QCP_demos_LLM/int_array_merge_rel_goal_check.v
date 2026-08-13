From SimpleC.EE.QCP_demos_LLM Require Import int_array_merge_rel_goal int_array_merge_rel_proof_auto int_array_merge_rel_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexec_strategy_proof.
  Include int_array_merge_rel_proof_auto.
  Include int_array_merge_rel_proof_manual.
End VC_Correctness.
