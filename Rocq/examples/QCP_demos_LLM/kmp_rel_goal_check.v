From SimpleC.EE.QCP_demos_LLM Require Import kmp_rel_goal kmp_rel_proof_auto kmp_rel_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexecE_strategy_proof.
  Include kmp_rel_proof_auto.
  Include kmp_rel_proof_manual.
End VC_Correctness.
