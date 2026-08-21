From SimpleC.EE.QCP_demos_LLM Require Import union_find_err_rel_goal union_find_err_rel_proof_auto union_find_err_rel_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexecE_strategy_proof.
  Include union_find_err_rel_proof_auto.
  Include union_find_err_rel_proof_manual.
End VC_Correctness.
