From SimpleC.EE.QCP_demos_LLM Require Import array_cases_goal array_cases_proof_auto array_cases_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sll_strategy_proof.
  Include array_cases_proof_auto.
  Include array_cases_proof_manual.
End VC_Correctness.
