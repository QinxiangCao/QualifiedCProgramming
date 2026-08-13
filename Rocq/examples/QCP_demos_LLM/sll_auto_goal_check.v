From SimpleC.EE.QCP_demos_LLM Require Import sll_auto_goal sll_auto_proof_auto sll_auto_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sll_shape_strategy_proof.
  Include sll_auto_proof_auto.
  Include sll_auto_proof_manual.
End VC_Correctness.
