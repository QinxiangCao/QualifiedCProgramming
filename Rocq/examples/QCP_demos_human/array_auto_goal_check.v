From SimpleC.EE.QCP_demos_human Require Import array_auto_goal array_auto_proof_auto array_auto_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sll_shape_strategy_proof.
  Include array_auto_proof_auto.
  Include array_auto_proof_manual.
End VC_Correctness.
