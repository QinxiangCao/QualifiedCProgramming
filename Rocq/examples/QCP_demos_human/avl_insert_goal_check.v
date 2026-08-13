From SimpleC.EE.QCP_demos_human Require Import avl_insert_goal avl_insert_proof_auto avl_insert_proof_manual.

Module VC_Correctness : VC_Correct.
  Include avl_strategy_proof.
  Include avl_insert_proof_auto.
  Include avl_insert_proof_manual.
End VC_Correctness.
