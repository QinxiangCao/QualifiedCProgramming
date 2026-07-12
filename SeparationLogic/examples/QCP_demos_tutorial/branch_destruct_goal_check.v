From SimpleC.EE.QCP_demos_tutorial Require Import branch_destruct_goal branch_destruct_proof_auto branch_destruct_proof_manual.

Module VC_Correctness : VC_Correct.
  Include branch_destruct_proof_auto.
  Include branch_destruct_proof_manual.
End VC_Correctness.
