From SimpleC.EE.QCP_demos_human Require Import chars_goal chars_proof_auto chars_proof_manual.

Module VC_Correctness : VC_Correct.
  Include chars_proof_auto.
  Include chars_proof_manual.
End VC_Correctness.
