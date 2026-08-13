From SimpleC.EE.QCP_demos_tutorial Require Import given_mark_goal given_mark_proof_auto given_mark_proof_manual.

Module VC_Correctness : VC_Correct.
  Include given_mark_proof_auto.
  Include given_mark_proof_manual.
End VC_Correctness.
