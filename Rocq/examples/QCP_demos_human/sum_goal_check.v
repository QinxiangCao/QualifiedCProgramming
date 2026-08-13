From SimpleC.EE.QCP_demos_human Require Import sum_goal sum_proof_auto sum_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sum_proof_auto.
  Include sum_proof_manual.
End VC_Correctness.
