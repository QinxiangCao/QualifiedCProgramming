From SimpleC.EE.QCP_demos_human.simple_arith Require Import max3_goal max3_proof_auto max3_proof_manual.

Module VC_Correctness : VC_Correct.
  Include max3_proof_auto.
  Include max3_proof_manual.
End VC_Correctness.
