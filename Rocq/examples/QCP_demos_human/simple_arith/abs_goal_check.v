From SimpleC.EE.QCP_demos_human.simple_arith Require Import abs_goal abs_proof_auto abs_proof_manual.

Module VC_Correctness : VC_Correct.
  Include abs_proof_auto.
  Include abs_proof_manual.
End VC_Correctness.
