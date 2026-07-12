From SimpleC.EE.QCP_demos_tutorial Require Import float_goal float_proof_auto float_proof_manual.

Module VC_Correctness : VC_Correct.
  Include float_proof_auto.
  Include float_proof_manual.
End VC_Correctness.
