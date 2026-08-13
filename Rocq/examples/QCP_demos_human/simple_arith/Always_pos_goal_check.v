From SimpleC.EE.QCP_demos_human.simple_arith Require Import Always_pos_goal Always_pos_proof_auto Always_pos_proof_manual.

Module VC_Correctness : VC_Correct.
  Include Always_pos_proof_auto.
  Include Always_pos_proof_manual.
End VC_Correctness.
