From SimpleC.EE.Applications_human.LiteOS Require Import LOS_ListInit_goal LOS_ListInit_proof_auto LOS_ListInit_proof_manual.

Module VC_Correctness : VC_Correct.
  Include los_sortlink_strategy_proof.
  Include LOS_ListInit_proof_auto.
  Include LOS_ListInit_proof_manual.
End VC_Correctness.
