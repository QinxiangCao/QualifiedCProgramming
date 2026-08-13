From SimpleC.EE.Applications_human.LiteOS Require Import OsGetNextExpireTime_goal OsGetNextExpireTime_proof_auto OsGetNextExpireTime_proof_manual.

Module VC_Correctness : VC_Correct.
  Include los_sortlink_strategy_proof.
  Include OsGetNextExpireTime_proof_auto.
  Include OsGetNextExpireTime_proof_manual.
End VC_Correctness.
