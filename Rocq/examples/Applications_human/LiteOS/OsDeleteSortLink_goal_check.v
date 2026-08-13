From SimpleC.EE.Applications_human.LiteOS Require Import OsDeleteSortLink_goal OsDeleteSortLink_proof_auto OsDeleteSortLink_proof_manual.

Module VC_Correctness : VC_Correct.
  Include los_sortlink_strategy_proof.
  Include OsDeleteSortLink_proof_auto.
  Include OsDeleteSortLink_proof_manual.
End VC_Correctness.
