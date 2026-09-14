From SimpleC.EE.Applications_human.hashtable Require Import hashtbl_goal hashtbl_proof_auto hashtbl_proof_manual.

Module VC_Correctness : VC_Correct.
  Include hashtbl_strategy_proof.
  Include hashtbl_proof_auto.
  Include hashtbl_proof_manual.
End VC_Correctness.
