From SimpleC.EE.Applications_human.cnf_trans Require Import cnf_trans_goal cnf_trans_proof_auto cnf_trans_proof_manual.

Module VC_Correctness : VC_Correct.
  Include cnf_trans_proof_auto.
  Include cnf_trans_proof_manual.
End VC_Correctness.
