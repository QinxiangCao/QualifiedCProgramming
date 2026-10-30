From SimpleC.EE.Applications_human.minisat Require Import vec_qcp_goal vec_qcp_proof_auto vec_qcp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include vec_qcp_strategy_proof.
  Include vec_qcp_proof_auto.
  Include vec_qcp_proof_manual.
End VC_Correctness.
