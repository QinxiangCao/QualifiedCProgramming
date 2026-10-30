From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_support_goal solver_qcp_support_proof_auto solver_qcp_support_proof_manual.

Module VC_Correctness : VC_Correct.
  Include solver_qcp_strategy_proof.
  Include vec_qcp_strategy_proof.
  Include solver_qcp_support_proof_auto.
  Include solver_qcp_support_proof_manual.
End VC_Correctness.
