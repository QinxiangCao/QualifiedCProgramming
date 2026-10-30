From SimpleC.EE.Applications_human.typeinfer_rc Require Import typeinfer_rc_goal typeinfer_rc_proof_auto typeinfer_rc_proof_manual.

Module VC_Correctness : VC_Correct.
  Include typeinfer_rc_strategy_proof.
  Include typeinfer_rc_proof_auto.
  Include typeinfer_rc_proof_manual.
End VC_Correctness.
