From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple3_goal swap_simple3_proof_auto swap_simple3_proof_manual.

Module VC_Correctness : VC_Correct.
  Include swap_simple3_strategy_proof.
  Include swap_simple3_proof_auto.
  Include swap_simple3_proof_manual.
End VC_Correctness.
