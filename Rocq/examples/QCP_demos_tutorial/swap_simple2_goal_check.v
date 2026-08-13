From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple2_goal swap_simple2_proof_auto swap_simple2_proof_manual.

Module VC_Correctness : VC_Correct.
  Include swap_simple2_strategy_proof.
  Include swap_simple2_proof_auto.
  Include swap_simple2_proof_manual.
End VC_Correctness.
