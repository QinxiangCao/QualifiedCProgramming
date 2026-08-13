From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple5_goal swap_simple5_proof_auto swap_simple5_proof_manual.

Module VC_Correctness : VC_Correct.
  Include swap_simple5_strategy_proof.
  Include swap_simple5_proof_auto.
  Include swap_simple5_proof_manual.
End VC_Correctness.
