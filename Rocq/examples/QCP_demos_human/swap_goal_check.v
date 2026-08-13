From SimpleC.EE.QCP_demos_human Require Import swap_goal swap_proof_auto swap_proof_manual.

Module VC_Correctness : VC_Correct.
  Include swap_proof_auto.
  Include swap_proof_manual.
End VC_Correctness.
