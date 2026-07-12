From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple1_goal swap_simple1_proof_auto swap_simple1_proof_manual.

Module VC_Correctness : VC_Correct.
  Include swap_simple1_proof_auto.
  Include swap_simple1_proof_manual.
End VC_Correctness.
