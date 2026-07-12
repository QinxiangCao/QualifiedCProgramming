From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import delta_goal delta_proof_auto delta_proof_manual.

Module VC_Correctness : VC_Correct.
  Include delta_proof_auto.
  Include delta_proof_manual.
End VC_Correctness.
