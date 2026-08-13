From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import gcd_goal gcd_proof_auto gcd_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gcd_proof_auto.
  Include gcd_proof_manual.
End VC_Correctness.
