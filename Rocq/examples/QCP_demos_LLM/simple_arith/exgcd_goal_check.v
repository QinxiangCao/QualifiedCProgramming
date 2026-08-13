From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import exgcd_goal exgcd_proof_auto exgcd_proof_manual.

Module VC_Correctness : VC_Correct.
  Include exgcd_proof_auto.
  Include exgcd_proof_manual.
End VC_Correctness.
