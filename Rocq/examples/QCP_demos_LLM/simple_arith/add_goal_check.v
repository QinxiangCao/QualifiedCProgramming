From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import add_goal add_proof_auto add_proof_manual.

Module VC_Correctness : VC_Correct.
  Include add_proof_auto.
  Include add_proof_manual.
End VC_Correctness.
