From SimpleC.EE.QCP_demos_human.simple_arith Require Import add_goal add_proof_auto add_proof_manual.

Module VC_Correctness : VC_Correct.
  Include add_proof_auto.
  Include add_proof_manual.
End VC_Correctness.
