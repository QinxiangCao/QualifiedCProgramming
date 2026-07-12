From SimpleC.EE.QCP_demos_tutorial Require Import multiinv_examples_goal multiinv_examples_proof_auto multiinv_examples_proof_manual.

Module VC_Correctness : VC_Correct.
  Include multiinv_examples_proof_auto.
  Include multiinv_examples_proof_manual.
End VC_Correctness.
