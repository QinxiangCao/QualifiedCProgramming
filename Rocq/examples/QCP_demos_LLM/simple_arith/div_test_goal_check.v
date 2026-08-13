From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import div_test_goal div_test_proof_auto div_test_proof_manual.

Module VC_Correctness : VC_Correct.
  Include div_test_proof_auto.
  Include div_test_proof_manual.
End VC_Correctness.
