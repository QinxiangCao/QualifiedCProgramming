From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import test_prime_goal test_prime_proof_auto test_prime_proof_manual.

Module VC_Correctness : VC_Correct.
  Include test_prime_proof_auto.
  Include test_prime_proof_manual.
End VC_Correctness.
