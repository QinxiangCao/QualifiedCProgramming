From SimpleC.EE.QCP_demos_LLM Require Import two_d_int_ptr_array_goal two_d_int_ptr_array_proof_auto two_d_int_ptr_array_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_ptr_array2_strategy_proof.
  Include int_array_strategy_proof.
  Include two_d_int_ptr_array_proof_auto.
  Include two_d_int_ptr_array_proof_manual.
End VC_Correctness.
