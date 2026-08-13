From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_goal CDCL_qcp_proof_auto CDCL_qcp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include int_ptr_array2_strategy_proof.
  Include CDCL_qcp_strategy_proof.
  Include CDCL_qcp_proof_auto.
  Include CDCL_qcp_proof_manual.
End VC_Correctness.
