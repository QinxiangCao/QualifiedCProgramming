From SimpleC.EE.QCP_demos_LLM Require Import union_find_err_rel_goal union_find_err_rel_proof_auto union_find_err_rel_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include safeexecE_strategy_proof.
  Include union_find_err_rel_proof_auto.
  Include union_find_err_rel_proof_manual.
End VC_Correctness.
