From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import build_inverse_cols_gmp_goal build_inverse_cols_gmp_proof_auto build_inverse_cols_gmp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include ge_gmp_array_strategy_proof.
  Include build_inverse_cols_gmp_proof_auto.
  Include build_inverse_cols_gmp_proof_manual.
End VC_Correctness.
