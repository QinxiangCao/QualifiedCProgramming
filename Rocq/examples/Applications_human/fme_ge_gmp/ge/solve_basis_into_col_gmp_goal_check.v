From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import solve_basis_into_col_gmp_goal solve_basis_into_col_gmp_proof_auto solve_basis_into_col_gmp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include ge_gmp_array_strategy_proof.
  Include solve_basis_into_col_gmp_proof_auto.
  Include solve_basis_into_col_gmp_proof_manual.
End VC_Correctness.
