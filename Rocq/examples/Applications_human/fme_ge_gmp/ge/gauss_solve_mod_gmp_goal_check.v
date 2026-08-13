From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import gauss_solve_mod_gmp_goal gauss_solve_mod_gmp_proof_auto gauss_solve_mod_gmp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include ge_gmp_array_strategy_proof.
  Include gauss_solve_mod_gmp_proof_auto.
  Include gauss_solve_mod_gmp_proof_manual.
End VC_Correctness.
