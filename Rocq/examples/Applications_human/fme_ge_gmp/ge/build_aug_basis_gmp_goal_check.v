From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import build_aug_basis_gmp_goal build_aug_basis_gmp_proof_auto build_aug_basis_gmp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include ge_gmp_array_strategy_proof.
  Include build_aug_basis_gmp_proof_auto.
  Include build_aug_basis_gmp_proof_manual.
End VC_Correctness.
