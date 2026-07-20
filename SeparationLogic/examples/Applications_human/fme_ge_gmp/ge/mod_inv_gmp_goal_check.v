From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import mod_inv_gmp_goal mod_inv_gmp_proof_auto mod_inv_gmp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include ge_gmp_array_strategy_proof.
  Include mpz_tdiv_r_read0_strategy_proof.
  Include mod_inv_gmp_proof_auto.
  Include mod_inv_gmp_proof_manual.
End VC_Correctness.
