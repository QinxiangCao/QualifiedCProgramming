From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_gcd_goal mpz_gcd_proof_auto mpz_gcd_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include mpz_tdiv_r_read0_strategy_proof.
  Include mpz_gcd_proof_auto.
  Include mpz_gcd_proof_manual.
End VC_Correctness.
