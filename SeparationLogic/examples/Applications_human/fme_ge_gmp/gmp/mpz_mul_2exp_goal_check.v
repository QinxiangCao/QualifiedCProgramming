From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_mul_2exp_goal mpz_mul_2exp_proof_auto mpz_mul_2exp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include mpz_mul_2exp_proof_auto.
  Include mpz_mul_2exp_proof_manual.
End VC_Correctness.
