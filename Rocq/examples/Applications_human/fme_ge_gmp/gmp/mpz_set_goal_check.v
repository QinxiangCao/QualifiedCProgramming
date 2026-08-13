From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_set_goal mpz_set_proof_auto mpz_set_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include mpz_set_proof_auto.
  Include mpz_set_proof_manual.
End VC_Correctness.
