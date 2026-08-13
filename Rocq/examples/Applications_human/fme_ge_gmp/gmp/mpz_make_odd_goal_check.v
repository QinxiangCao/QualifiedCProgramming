From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_make_odd_goal mpz_make_odd_proof_auto mpz_make_odd_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include mpz_make_odd_proof_auto.
  Include mpz_make_odd_proof_manual.
End VC_Correctness.
