From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_divexact_goal mpz_divexact_proof_auto mpz_divexact_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include mpz_divexact_proof_auto.
  Include mpz_divexact_proof_manual.
End VC_Correctness.
