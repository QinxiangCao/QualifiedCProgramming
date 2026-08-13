From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_div_qr_goal mpz_div_qr_proof_auto mpz_div_qr_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include mpz_div_qr_strategy_proof.
  Include mpz_div_qr_proof_auto.
  Include mpz_div_qr_proof_manual.
End VC_Correctness.
