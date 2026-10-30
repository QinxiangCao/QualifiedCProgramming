From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_div_qr_goal mpz_div_qr_proof_auto mpz_div_qr_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include mpz_div_qr_strategy_proof.
  Include mpz_tdiv_r_read0_strategy_proof.
  Include mpz_div_qr_proof_auto.
  Include mpz_div_qr_proof_manual.
End VC_Correctness.
