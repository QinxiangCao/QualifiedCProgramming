From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_add_ui_goal mpz_add_ui_proof_auto mpz_add_ui_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include mpz_add_ui_proof_auto.
  Include mpz_add_ui_proof_manual.
End VC_Correctness.
