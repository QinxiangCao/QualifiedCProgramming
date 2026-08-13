From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_ui_sub_goal mpz_ui_sub_proof_auto mpz_ui_sub_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include mpz_ui_sub_proof_auto.
  Include mpz_ui_sub_proof_manual.
End VC_Correctness.
