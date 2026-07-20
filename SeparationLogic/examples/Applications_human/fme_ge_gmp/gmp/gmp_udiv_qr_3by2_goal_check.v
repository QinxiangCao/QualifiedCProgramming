From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_udiv_qr_3by2_goal gmp_udiv_qr_3by2_proof_auto gmp_udiv_qr_3by2_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include gmp_udiv_qr_3by2_proof_auto.
  Include gmp_udiv_qr_3by2_proof_manual.
End VC_Correctness.
