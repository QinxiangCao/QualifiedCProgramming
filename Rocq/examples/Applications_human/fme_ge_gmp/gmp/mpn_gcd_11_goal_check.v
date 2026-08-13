From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_gcd_11_goal mpn_gcd_11_proof_auto mpn_gcd_11_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include mpn_gcd_11_proof_auto.
  Include mpn_gcd_11_proof_manual.
End VC_Correctness.
