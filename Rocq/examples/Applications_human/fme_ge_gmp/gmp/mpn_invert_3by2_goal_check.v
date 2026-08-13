From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_invert_3by2_goal mpn_invert_3by2_proof_auto mpn_invert_3by2_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include mpn_invert_3by2_proof_auto.
  Include mpn_invert_3by2_proof_manual.
End VC_Correctness.
