From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_lshift_goal mpn_lshift_proof_auto mpn_lshift_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include mpn_lshift_proof_auto.
  Include mpn_lshift_proof_manual.
End VC_Correctness.
