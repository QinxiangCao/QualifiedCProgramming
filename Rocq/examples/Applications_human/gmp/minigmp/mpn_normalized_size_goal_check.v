From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpn_normalized_size_goal mpn_normalized_size_proof_auto mpn_normalized_size_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include mpn_normalized_size_proof_auto.
  Include mpn_normalized_size_proof_manual.
End VC_Correctness.
