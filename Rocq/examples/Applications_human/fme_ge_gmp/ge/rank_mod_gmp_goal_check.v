From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import rank_mod_gmp_goal rank_mod_gmp_proof_auto rank_mod_gmp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include ge_gmp_array_strategy_proof.
  Include rank_mod_gmp_proof_auto.
  Include rank_mod_gmp_proof_manual.
End VC_Correctness.
