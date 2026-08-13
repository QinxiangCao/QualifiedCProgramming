From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import col_swap_mod_gmp_goal col_swap_mod_gmp_proof_auto col_swap_mod_gmp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include ge_gmp_array_strategy_proof.
  Include col_swap_mod_gmp_proof_auto.
  Include col_swap_mod_gmp_proof_manual.
End VC_Correctness.
