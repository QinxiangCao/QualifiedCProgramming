From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mrz_realloc_if_goal mrz_realloc_if_proof_auto mrz_realloc_if_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include mrz_realloc_if_proof_auto.
  Include mrz_realloc_if_proof_manual.
End VC_Correctness.
