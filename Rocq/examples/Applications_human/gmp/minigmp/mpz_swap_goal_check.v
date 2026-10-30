From SimpleC.EE.Applications_human.gmp.minigmp Require Import mpz_swap_goal mpz_swap_proof_auto mpz_swap_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include mpz_swap_proof_auto.
  Include mpz_swap_proof_manual.
End VC_Correctness.
