From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import copy_vector_to_col_gmp_goal copy_vector_to_col_gmp_proof_auto copy_vector_to_col_gmp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include ge_gmp_array_strategy_proof.
  Include copy_vector_to_col_gmp_proof_auto.
  Include copy_vector_to_col_gmp_proof_manual.
End VC_Correctness.
