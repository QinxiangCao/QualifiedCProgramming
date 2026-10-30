From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_clz_goal gmp_clz_proof_auto gmp_clz_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include gmp_clz_proof_auto.
  Include gmp_clz_proof_manual.
End VC_Correctness.
