From SimpleC.EE.Applications_human.fme_ge_gmp.fme Require Import fme_gmp_goal fme_gmp_proof_auto fme_gmp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_optional_strategy_proof.
  Include fme_gmp_strategy_proof.
  Include safeexec_fme_gmp_strategy_proof.
  Include fme_gmp_proof_auto.
  Include fme_gmp_proof_manual.
End VC_Correctness.
