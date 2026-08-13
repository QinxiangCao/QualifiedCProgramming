From SimpleC.EE.Applications_human.minigmp_sumlib Require Import gmp_goal gmp_proof_auto gmp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include gmp_strategy_proof.
  Include gmp_proof_auto.
  Include gmp_proof_manual.
End VC_Correctness.
