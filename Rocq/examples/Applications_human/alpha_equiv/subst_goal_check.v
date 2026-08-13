From SimpleC.EE.Applications_human.alpha_equiv Require Import subst_goal subst_proof_auto subst_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexec_strategy_proof.
  Include subst_proof_auto.
  Include subst_proof_manual.
End VC_Correctness.
