From SimpleC.EE.Applications_human.alpha_equiv Require Import alpha_equiv_goal alpha_equiv_proof_auto alpha_equiv_proof_manual.

Module VC_Correctness : VC_Correct.
  Include safeexec_strategy_proof.
  Include alpha_equiv_proof_auto.
  Include alpha_equiv_proof_manual.
End VC_Correctness.
