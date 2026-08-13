From SimpleC.EE.Applications_human.mergeablelist Require Import sll_project_goal sll_project_proof_auto sll_project_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sll_project_strategy_proof.
  Include sll_project_proof_auto.
  Include sll_project_proof_manual.
End VC_Correctness.
