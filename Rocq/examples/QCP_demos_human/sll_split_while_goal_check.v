From SimpleC.EE.QCP_demos_human Require Import sll_split_while_goal sll_split_while_proof_auto sll_split_while_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sll_strategy_proof.
  Include safeexec_strategy_proof.
  Include sll_split_while_proof_auto.
  Include sll_split_while_proof_manual.
End VC_Correctness.
