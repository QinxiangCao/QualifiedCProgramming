From SimpleC.EE.QCP_demos_human Require Import functional_queue_goal functional_queue_proof_auto functional_queue_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sll_strategy_proof.
  Include functional_queue_strategy_proof.
  Include functional_queue_proof_auto.
  Include functional_queue_proof_manual.
End VC_Correctness.
