From SimpleC.EE.QCP_demos_LLM Require Import bubble_sort_goal bubble_sort_proof_auto bubble_sort_proof_manual.

Module VC_Correctness : VC_Correct.
  Include bubble_sort_proof_auto.
  Include bubble_sort_proof_manual.
End VC_Correctness.
