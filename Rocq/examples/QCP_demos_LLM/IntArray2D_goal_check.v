From SimpleC.EE.QCP_demos_LLM Require Import IntArray2D_goal IntArray2D_proof_auto IntArray2D_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array2_strategy_proof.
  Include IntArray2D_proof_auto.
  Include IntArray2D_proof_manual.
End VC_Correctness.
