From SimpleC.EE.QCP_demos_LLM Require Import CharPtrArray2D_goal CharPtrArray2D_proof_auto CharPtrArray2D_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include CharPtrArray2D_proof_auto.
  Include CharPtrArray2D_proof_manual.
End VC_Correctness.
