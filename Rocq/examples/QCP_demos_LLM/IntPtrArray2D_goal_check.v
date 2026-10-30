From SimpleC.EE.QCP_demos_LLM Require Import IntPtrArray2D_goal IntPtrArray2D_proof_auto IntPtrArray2D_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_ptr_array2_strategy_proof.
  Include IntPtrArray2D_proof_auto.
  Include IntPtrArray2D_proof_manual.
End VC_Correctness.
