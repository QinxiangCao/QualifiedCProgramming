From SimpleC.EE.QCP_demos_LLM Require Import GraphField3D_goal GraphField3D_proof_auto GraphField3D_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array3_strategy_proof.
  Include array2_strategy_proof.
  Include GraphField3D_proof_auto.
  Include GraphField3D_proof_manual.
End VC_Correctness.
