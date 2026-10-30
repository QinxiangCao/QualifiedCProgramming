From SimpleC.EE.QCP_demos_LLM Require Import GraphFieldOneRead3D_goal GraphFieldOneRead3D_proof_auto GraphFieldOneRead3D_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array3_strategy_proof.
  Include array2_strategy_proof.
  Include GraphFieldOneRead3D_proof_auto.
  Include GraphFieldOneRead3D_proof_manual.
End VC_Correctness.
