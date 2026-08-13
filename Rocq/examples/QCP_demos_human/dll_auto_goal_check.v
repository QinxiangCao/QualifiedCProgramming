From SimpleC.EE.QCP_demos_human Require Import dll_auto_goal dll_auto_proof_auto dll_auto_proof_manual.

Module VC_Correctness : VC_Correct.
  Include dll_shape_strategy_proof.
  Include dll_auto_proof_auto.
  Include dll_auto_proof_manual.
End VC_Correctness.
