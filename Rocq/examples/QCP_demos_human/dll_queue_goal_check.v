From SimpleC.EE.QCP_demos_human Require Import dll_queue_goal dll_queue_proof_auto dll_queue_proof_manual.

Module VC_Correctness : VC_Correct.
  Include dll_queue_strategy_proof.
  Include dll_queue_proof_auto.
  Include dll_queue_proof_manual.
End VC_Correctness.
