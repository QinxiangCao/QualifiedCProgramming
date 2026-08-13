From SimpleC.EE.QCP_demos_tutorial Require Import pos_int_pair_goal pos_int_pair_proof_auto pos_int_pair_proof_manual.

Module VC_Correctness : VC_Correct.
  Include pos_int_pair_strategy_proof.
  Include pos_int_pair_proof_auto.
  Include pos_int_pair_proof_manual.
End VC_Correctness.
