From SimpleC.EE.QCP_demos_LLM Require Import three_d_graph_field_goal three_d_graph_field_proof_auto three_d_graph_field_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array3_strategy_proof.
  Include array2_strategy_proof.
  Include int_array_strategy_proof.
  Include three_d_graph_field_proof_auto.
  Include three_d_graph_field_proof_manual.
End VC_Correctness.
