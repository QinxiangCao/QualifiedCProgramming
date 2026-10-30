From SimpleC.EE.Applications_human.hash_table Require Import hash_table_goal hash_table_proof_auto hash_table_proof_manual.

Module VC_Correctness : VC_Correct.
  Include hash_table_proof_auto.
  Include hash_table_proof_manual.
End VC_Correctness.
