From SimpleC.EE.LLM_bench.Data_structures.priority_queue_index Require Import priority_queue_index_goal priority_queue_index_proof_auto priority_queue_index_proof_manual.

Module VC_Correctness : VC_Correct.
  Include priority_queue_index_proof_auto.
  Include priority_queue_index_proof_manual.
End VC_Correctness.
