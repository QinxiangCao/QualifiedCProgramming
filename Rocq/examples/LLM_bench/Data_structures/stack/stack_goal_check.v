From SimpleC.EE.LLM_bench.Data_structures.stack Require Import stack_goal stack_proof_auto stack_proof_manual.

Module VC_Correctness : VC_Correct.
  Include stack_proof_auto.
  Include stack_proof_manual.
End VC_Correctness.
