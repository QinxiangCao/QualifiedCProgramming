From SimpleC.EE.LLM_bench.Engineering.minisat Require Import vec_goal vec_proof_auto vec_proof_manual.

Module VC_Correctness : VC_Correct.
  Include vec_proof_auto.
  Include vec_proof_manual.
End VC_Correctness.
