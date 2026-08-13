From SimpleC.EE.LLM_bench.Algorithms.choosing_inns Require Import choosing_inns_goal choosing_inns_proof_auto choosing_inns_proof_manual.

Module VC_Correctness : VC_Correct.
  Include choosing_inns_proof_auto.
  Include choosing_inns_proof_manual.
End VC_Correctness.
