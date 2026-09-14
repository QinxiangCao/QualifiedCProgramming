From SimpleC.EE.LLM_bench.Algorithms.lcs_n Require Import lcs_n_goal lcs_n_proof_auto lcs_n_proof_manual.

Module VC_Correctness : VC_Correct.
  Include lcs_n_proof_auto.
  Include lcs_n_proof_manual.
End VC_Correctness.
