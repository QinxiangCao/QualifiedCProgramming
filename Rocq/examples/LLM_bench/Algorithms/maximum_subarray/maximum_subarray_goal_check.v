From SimpleC.EE.LLM_bench.Algorithms.maximum_subarray Require Import maximum_subarray_goal maximum_subarray_proof_auto maximum_subarray_proof_manual.

Module VC_Correctness : VC_Correct.
  Include maximum_subarray_proof_auto.
  Include maximum_subarray_proof_manual.
End VC_Correctness.
