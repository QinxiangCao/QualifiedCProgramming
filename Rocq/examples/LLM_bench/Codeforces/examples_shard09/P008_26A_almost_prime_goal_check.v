From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P008_26A_almost_prime_goal P008_26A_almost_prime_proof_auto P008_26A_almost_prime_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P008_26A_almost_prime_proof_auto.
  Include P008_26A_almost_prime_proof_manual.
End VC_Correctness.
