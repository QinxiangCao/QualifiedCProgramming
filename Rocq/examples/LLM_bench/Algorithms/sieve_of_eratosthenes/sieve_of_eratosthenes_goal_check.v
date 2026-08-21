From SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes Require Import sieve_of_eratosthenes_goal sieve_of_eratosthenes_proof_auto sieve_of_eratosthenes_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sieve_of_eratosthenes_proof_auto.
  Include sieve_of_eratosthenes_proof_manual.
End VC_Correctness.
