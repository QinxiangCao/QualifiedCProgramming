From SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler Require Import sieve_of_euler_goal sieve_of_euler_proof_auto sieve_of_euler_proof_manual.

Module VC_Correctness : VC_Correct.
  Include sieve_of_euler_proof_auto.
  Include sieve_of_euler_proof_manual.
End VC_Correctness.
