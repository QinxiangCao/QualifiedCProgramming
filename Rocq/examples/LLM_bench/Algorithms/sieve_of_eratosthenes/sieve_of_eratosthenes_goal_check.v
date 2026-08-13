From SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes Require Import sieve_of_eratosthenes_goal sieve_of_eratosthenes_proof_auto sieve_of_eratosthenes_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include sieve_of_eratosthenes_proof_auto.
  Include sieve_of_eratosthenes_proof_manual.
End VC_Correctness.
