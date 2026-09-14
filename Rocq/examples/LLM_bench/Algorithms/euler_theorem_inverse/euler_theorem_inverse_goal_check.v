From SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse Require Import euler_theorem_inverse_goal euler_theorem_inverse_proof_auto euler_theorem_inverse_proof_manual.

Module VC_Correctness : VC_Correct.
  Include euler_theorem_inverse_proof_auto.
  Include euler_theorem_inverse_proof_manual.
End VC_Correctness.
