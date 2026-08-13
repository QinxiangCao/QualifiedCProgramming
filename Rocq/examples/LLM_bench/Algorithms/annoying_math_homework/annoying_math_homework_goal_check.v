From SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework Require Import annoying_math_homework_goal annoying_math_homework_proof_auto annoying_math_homework_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include annoying_math_homework_proof_auto.
  Include annoying_math_homework_proof_manual.
End VC_Correctness.
