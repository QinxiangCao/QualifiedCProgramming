From SimpleC.EE.LLM_bench.Algorithms.Prim Require Import prim_forward_star_heap_goal prim_forward_star_heap_proof_auto prim_forward_star_heap_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include safeexec_strategy_proof.
  Include prim_forward_star_heap_proof_auto.
  Include prim_forward_star_heap_proof_manual.
End VC_Correctness.
