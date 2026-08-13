From SimpleC.EE.LLM_bench.Algorithms.paint_house_ii Require Import paint_house_ii_goal paint_house_ii_proof_auto paint_house_ii_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_ptr_array2_strategy_proof.
  Include int_array_strategy_proof.
  Include paint_house_ii_proof_auto.
  Include paint_house_ii_proof_manual.
End VC_Correctness.
