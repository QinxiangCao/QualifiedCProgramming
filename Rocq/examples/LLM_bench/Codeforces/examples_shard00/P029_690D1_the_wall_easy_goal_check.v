From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P029_690D1_the_wall_easy_goal P029_690D1_the_wall_easy_proof_auto P029_690D1_the_wall_easy_proof_manual.

Module VC_Correctness : VC_Correct.
  Include array2_strategy_proof.
  Include array2_char_strategy_proof.
  Include array2_ext_strategy_proof.
  Include P029_690D1_the_wall_easy_proof_auto.
  Include P029_690D1_the_wall_easy_proof_manual.
End VC_Correctness.
