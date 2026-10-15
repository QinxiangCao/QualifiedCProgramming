From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P010_48A_rock_paper_scissors_goal P010_48A_rock_paper_scissors_proof_auto P010_48A_rock_paper_scissors_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include array2_strategy_proof.
  Include array2_char_strategy_proof.
  Include int_array_strategy_proof.
  Include array2_ext_strategy_proof.
  Include P010_48A_rock_paper_scissors_proof_auto.
  Include P010_48A_rock_paper_scissors_proof_manual.
End VC_Correctness.
