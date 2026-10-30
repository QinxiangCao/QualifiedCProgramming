From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P064_1992F_valuable_cards_goal P064_1992F_valuable_cards_proof_auto P064_1992F_valuable_cards_proof_manual.

Module VC_Correctness : VC_Correct.
  Include string_strategy_proof.
  Include P064_1992F_valuable_cards_proof_auto.
  Include P064_1992F_valuable_cards_proof_manual.
End VC_Correctness.
