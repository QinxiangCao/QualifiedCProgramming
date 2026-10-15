From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P022_705B_spider_man_goal P022_705B_spider_man_proof_auto P022_705B_spider_man_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P022_705B_spider_man_proof_auto.
  Include P022_705B_spider_man_proof_manual.
End VC_Correctness.
