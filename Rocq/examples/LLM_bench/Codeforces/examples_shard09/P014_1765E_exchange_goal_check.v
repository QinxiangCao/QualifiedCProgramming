From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P014_1765E_exchange_goal P014_1765E_exchange_proof_auto P014_1765E_exchange_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P014_1765E_exchange_proof_auto.
  Include P014_1765E_exchange_proof_manual.
End VC_Correctness.
