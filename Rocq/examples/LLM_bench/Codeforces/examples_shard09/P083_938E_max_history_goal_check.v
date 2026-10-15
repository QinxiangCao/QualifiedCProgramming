From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P083_938E_max_history_goal P083_938E_max_history_proof_auto P083_938E_max_history_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P083_938E_max_history_proof_auto.
  Include P083_938E_max_history_proof_manual.
End VC_Correctness.
