From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P070_509E_pretty_song_goal P070_509E_pretty_song_proof_auto P070_509E_pretty_song_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P070_509E_pretty_song_proof_auto.
  Include P070_509E_pretty_song_proof_manual.
End VC_Correctness.
