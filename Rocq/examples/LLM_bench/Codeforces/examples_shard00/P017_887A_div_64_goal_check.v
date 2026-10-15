From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P017_887A_div_64_goal P017_887A_div_64_proof_auto P017_887A_div_64_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P017_887A_div_64_proof_auto.
  Include P017_887A_div_64_proof_manual.
End VC_Correctness.
