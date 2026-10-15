From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P050_847H_load_testing_goal P050_847H_load_testing_proof_auto P050_847H_load_testing_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P050_847H_load_testing_proof_auto.
  Include P050_847H_load_testing_proof_manual.
End VC_Correctness.
