From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P068_1416C_xor_inverse_goal P068_1416C_xor_inverse_proof_auto P068_1416C_xor_inverse_proof_manual.

Module VC_Correctness : VC_Correct.
  Include P068_1416C_xor_inverse_proof_auto.
  Include P068_1416C_xor_inverse_proof_manual.
End VC_Correctness.
