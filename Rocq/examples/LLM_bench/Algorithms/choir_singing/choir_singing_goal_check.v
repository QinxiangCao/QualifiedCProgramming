From SimpleC.EE.LLM_bench.Algorithms.choir_singing Require Import choir_singing_goal choir_singing_proof_auto choir_singing_proof_manual.

Module VC_Correctness : VC_Correct.
  Include choir_singing_proof_auto.
  Include choir_singing_proof_manual.
End VC_Correctness.
