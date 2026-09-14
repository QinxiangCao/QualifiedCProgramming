From SimpleC.EE.LLM_bench.Algorithms.huffman_encoding Require Import huffman_encoding_goal huffman_encoding_proof_auto huffman_encoding_proof_manual.

Module VC_Correctness : VC_Correct.
  Include huffman_encoding_proof_auto.
  Include huffman_encoding_proof_manual.
End VC_Correctness.
