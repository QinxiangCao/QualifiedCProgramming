From SimpleC.EE.stdlib.glibc Require Import strlen_word_goal strlen_word_proof_auto strlen_word_proof_manual.

Module VC_Correctness : VC_Correct.
  Include strlen_word_proof_auto.
  Include strlen_word_proof_manual.
End VC_Correctness.
