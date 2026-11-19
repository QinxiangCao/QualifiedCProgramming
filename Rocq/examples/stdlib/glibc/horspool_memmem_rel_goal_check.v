From SimpleC.EE.stdlib.glibc Require Import horspool_memmem_rel_goal horspool_memmem_rel_proof_auto horspool_memmem_rel_proof_manual.

Module VC_Correctness : VC_Correct.
  Include horspool_memmem_rel_proof_auto.
  Include horspool_memmem_rel_proof_manual.
End VC_Correctness.
