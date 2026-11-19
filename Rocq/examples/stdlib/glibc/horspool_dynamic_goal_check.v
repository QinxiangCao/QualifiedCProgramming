From SimpleC.EE.stdlib.glibc Require Import horspool_dynamic_goal horspool_dynamic_proof_auto horspool_dynamic_proof_manual.

Module VC_Correctness : VC_Correct.
  Include horspool_dynamic_proof_auto.
  Include horspool_dynamic_proof_manual.
End VC_Correctness.
