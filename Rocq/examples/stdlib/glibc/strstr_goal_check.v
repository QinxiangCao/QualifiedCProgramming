From SimpleC.EE.stdlib.glibc Require Import strstr_goal strstr_proof_auto strstr_proof_manual.

Module VC_Correctness : VC_Correct.
  Include strstr_proof_auto.
  Include strstr_proof_manual.
End VC_Correctness.
