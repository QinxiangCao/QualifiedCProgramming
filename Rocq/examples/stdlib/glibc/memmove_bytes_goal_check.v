Require Import SimpleC.EE.stdlib.glibc.memmove_bytes_goal.
Require Import SimpleC.EE.stdlib.glibc.memmove_bytes_proof_manual.
Module VC_Correctness : VC_Correct.
 Include memmove_bytes_proof_manual.
End VC_Correctness.
