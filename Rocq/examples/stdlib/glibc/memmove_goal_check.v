Require Import SimpleC.EE.stdlib.glibc.memmove_goal.
Require Import SimpleC.EE.stdlib.glibc.memmove_proof_manual.
Module VC_Correctness : memmove_goal.VC_Correct.
 Include memmove_proof_manual.
End VC_Correctness.
