Require Import SimpleC.EE.stdlib.glibc.memmove_loops_goal.
Require Import SimpleC.EE.stdlib.glibc.memmove_loops_proof_manual.
Module VC_Correctness : VC_Correct.
 Include memmove_loops_proof_manual.
End VC_Correctness.
