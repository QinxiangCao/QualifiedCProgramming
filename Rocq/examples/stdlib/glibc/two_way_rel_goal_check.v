From SimpleC.EE.stdlib.glibc Require Import two_way_rel_goal two_way_rel_proof_auto two_way_rel_proof_manual.

Module VC_Correctness : VC_Correct.
  Include two_way_rel_proof_auto.
  Include two_way_rel_proof_manual.
End VC_Correctness.
