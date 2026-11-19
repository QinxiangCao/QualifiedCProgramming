From SimpleC.EE.stdlib.musl Require Import strstr_rel_goal strstr_rel_proof_auto strstr_rel_proof_manual.

Module VC_Correctness : VC_Correct.
  Include strstr_rel_cleanup_strategy_proof.
  Include strstr_rel_proof_auto.
  Include strstr_rel_proof_manual.
End VC_Correctness.
