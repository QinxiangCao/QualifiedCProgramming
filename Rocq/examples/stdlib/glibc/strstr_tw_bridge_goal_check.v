(* All five obligations, including QCP's two automatic cases, are Rocq proved. *)
From SimpleC.EE.stdlib.glibc Require Import strstr_tw_bridge_goal strstr_tw_bridge_proof_manual.
Module VC_Correctness : VC_Correct.
  Include strstr_tw_bridge_proof_manual.
End VC_Correctness.
