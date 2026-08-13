From SimpleC.EE.Applications_human.convex_hull Require Import graham_scan_goal graham_scan_proof_auto graham_scan_proof_manual.

Module VC_Correctness : VC_Correct.
  Include point_array_strategy_proof.
  Include safeexec_strategy_proof.
  Include graham_scan_proof_auto.
  Include graham_scan_proof_manual.
End VC_Correctness.
