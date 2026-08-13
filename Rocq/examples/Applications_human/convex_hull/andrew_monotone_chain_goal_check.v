From SimpleC.EE.Applications_human.convex_hull Require Import andrew_monotone_chain_goal andrew_monotone_chain_proof_auto andrew_monotone_chain_proof_manual.

Module VC_Correctness : VC_Correct.
  Include point_array_strategy_proof.
  Include safeexec_strategy_proof.
  Include andrew_monotone_chain_proof_auto.
  Include andrew_monotone_chain_proof_manual.
End VC_Correctness.
