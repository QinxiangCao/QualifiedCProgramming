(* Split manual proof wrapper.  Proof bodies live in the part files.
   [Include] re-exports their lemmas as fields of this compilation unit, which
   is what [CDCL_qcp_goal_check] checks with [Include CDCL_qcp_proof_manual]. *)
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_proof_manual_part1.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_proof_manual_part2.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_proof_manual_part3.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_proof_manual_part4.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_proof_manual_part5.
From SimpleC.EE.Applications_human.CDCL Require Import CDCL_qcp_proof_manual_part6.

Include CDCL_qcp_proof_manual_part1.
Include CDCL_qcp_proof_manual_part2.
Include CDCL_qcp_proof_manual_part3.
Include CDCL_qcp_proof_manual_part4.
Include CDCL_qcp_proof_manual_part5.
Include CDCL_qcp_proof_manual_part6.
