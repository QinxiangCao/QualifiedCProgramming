(* COLLECTOR - do not add lemmas here; they belong in the part files.  The nine
   solver_qcp_proof_manual_partN.v files are the source of truth - edit them directly.

   The build layers, in dependency order, are

     solver_qcp_lib.v -> solver_qcp_goal.v -> solver_qcp_proof_auto.v
       -> solver_qcp_proof_common.v -> solver_qcp_proof_manual_part1..9.v
       -> this collector

   Parts are mutually independent: each Requires only those four files below it and
   never another part, so shared proof content goes to solver_qcp_proof_common.v when
   only the parts consume it and to solver_qcp_lib.v when the library does too.  That
   independence is what lets the nine parts build in parallel.

   Some verification conditions in solver_qcp_goal.v have identical statement text
   under different names: the symbolic executor emits one VC per syntactic obligation,
   and two obligations arising at different program points can be the same proposition.
   Such a duplicate is proved once and the other name is discharged by a one-line stub,
     Lemma proof_of_<stub> : <stub>.  Proof. exact proof_of_<keeper>. Qed.
   which closes the goal by delta-conversion, both names being transparent Definitions
   with the same body.  A stub always sits in the SAME part as its keeper, with the
   keeper appearing earlier in that file; a cross-part reference would serialise the
   parallel build.

   solver_qcp_goal_check.v ascribes the full VC module (Module VC_Correctness :
   VC_Correct), so a missing or misnamed proof fails the kernel's ascription check. *)
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_proof_manual_part1.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_proof_manual_part2.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_proof_manual_part3.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_proof_manual_part4.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_proof_manual_part5.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_proof_manual_part6.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_proof_manual_part7.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_proof_manual_part8.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_proof_manual_part9.

Include solver_qcp_proof_manual_part1.
Include solver_qcp_proof_manual_part2.
Include solver_qcp_proof_manual_part3.
Include solver_qcp_proof_manual_part4.
Include solver_qcp_proof_manual_part5.
Include solver_qcp_proof_manual_part6.
Include solver_qcp_proof_manual_part7.
Include solver_qcp_proof_manual_part8.
Include solver_qcp_proof_manual_part9.
