From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.cnf_trans Require Import cnf_trans_goal.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.cnf_trans Require Import smt_lang_lib.
From SimpleC.EE.Applications_human.cnf_trans Require Import cnf_trans_lib.
From SimpleC.EE.Applications_human Require Import malloc.
From SimpleC.EE.Applications_human Require Import super_poly_sll2.
Local Open Scope sac.

From SimpleC.EE.Applications_human.cnf_trans Require Import cnf_trans_proof_manual1 cnf_trans_proof_manual2 cnf_trans_proof_manual3.

Include cnf_trans_proof_manual1.
Include cnf_trans_proof_manual2.
Include cnf_trans_proof_manual3.