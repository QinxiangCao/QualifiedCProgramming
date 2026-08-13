Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_human Require Import bst_strategy_goal.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_human Require Import sll_lib.
From SimpleC.EE.QCP_demos_human Require Import bst_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma bst_strategy0_correctness : bst_strategy0.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma bst_strategy1_correctness : bst_strategy1.
  pre_process_default.
  Intros; subst; simpl; entailer!.
Qed.

Lemma bst_strategy2_correctness : bst_strategy2.
  pre_process_default.
  Intros; subst; entailer!.
Qed. 

Lemma bst_strategy5_correctness : bst_strategy5.
  pre_process_default.
  Intros; subst; entailer!.
Qed. 

Lemma bst_strategy4_correctness : bst_strategy4.
  pre_process_default.
  Intros; subst; entailer!.
  simpl. entailer!.
Qed.
