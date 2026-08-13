Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import eval_strategy_goal.
Import naive_C_Rules.

From SimpleC.EE.QCP_demos_LLM Require Import eval_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma eval_strategy0_correctness : eval_strategy0.
Proof.
  pre_process_default.
  Intros_p H.
  subst l1.
  cancel.
Qed.

Lemma eval_strategy1_correctness : eval_strategy1.
Proof.
  pre_process_default.
  Intros_p H.
  Intros_p H0.
  subst q1 l1.
  cancel.
Qed.
