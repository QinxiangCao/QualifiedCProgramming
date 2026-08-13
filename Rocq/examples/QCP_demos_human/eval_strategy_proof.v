Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_human Require Import eval_strategy_goal.
Import naive_C_Rules.

From SimpleC.EE.QCP_demos_human Require Import eval_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma eval_strategy0_correctness : eval_strategy0.
  pre_process_default.
  Intros; subst.
  entailer!.
Qed.

Lemma eval_strategy1_correctness : eval_strategy1.
  pre_process_default.
  Intros; subst.
  entailer!.
Qed.
