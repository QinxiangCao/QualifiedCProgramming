Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_human Require Import functional_queue_strategy_goal.
From SimpleC.EE.QCP_demos_human Require Import sll_lib.
From SimpleC.EE.QCP_demos_human Require Import functional_queue_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma functional_queue_strategy0_correctness : functional_queue_strategy0.
  pre_process_default.
  Intros; subst; entailer!.
Qed.

Lemma functional_queue_strategy1_correctness : functional_queue_strategy1.
  pre_process_default.
  Intros; subst; entailer!.
Qed.
