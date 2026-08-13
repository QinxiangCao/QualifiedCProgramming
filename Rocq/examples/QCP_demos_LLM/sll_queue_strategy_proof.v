Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import sll_queue_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
From SimpleC.EE.QCP_demos_LLM Require Import sll_queue_lib.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma sll_queue_strategy0_correctness : sll_queue_strategy0.
Proof.
  pre_process_default.
  Intros_p H.
  subst l1.
  cancel.
Qed.

Lemma sll_queue_strategy1_correctness : sll_queue_strategy1.
Proof.
  pre_process_default.
  Intros_p H.
  Intros_p H0.
  subst x2 l2.
  split_pure_spatial.
  2: {
    dump_pre_spatial.
    reflexivity.
  }
  cancel.
Qed.
