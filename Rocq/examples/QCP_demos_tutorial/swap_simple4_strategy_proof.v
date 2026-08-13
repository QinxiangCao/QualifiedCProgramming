Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_tutorial Require Import swap_simple4_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_tutorial.swap_simple1_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma swap_simple4_strategy0_correctness : swap_simple4_strategy0.
Proof.
  pre_process_default.
Qed.

Lemma swap_simple4_strategy1_correctness : swap_simple4_strategy1.
Proof.
  pre_process_default.
Qed.
