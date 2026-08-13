Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.StdLib Require Import string_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma string_strategy1_correctness : string_strategy1.
  pre_process_default.
Qed.

Lemma string_strategy2_correctness : string_strategy2.
  pre_process_default.
Qed.
