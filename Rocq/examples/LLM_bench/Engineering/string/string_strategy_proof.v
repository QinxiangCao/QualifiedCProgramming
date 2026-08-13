Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.LLM_bench.Engineering.string Require Import string_strategy_goal.
From SimpleC.EE.LLM_bench.Engineering.string Require Import string_lib.
Import naive_C_Rules.

Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma string_strategy1_correctness : string_strategy1.
Proof.
  pre_process_default.
Qed.

Lemma string_strategy2_correctness : string_strategy2.
Proof.
  pre_process_default.
Qed.
