Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export SimpleC.StdLib.string_lib.

Local Open Scope Z_scope.
Import ListNotations.
Import naive_C_Rules.

Definition all_ascii (s: list Z): Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition no_inner_nul (s: list Z): Prop :=
  forall i, 0 <= i < Zlength s -> Znth i s 0 <> 0.

Definition valid_string (s: list Z): Prop :=
  all_ascii s /\ no_inner_nul s.

Definition c_string (s: list Z): list Z :=
  s ++ [0].

Definition string_length (s: list Z): Z :=
  Zlength s.

Definition store_string (p: Z) (s: list Z): Assertion :=
  CharArray.full p (string_length s + 1) (c_string s).
