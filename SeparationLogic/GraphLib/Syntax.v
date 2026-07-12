Require Import Coq.Logic.Classical.
Require Import Relations.
Require Import SetsClass.SetsClass.

Ltac destruct_equality_impl x y :=
  let Heq := fresh "eq_" x y in
  let Hneq := fresh "neq_" x y in
  let Hdisj := fresh "Disj_" x y in
  assert (x = y \/ x <> y) as Hdisj;
  [ apply classic
  | destruct Hdisj as [ Heq | Hneq ];
    subst;
    auto
  ].

Tactic Notation "destruct_equality" uconstr(x) uconstr(y) :=
  destruct_equality_impl x y.
  
