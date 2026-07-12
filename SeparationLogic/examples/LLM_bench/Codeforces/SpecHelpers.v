Require Export Coq.ZArith.ZArith.
Require Export Coq.Lists.List.
Require Export Coq.Reals.Reals.
Require Export Coq.Logic.ClassicalEpsilon.
Require Export SetsClass.SetsClass.
Require Export ListLib.Base.Inductive.
Require Export ListLib.Base.Positional.
Require Export ListLib.General.Length.
Require Export MaxMinLib.MaxMin.
Require Export MaxMinLib.Interface.
Require Export SumLib.Sum.
Require Export SumLib.ZRange.
Require Export SumLib.FiniteExtra.
Require Export AUXLib.MonotonicList.

Local Open Scope Z_scope.

(** Cardinality of a finite predicate-set, implemented as summing [1].
    This is the meaning of the [# P] notation below. *)
Definition set_card {A : Type} (P : A -> Prop) `{Finite A P} : Z :=
  @sum A P _ (fun _ => 1).

(** Inclusive integer range sum: [sum_range a b f] computes
    [f a + ... + f b].   *)
Definition sum_range (a b : Z) (f : Z -> Z) : Z :=
  @sum Z (fun i => a <= i < b + 1) _ f.

(** Inclusive integer range sum for real-valued terms. *)
Definition sum_range_R (a b : Z) (f : Z -> R) : R :=
  fold_right Rplus 0%R (map f (Zrange a (b + 1))).

(** Finite-set sum for real-valued terms, using the [Finite] enumeration. *)
Definition sum_set_R {A : Type} (P : A -> Prop) `{Finite A P} (f : A -> R) : R :=
  fold_right Rplus 0%R (map f (@enum A P _)).

(** Short notation for finite-set cardinality. *)
Notation "# x" := (set_card x) (at level 35, only parsing).

