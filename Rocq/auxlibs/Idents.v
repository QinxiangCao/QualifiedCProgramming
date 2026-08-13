Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.


Definition ident := positive.

Definition ident_eq_dec : forall x y : ident, {x = y} + {x <> y} := Pos.eq_dec.
Definition ident_eqb (x y : ident) : bool := Pos.eqb x y.
Definition ident_eqb_refl : forall x, ident_eqb x x = true := Pos.eqb_refl.
Definition ident_eqb_eq : forall x y, ident_eqb x y = true <-> x = y := Pos.eqb_eq.


Definition var : Type := positive.
Definition func : Type := positive.

Definition var_eqb : var -> var -> bool := Pos.eqb.
Definition func_eqb : func -> func -> bool := Pos.eqb.

Definition var_dec : forall (x y : var), {x = y} + {x <> y} := Pos.eq_dec.
Definition func_dec : forall (x y : var), {x = y} + {x <> y} := Pos.eq_dec.

Definition var_eqb_eq : forall x y,
  var_eqb x y = true <-> x = y := Pos.eqb_eq.
Definition var_eqb_neq : forall x y,
  var_eqb x y = false <-> x <> y := Pos.eqb_neq.
Definition func_eqb_eq : forall f1 f2,
  func_eqb f1 f2 = true <-> f1 = f2 := Pos.eqb_eq.
Definition func_eqb_neq : forall f1 f2,
  func_eqb f1 f2 = false <-> f1 <> f2 := Pos.eqb_neq.

Definition var_eqb_refl : forall x,
  var_eqb x x = true := Pos.eqb_refl.
Definition func_eqb_refl : forall f,
  func_eqb f f = true := Pos.eqb_refl.

Ltac var_destruct x y :=
  let H := fresh "E" in
  destruct (var_eqb x y) eqn:H;
  [apply var_eqb_eq in H | apply var_eqb_neq in H].
