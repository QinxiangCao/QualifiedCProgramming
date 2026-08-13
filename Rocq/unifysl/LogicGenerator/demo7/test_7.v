Require Import Morphisms.
Require Import export_lib_7.
Require Import SepApply_7.
Require Import SepCancel_7.
Require Import implementation_7.

Import EXPO.
Declare Scope syntax.
Open Scope syntax.
Notation "|--  x" := (provable x) (at level 71, no associativity) : syntax.
Notation "x --> y" := (impp x y) (at level 55, right associativity) : syntax.
Notation "x * y" := (SepCon x y) (at level 40, left associativity) : syntax.


Goal forall (PP: Prop) (P Q R S T: (nat -> option X) -> Prop), (PP -> |-- P * Q --> R) -> PP -> |-- P * S * Q * T --> T * S * R.
  intros.
  sep_apply H.
Abort.

Goal forall (PP: Prop) (P Q R S T: (nat -> option X) -> Prop), (PP -> |-- P * Q --> R) -> PP -> |-- P * S * Q * T --> T * S * R.
  intros.
  sep_cancel.
Abort.