Require Import Morphisms.
Require Import HypotheticalExternLib.
Require Import export_lib_6.
Require Import SepApply_6.
Require Import SepCancel_6.
Require Import implementation_6.

Import EXPO.
Declare Scope syntax.
Open Scope syntax.
Notation "|--  x" := (provable x) (at level 71, no associativity) : syntax.
Notation "x --> y" := (impp x y) (at level 55, right associativity) : syntax.
Notation "x * y" := (SepCon x y) (at level 40, left associativity) : syntax.

Parameter p: para.
Existing Instance p.

Goal forall (PP: Prop) (P Q R S T: (nat -> option X) -> Prop), (PP -> |-- P * Q --> R) -> PP -> |-- P * S * Q * T --> T * S * R.
  intros.
  sep_apply H.
Abort.

Goal forall (PP: Prop) (P Q R S T: (nat -> option X) -> Prop), (PP -> |-- P * Q --> R) -> PP -> |-- P * S * Q * T --> T * S * R.
  intros.
  sep_cancel.
Abort.