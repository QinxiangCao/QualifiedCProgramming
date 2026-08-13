(** This file and BourbakiWitt.v are based on a course project of Shanghai Jiao 
    Tong University, CS263 2020 spring, developed by Xinyi Wan and Zimeng Huang.
    Qinxiang Cao editted this file and add more theorems to it later. *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.RelationPairs.
Require Import SetsClass.SetsDomain.
Require Import FP.LiftConstructors.

Class Order (A: Type): Type :=
  order_rel: A -> A -> Prop.

Class Equiv (A: Type): Type :=
  equiv: A -> A -> Prop.

Declare Scope order_scope.
Notation "a <= b" := (order_rel a b): order_scope.
Notation "a == b" := (equiv a b): order_scope.
Local Open Scope order_scope.

Class AntiSymmetric_Setoid
        (A: Type) {RA: Order A} {EA: Equiv A}: Prop :=
  antisymmetricity_setoid: forall a b, a <= b -> b <= a -> a == b. 
(*反对称性*)

Class PartialOrder_Setoid
        (A: Type) {RA: Order A} {EA: Equiv A}: Prop :=
{
  PO_AntiSymmetric_Setoid: AntiSymmetric_Setoid A;
  PO_Reflexive_Setoid: forall x y, x == y -> x <= y;
  PO_Transitive: Transitive order_rel
}.
(*偏序关系*)

#[export] Existing Instances PO_AntiSymmetric_Setoid PO_Transitive.

#[export] Instance PartialOrder_Setoid_Reflexive:
  forall (A: Type) {RA: Order A} {EA: Equiv A},
    Equivalence equiv -> PartialOrder_Setoid A -> Reflexive order_rel.
Proof.
  intros.
  hnf; intros.
  apply PO_Reflexive_Setoid.
  reflexivity.
Qed.

#[export] Instance PartialOrder_Setoid_Proper:
  forall (A: Type) {RA: Order A} {EA: Equiv A},
    Equivalence equiv ->
    PartialOrder_Setoid A ->
    Proper (equiv ==> equiv ==> iff) order_rel.
Proof.
  unfold Proper, respectful.
  intros.
  split; intros.
  + transitivity x0; [| apply PO_Reflexive_Setoid; auto].
    transitivity x; [apply PO_Reflexive_Setoid; symmetry; auto |].
    auto.
  + transitivity y0; [| apply PO_Reflexive_Setoid; symmetry; auto].
    transitivity y; [apply PO_Reflexive_Setoid; auto |].
    auto.
Qed.

Definition fixpoint {A: Type} {EA: Equiv A} (f: A -> A) (a: A): Prop:=
  a == f a.
(* 函数f的不动点, R' 为等价关系*)

Definition least_fixpoint
             {A: Type} {RA: Order A} {EA: Equiv A} (f: A -> A) (a: A): Prop:=
  fixpoint f a /\ forall a', fixpoint f a' -> a <= a'.
(* 最小不动点 *)

Definition greatest_fixpoint
             {A: Type} {RA: Order A} {EA: Equiv A} (f: A -> A) (a: A): Prop:=
  fixpoint f a /\ forall a', fixpoint f a' -> a' <= a.
(* 最大不动点 *)

Lemma ProperR_ProperR'
        {A: Type} {RA: Order A} {EA: Equiv A}
        {Equ: Equivalence equiv} {PO: PartialOrder_Setoid A}:
  forall f,
    Proper (order_rel ==> order_rel) f ->
    Proper (equiv ==> equiv) f.
Proof.
  intros.
  hnf; intros.
  apply antisymmetricity_setoid.
  + apply H; rewrite H0; reflexivity.
  + apply H; rewrite H0; reflexivity.
Qed.

Module PO_sets.

#[export] Instance R_sets
           {T: Type}
           {_SETS: Sets.SETS T}: Order T :=
  Sets.included.

#[export] Instance Equiv_sets
           {T: Type}
           {_SETS: Sets.SETS T}: Equiv T :=
  Sets.equiv.

Ltac unfold_PO_defs :=
  unfold equiv, order_rel, R_sets, Equiv_sets.

#[export] Instance PO_sets
           {T: Type}
           {_SETS: Sets.SETS T}
           {_SETS_Properties: SETS_Properties T}: PartialOrder_Setoid T.
Proof.
  split.
  + unfold AntiSymmetric_Setoid.
    unfold_PO_defs.
    intros.
    apply Sets_equiv_Sets_included; tauto.
  + unfold_PO_defs.
    intros.
    rewrite H; reflexivity.
  + unfold Transitive.
    unfold_PO_defs.
    intros.
    rewrite H, H0.
    reflexivity.
Qed.

#[export] Instance Equiv_equiv_sets
           {T: Type}
           {_SETS: Sets.SETS T}
           {_SETS_Properties: SETS_Properties T}:
  Equivalence (@equiv T _).
Proof.
  apply Sets_equiv_equiv.
Qed.

Arguments R_sets: simpl never.
Arguments Equiv_sets: simpl never.

End PO_sets.

Module PO_lift.

Section PO_lift.

Context (A: Type) {B: Type} {RB: Order B} {EB: Equiv B}.

#[export] Instance R_lift: Order (A -> B) :=
  lift_rel2 order_rel.

#[export] Instance Equiv_lift: Equiv (A -> B) :=
  lift_rel2 equiv.

Ltac unfold_PO_defs :=
  unfold equiv, order_rel, R_lift, Equiv_lift, lift_rel2.

#[export] Instance PO_lift {POB: PartialOrder_Setoid B}:
  PartialOrder_Setoid (A -> B).
Proof.
  constructor.
  + hnf; unfold_PO_defs; intros.
    apply PO_AntiSymmetric_Setoid; auto.
  + unfold_PO_defs; intros.
    apply PO_Reflexive_Setoid; auto.
  + hnf; unfold_PO_defs; intros.
    eapply PO_Transitive; auto.
Qed.

#[export] Instance Equiv_equiv_lift {equB: Equivalence (@equiv B EB)}:
  Equivalence (@equiv (A -> B) Equiv_lift).
Proof.
  intros.
  apply pointwise_equivalence.
  auto.
Qed.

End PO_lift.

End PO_lift.

