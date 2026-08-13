Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Logic.Classical_Prop.
Require Import SetsClass.SetElement.
Require Import SetsClass.SetsDomain.

Class SETS_Classical_Properties (T: Type) {_SETS: Sets.SETS T}: Prop :=
{
  Sets_union_complement_self:
    forall x, Sets.equiv (Sets.union x (Sets.complement x)) Sets.full;
}.

#[export] Instance Prop_SETS_Classical_Properties: SETS_Classical_Properties Prop.
Proof.
  constructor; unfold_SETS_in_goal_tac; simpl.
  hnf; intros; try tauto.
Qed.

#[export] Instance lift_SETS_Classical_Properties (A B: Type) (_SETS: Sets.SETS B) (_SETS_Classical_Properties: SETS_Classical_Properties B): SETS_Classical_Properties (A -> B).
Proof.
  constructor; unfold_SETS_in_goal_tac; hnf; intros.
  apply Sets_union_complement_self.
Qed.

Lemma Sets_complement_self_union {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T} {_SETS_Classical_Properties: SETS_Classical_Properties T}:
  forall x, Sets.equiv (Sets.union (Sets.complement x) x) Sets.full.
Proof.
  intros.
  rewrite Sets_union_comm.
  apply Sets_union_complement_self.
Qed.

Lemma Sets_contrapositive_CC {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T} {_SETS_Classical_Properties: SETS_Classical_Properties T}:
  forall x y,
    Sets.included (Sets.complement y) (Sets.complement x) ->
    Sets.included x y.
Proof.
  intros.
  rewrite <- (Sets_intersect_full x).
  rewrite <- (Sets_union_complement_self y).
  rewrite Sets_intersect_union_distr_l.
  apply Sets_union_included.
  + apply Sets_intersect_included2.
  + rewrite H.
    rewrite Sets_intersect_complement_self.
    apply Sets_empty_included.
Qed.

Lemma Sets_contrapositive_CP {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T} {_SETS_Classical_Properties: SETS_Classical_Properties T}:
  forall x y,
    Sets.included (Sets.complement x) y ->
    Sets.included (Sets.complement y) x.
Proof.
  intros.
  apply Sets_contrapositive_CC.
  rewrite H.
  apply Sets_included_double_complement.
Qed.

Lemma Sets_complement_complement {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T} {_SETS_Classical_Properties: SETS_Classical_Properties T}:
  forall x,
    Sets.equiv (Sets.complement (Sets.complement x)) x.
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_contrapositive_CP.
    reflexivity.
  + apply Sets_included_double_complement.
Qed.

Lemma Sets_complement_intersect {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T} {_SETS_Classical_Properties: SETS_Classical_Properties T}:
  forall x y,
    Sets.equiv
      (Sets.complement (Sets.intersect x y))
      (Sets.union (Sets.complement x) (Sets.complement y)).
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_contrapositive_CP.
    rewrite Sets_complement_union.
    rewrite ! Sets_complement_complement.
    reflexivity.
  + apply Sets_included_complement_intersect.
Qed.

