Require Import HypotheticalExternLib.
Require Import ZArith.
Require Import interface_1.

Module NaiveLang.
  Definition expr {p: para} := (nat -> X * X) -> Prop.
  Section NaiveLang.
  Context {p: para}.
  Definition context := expr -> Prop.
  Definition impp (e1 e2 : expr) : expr := fun st => e1 st -> e2 st.
  Definition andp (e1 e2 : expr) : expr := fun st => e1 st /\ e2 st.
  Definition orp  (e1 e2 : expr) : expr := fun st => e1 st \/ e2 st.
  Definition falsep : expr := fun st => False.

  Definition provable (e : expr) : Prop := forall st, e st.
  End NaiveLang.
End NaiveLang.

Module NaiveRule.
  Include DerivedNames (NaiveLang).
  Section NaiveRule.
  Context {p: para}.
  Lemma provables_modus_ponens :
    forall x y : expr, provable (impp x y) -> provable x -> provable y.
  Proof. unfold provable, impp. auto. Qed.

  Lemma provable_axiom1 : forall x y : expr, provable (impp x (impp y x)).
  Proof. unfold provable, impp. auto. Qed.

  Lemma provable_axiom2 : forall x y z : expr,
      provable (impp (impp x (impp y z)) (impp (impp x y) (impp x z))).
  Proof. unfold provable, impp. auto. Qed.

  Lemma provable_andp_intros :
    forall x y : expr, provable (impp x (impp y (andp x y))).
  Proof. unfold provable, impp, andp. auto. Qed.

  Lemma provable_andp_elim1 : forall x y : expr, provable (impp (andp x y) x).
  Proof. unfold provable, impp, andp. tauto. Qed.

  Lemma provable_andp_elim2 : forall x y : expr, provable (impp (andp x y) y).
  Proof. unfold provable, impp, andp. tauto. Qed.

  Lemma provable_orp_intros1 : forall x y : expr, provable (impp x (orp x y)).
  Proof. unfold provable, impp, orp. auto. Qed.

  Lemma provable_orp_intros2 : forall x y : expr, provable (impp y (orp x y)).
  Proof. unfold provable, impp, orp. auto. Qed.

  Lemma provable_orp_elim : forall x y z : expr,
      provable (impp (impp x z) (impp (impp y z) (impp (orp x y) z))).
  Proof. unfold provable, impp, orp. tauto. Qed.

  Lemma provable_falsep_elim : forall x : expr, provable (impp falsep x).
  Proof. unfold provable, impp, falsep. destruct 1. Qed.

  Lemma provable_peirce_law : forall x y: expr, provable (impp (impp (impp x y) x) x).
  Proof. unfold provable, impp. intros; tauto. Qed.
  End NaiveRule.
End NaiveRule.

Module T := LogicTheorem NaiveLang NaiveRule.
Module Solver := IPSolver NaiveLang.
Import T.
Import Solver.

Notation "x --> y" := (impp x y)(at level 55, right associativity).
Notation "x && y" := (andp x y)(at level 40, left associativity).
Notation "|-- P " := (provable P) (at level 71, no associativity).

Goal forall {p: para} (P Q R: (nat -> X * X) -> Prop), |-- Q && P --> R --> P && Q && R.
  intros.
  Fail ip_solve.
Abort.
