Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.

Import naive_C_Rules.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Export sll_lib.

Definition listrep (x : addr) : Assertion :=
  EX l: list Z, sll x l.

Definition lseg (x y: addr): Assertion :=
  EX l: list Z, sllseg x y l.

Definition listboxseg (x y: addr): Assertion :=
  EX l: list Z, sllbseg x y l.

Definition sll_tag (x : addr) : Prop := True.

Lemma listrep_zero : forall (x : Z), x = NULL -> listrep x |-- emp.
Proof.
  intros x Hx.
  unfold listrep.
  Intros l.
  sep_apply (sll_zero x l).
  - Intros_p Hl.
    subst l.
    cancel.
  - exact Hx.
Qed.

Lemma listrep_nonzero : forall (x : Z), x <> NULL -> listrep x |-- EX y a, &(x # "list" ->ₛ "data") # Int |-> a ** &(x # "list" ->ₛ "next") # Ptr |-> y ** listrep y.
Proof.
  intros x Hx.
  unfold listrep.
  Intros l.
  sep_apply (sll_not_zero x l).
  - Intros y.
    Intros a.
    Intros l0.
    Exists y.
    Exists a.
    unfold listrep.
    Exists l0.
    cancel (&(x # "list" ->ₛ "data") # Int |-> a).
    cancel (&(x # "list" ->ₛ "next") # Ptr |-> y).
    cancel (sll y l0).
  - exact Hx.
Qed.

Lemma lseg_len1: forall x a y,
  x <> NULL ->
  &(x # "list" ->ₛ "data") # Int |-> a **
  &(x # "list" ->ₛ "next") # Ptr |-> y |--
  lseg x y.
Proof.
  intros x a y Hx.
  unfold lseg.
  Exists (a :: nil)%list.
  apply sllseg_len1.
  exact Hx.
Qed.

Lemma lseg_lseg: forall x y z,
  lseg x y ** lseg y z |--
  lseg x z.
Proof.
  intros x y z.
  unfold lseg.
  Intros l1.
  Intros l2.
  Exists (l1 ++ l2)%list.
  sep_apply (sllseg_sllseg x y z l1 l2).
  cancel.
Qed.

Lemma lseg_listrep : forall (x y : addr), 
  lseg x y ** listrep y |-- listrep x.
Proof.
  intros x y.
  unfold lseg, listrep.
  Intros l1.
  Intros l2.
  Exists (l1 ++ l2)%list.
  sep_apply (sllseg_sll x y l1 l2).
  cancel.
Qed.