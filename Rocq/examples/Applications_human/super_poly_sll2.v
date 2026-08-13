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
Require Import String.
Local Open Scope string.

Import naive_C_Rules.
Local Open Scope sac.

Section super_poly_sll2.
Context {A: Type}.
(* Context (storeA: addr -> A -> Assertion) (linkA: addr -> addr -> Assertion). *)
Context (storeA: addr -> A -> Assertion) (s n: string).

Fixpoint sll (x: addr) (l: list A): Assertion :=
  match l with
    | nil => “ x = NULL ” && emp
    | a :: l0 => “ x <> NULL ” &&
                  EX y: addr,
                  storeA x a **
                  &(x # s ->ₛ n) # Ptr |-> y **
                  sll y l0
  end.

Fixpoint sllseg (x y: addr) (l: list A): Assertion :=
  match l with
    | nil => “ x = y ” && emp
    | a :: l0 => “ x <> NULL ” &&
                  EX z: addr,
                  storeA x a **
                  &(x # s ->ₛ n) # Ptr |-> z **
                  sllseg z y l0
  end.

Fixpoint sllbseg (x y: addr) (l: list A): Assertion :=
  match l with
    | nil => “ x = y ” && emp
    | a :: l0 => EX x0: addr,
                  “ x0 <> NULL ” &&
                  x # Ptr |-> x0 **
                  storeA x0 a **
                  sllbseg (&(x0 # s ->ₛ n)) y l0
  end.

Definition append (l1 : list A) (l2 : list A) := app l1 l2.

Lemma sll_zero: forall x l,
  x = NULL ->
  sll x l |-- “ l = nil ” && emp.
Proof.
  intros.
  destruct l.
  + entailer!.
  + simpl.
    Intros. Intros x0.
    entailer!.
Qed.

Lemma sll_not_zero: forall x l,
  x <> NULL ->
  sll x l |--
    EX y a l0,
      “ l = a :: l0 ” &&
      storeA x a **
      &(x # s ->ₛ n) # Ptr |-> y **
      sll y l0.
Proof.
  intros.
  destruct l.
  + simpl.
    Intros.
    tauto.
  + simpl. Intros.
    Intros y.
    Exists y a l.
    entailer!.
Qed.

Lemma sll_not_zero': forall x l,
  x <> NULL ->
  sll x l |-- “ l <> nil ”.
Proof.
  intros.
  destruct l.
  + simpl.
    Intros.
    tauto.
  + simpl. Intros.
    Intros y.
    entailer!.
    congruence.
Qed.

Lemma sllseg_len1: forall x a y,
  x <> NULL ->
  storeA x a **
  &(x # s ->ₛ n) # Ptr |-> y |--
  sllseg x y (a :: nil).
Proof.
  intros.
  simpl sllseg.
  Exists y.
  entailer!.
Qed.

Lemma sllseg_sllseg: forall x y z l1 l2,
  sllseg x y l1 ** sllseg y z l2 |--
  sllseg x z (l1 ++ l2).
Proof.
  intros.
  revert x; induction l1; simpl sllseg; intros.
  + Intros.
    subst y.
    entailer!.
  + Intros. Intros z0.
    Exists z0.
    sep_apply IHl1.
    entailer!.
Qed.

Lemma sllseg_sll: forall x y l1 l2,
  sllseg x y l1 ** sll y l2 |--
  sll x (l1 ++ l2).
Proof.
  intros.
  revert x; induction l1; simpl sllseg; simpl sll; intros.
  + Intros.
    subst y.
    entailer!.
  + Intros. Intros z0.
    Exists z0.
    sep_apply IHl1.
    entailer!.
Qed.

Lemma sllbseg_2_sllseg: forall x y z l,
  sllbseg x y l ** y # Ptr |-> z |--
  EX y': addr, x # Ptr |-> y' ** sllseg y' z l.
Proof.
  intros.
  revert x; induction l; simpl; intros.
  + Intros.
    subst x.
    Exists z; entailer!.
  + Intros x_v.
    Exists x_v.
    sep_apply IHl.
    Intros y'.
    Exists y'.
    entailer!.
Qed.

Lemma sllbseg_len1: forall (x y: addr) (a: A),
  y <> 0 ->
  x # Ptr |-> y **
  storeA y a |--
  sllbseg x (&( y # s ->ₛ n)) (a :: nil).
Proof.
  intros.
  simpl.
  Exists y.
  entailer!.
Qed.

Lemma sllbseg_sllbseg: forall x y z l1 l2,
  sllbseg x y l1 ** sllbseg y z l2 |--
  sllbseg x z (l1 ++ l2).
Proof.
  intros.
  revert x; induction l1; simpl; intros.
  + entailer!.
    subst x.
    entailer!.
  + Intros u.
    Exists u.
    entailer!.
Qed.

Lemma sllseg_0_sll: forall x l,
  sllseg x 0 l |-- sll x l.
Proof.
  intros. revert x. 
  induction l; try easy.
  simpl. intros. 
  Intros z. Exists z. entailer!.
Qed. 

End super_poly_sll2.