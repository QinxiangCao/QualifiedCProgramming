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

Fixpoint sll {A: Type} (storeA: addr -> A -> Assertion) (x: addr) (l: list A): Assertion :=
  match l with
    | nil     => “ x = NULL ” && emp
    | a :: l0 => “ x <> NULL ” && 
                 EX h y: addr,
                   &(x # "list" ->ₛ "data") # Ptr |-> h **
                   &(x # "list" ->ₛ "next") # Ptr |-> y **
                   storeA h a **
                   sll storeA y l0
  end.

Fixpoint sllseg {A : Type} (storeA : addr -> A -> Assertion) (x : addr) (y : addr) (l : list A) : Assertion :=
  match l with
    | nil     => “ x = y ” && emp
    | a :: l0 => “ x <> NULL ” && 
                 EX h q: addr,
                   &(x # "list" ->ₛ "data") # Ptr |-> h **
                   &(x # "list" ->ₛ "next") # Ptr |-> q **
                   storeA h a **
                   sllseg storeA q y l0
  end.

Definition append {A : Type} (l1 : list A) (l2 : list A) := app l1 l2.

Lemma sll_zero: forall A (storeA: addr -> A -> Assertion) x l,
  x = NULL ->
  sll storeA x l |-- “ l = nil ” && emp.
Proof.
  intros A storeA x l Hx.
  destruct l.
  - simpl.
    subst x.
    split_pure_spatial.
    + Intros_p Hnil.
      cancel.
    + dump_pre_spatial.
      reflexivity.
  - simpl.
    rename a into v.
    rename l into l0.
    subst x.
    Intros h.
    Intros y.
    contradiction.
Qed.

Lemma sll_not_zero: forall A (storeA: addr -> A -> Assertion) x l,
  x <> NULL ->
  sll storeA x l |--
    EX h y a l0,
      “ l = a :: l0 ” &&
      &(x # "list" ->ₛ "data") # Ptr |-> h **
      &(x # "list" ->ₛ "next") # Ptr |-> y **
      storeA h a **
      sll storeA y l0.
Proof.
  intros A storeA x l Hx.
  destruct l.
  - simpl.
    Intros_p Hnull.
    contradiction.
  - simpl.
    rename a into v.
    rename l into l0.
    Intros h.
    Intros y.
    Exists h.
    Exists y.
    Exists v.
    Exists l0.
    split_pure_spatial.
    + cancel (&(x # "list" ->ₛ "data") # Ptr |-> h).
      cancel (&(x # "list" ->ₛ "next") # Ptr |-> y).
      cancel (storeA h v).
      cancel (sll storeA y l0).
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma sllseg_sll: forall A (storeA: addr -> A -> Assertion) x y l1 l2,
  sllseg storeA x y l1 ** sll storeA y l2 |--
  sll storeA x (l1 ++ l2).
Proof.
  intros A storeA x y l1.
  revert x y.
  induction l1; intros x y l2.
  - simpl.
    Intros_p Hxy.
    subst x.
    cancel.
  - simpl.
    Intros h.
    Intros q.
    Exists h.
    Exists q.
    split_pure_spatial.
    + cancel (&(x # "list" ->ₛ "data") # Ptr |-> h).
      cancel (&(x # "list" ->ₛ "next") # Ptr |-> q).
      cancel (storeA h a).
      apply (IHl1 q y l2).
    + dump_pre_spatial.
      exact H.
Qed.

Definition sll_para {A: Type} (storeA: addr -> A -> Assertion): Prop := True.
