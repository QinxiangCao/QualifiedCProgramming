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
  intros.
  destruct l.
  + entailer!.
  + simpl.
    Intros x0 x1.
    entailer!.
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
  intros.
  destruct l.
  + simpl.
    Intros.
    tauto.
  + simpl.
    Intros h y.
    Exists h y a l.
    entailer!.
Qed.

Lemma sllseg_sll: forall A (storeA: addr -> A -> Assertion) x y l1 l2,
  sllseg storeA x y l1 ** sll storeA y l2 |--
  sll storeA x (l1 ++ l2).
Proof.
  intros.
  revert x; induction l1; simpl sllseg; simpl sll; intros.
  + Intros.
    subst y.
    entailer!.
  + Intros. Intros z0 q.
    Exists z0 q.
    sep_apply IHl1.
    entailer!.
Qed.

Definition sll_para {A: Type} (storeA: addr -> A -> Assertion): Prop := True.
