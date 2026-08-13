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
From compcert.lib Require Import Integers.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.

Import naive_C_Rules.
Local Open Scope sac.

Fixpoint sll (x: addr) (l: list Z): Assertion :=
  match l with
    | nil     => “ x = NULL ” && emp
    | a :: l0 => “ x <> NULL ” && 
                 EX y: addr,
                   &(x # "list" ->ₛ "data") # Int |-> a **
                   &(x # "list" ->ₛ "next") # Ptr |-> y **
                   sll y l0
  end.

Fixpoint sllseg (x y: addr) (l: list Z): Assertion :=
  match l with
    | nil     => “ x = y ” && emp
    | a :: l0 => “ x <> NULL ” && 
                 EX z: addr,
                   &(x # "list" ->ₛ "data") # Int |-> a **
                   &(x # "list" ->ₛ "next") # Ptr |-> z **
                   sllseg z y l0
  end.

Fixpoint sllbseg (x y: addr) (l: list Z): Assertion :=
  match l with
    | nil     => “ x = y ” && emp
    | a :: l0 => EX z: addr,
                   “ z <> NULL ” && 
                   x # Ptr |-> z **
                   &(z # "list" ->ₛ "data") # Int |-> a **
                   sllbseg (&(z # "list" ->ₛ "next")) y l0
  end.

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
      &(x # "list" ->ₛ "data") # Int |-> a **
      &(x # "list" ->ₛ "next") # Ptr |-> y **
      sll y l0.
Proof.
  intros.
  destruct l.
  + simpl.
    Intros.
    tauto.
  + simpl. Intros.
    Intros y.
    Exists y z l.
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
  &(x # "list" ->ₛ "data") # Int |-> a **
  &(x # "list" ->ₛ "next") # Ptr |-> y |--
  sllseg x y [a].
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

Lemma sllbseg_len1: forall (x y: addr) (a: Z),
  y <> 0 ->
  x # Ptr |-> y **
  &( y # "list" ->ₛ "data") # Int |-> a |--
  sllbseg x (&( y # "list" ->ₛ "next")) [a].
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


Lemma sll_length : forall x l, 
  sll x l |-- store_align4_n (Zlength l * 2).
Proof.
  intros.
  revert x.
  induction l; simpl; intros.
  - Exists nil. entailer!.
    constructor.
  - Intros. Intros y.
    sep_apply IHl.
    sep_apply store_int_align4.
    sep_apply store_ptr_align4_32.
    sep_apply store_align4_merge.
    sep_apply (store_align4_merge (1 + 1) (Zlength l * 2)).
    assert ( 1 + 1 + Zlength l * 2 = Zlength (a :: l) * 2) by (rewrite Zlength_cons ; lia).
    rewrite H0. entailer!.
Qed.
   
Lemma sll_length_max : forall x l, 
  sll x l |-- “ Zlength l * 2 <= Int.max_unsigned / 4 + 1 ”.
Proof.
  intros.
  sep_apply sll_length.
  prop_apply store_align4_n_valid.
  Intros.
  rewrite addr_max_unsigned_eq_int in H.
  entailer!.
Qed. 
