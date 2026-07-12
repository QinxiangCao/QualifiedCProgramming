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
  intros x l Hx.
  destruct l.
  - simpl.
    subst x.
    split_pure_spatial.
    + Intros_p Hnil.
      cancel.
    + dump_pre_spatial.
      reflexivity.
  - simpl.
    rename z into a.
    rename l into l0.
    subst x.
    Intros y.
    contradiction.
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
  intros x l Hx.
  destruct l.
  - simpl.
    Intros_p Hnull.
    contradiction.
  - simpl.
    rename z into a.
    rename l into l0.
    Intros y.
    Exists y.
    Exists a.
    Exists l0.
    split_pure_spatial.
    + cancel (&(x # "list" ->ₛ "data") # Int |-> a).
      cancel (&(x # "list" ->ₛ "next") # Ptr |-> y).
      cancel (sll y l0).
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma sll_not_zero': forall x l,
  x <> NULL ->
  sll x l |-- “ l <> nil ”.
Proof.
  intros x l Hx.
  destruct l.
  - simpl.
    Intros_p Hnull.
    contradiction.
  - simpl.
    Intros y.
    dump_pre_spatial.
    discriminate.
Qed.

Lemma sllseg_len1: forall x a y,
  x <> NULL ->
  &(x # "list" ->ₛ "data") # Int |-> a **
  &(x # "list" ->ₛ "next") # Ptr |-> y |--
  sllseg x y [a].
Proof.
  intros x a y Hx.
  simpl.
  Exists y.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      exact Hx.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma sllseg_sllseg: forall x y z l1 l2,
  sllseg x y l1 ** sllseg y z l2 |--
  sllseg x z (l1 ++ l2).
Proof.
  intros x y z l1.
  revert x y z.
  induction l1; intros x y z l2.
  - simpl.
    Intros_p Hxy.
    subst y.
    cancel.
  - simpl.
    Intros z0.
    Exists z0.
    split_pure_spatial.
    + cancel (&(x # "list" ->ₛ "data") # Int |-> a).
      cancel (&(x # "list" ->ₛ "next") # Ptr |-> z0).
      apply (IHl1 z0 y z l2).
    + dump_pre_spatial.
      exact H.
Qed.

Lemma sllseg_sll: forall x y l1 l2,
  sllseg x y l1 ** sll y l2 |--
  sll x (l1 ++ l2).
Proof.
  intros x y l1.
  revert x y.
  induction l1; intros x y l2.
  - simpl.
    Intros_p Hxy.
    subst x.
    cancel.
  - simpl.
    Intros z0.
    Exists z0.
    split_pure_spatial.
    + cancel (&(x # "list" ->ₛ "data") # Int |-> a).
      cancel (&(x # "list" ->ₛ "next") # Ptr |-> z0).
      apply (IHl1 z0 y l2).
    + dump_pre_spatial.
      exact H.
Qed.

Lemma sllseg_unfold_head : forall p q l,
  p <> q ->
  sllseg p q l |--
  EX a z l',
    “ l = a :: l' ” &&
    &(p # "list" ->ₛ "data") # Int |-> a **
    &(p # "list" ->ₛ "next") # Ptr |-> z **
    sllseg z q l'.
Proof.
  intros p q l Hpq.
  destruct l as [| a l'].
  - simpl.
    Intros_p Heq.
    destruct (Hpq Heq).
  - simpl.
    Intros z.
    Exists a z l'.
    entailer!.
Qed.

Lemma sllbseg_2_sllseg: forall x y z l,
  sllbseg x y l ** y # Ptr |-> z |--
  EX y': addr, x # Ptr |-> y' ** sllseg y' z l.
Proof.
  intros x y target l.
  revert x y.
  induction l; intros x y.
  - simpl.
    Intros_p Hxy.
    subst x.
    Exists target.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
      reflexivity.
  - simpl.
    Intros y'.
    sep_apply (IHl (&(y' # "list" ->ₛ "next")) y).
    Intros tail.
    Exists y'.
    simpl.
    Exists tail.
    split_pure_spatial.
    + cancel (x # Ptr |-> y').
      cancel (&(y' # "list" ->ₛ "data") # Int |-> a).
      cancel (&(y' # "list" ->ₛ "next") # Ptr |-> tail).
      cancel (sllseg tail target l).
    + dump_pre_spatial.
      exact H.
Qed.

Lemma sllbseg_len1: forall (x y: addr) (a: Z),
  y <> 0 ->
  x # Ptr |-> y **
  &( y # "list" ->ₛ "data") # Int |-> a |--
  sllbseg x (&( y # "list" ->ₛ "next")) [a].
Proof.
  intros x y a Hy.
  simpl.
  Exists y.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      exact Hy.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma sllbseg_sllbseg: forall x y z l1 l2,
  sllbseg x y l1 ** sllbseg y z l2 |--
  sllbseg x z (l1 ++ l2).
Proof.
  intros x y z l1.
  revert x y z.
  induction l1; intros x y z l2.
  - simpl.
    Intros_p Hxy.
    subst x.
    cancel.
  - simpl.
    Intros y'.
    Exists y'.
    split_pure_spatial.
    + cancel (x # Ptr |-> y').
      cancel (&(y' # "list" ->ₛ "data") # Int |-> a).
      apply (IHl1 (&(y' # "list" ->ₛ "next")) y z l2).
    + dump_pre_spatial.
      exact H.
Qed.

Lemma sllseg_0_sll: forall x l,
  sllseg x 0 l |-- sll x l.
Proof.
  intros x l.
  revert x.
  induction l; intros x.
  - simpl.
    split_pure_spatial.
    + Intros_p Hnil.
      cancel.
    + Intros_p Hnil.
      rewrite Hnil.
      dump_pre_spatial.
      reflexivity.
  - simpl.
    Intros z0.
    Exists z0.
    split_pure_spatial.
    + cancel (&(x # "list" ->ₛ "data") # Int |-> a).
      cancel (&(x # "list" ->ₛ "next") # Ptr |-> z0).
      apply IHl.
    + dump_pre_spatial.
      exact H.
Qed. 


Lemma sll_length : forall x l, 
  sll x l |-- store_align4_n (Zlength l * 2).
Proof.
  intros x l.
  revert x.
  induction l; intros x.
  -
    simpl.
    unfold store_align4_n.
    Exists nil.
    simpl.
    split_pure_spatial;
      [ Intros_p Hnil; cancel
      | dump_pre_spatial;
        split;
        [ rewrite Zlength_nil; reflexivity
        | constructor ] ].
  -
    simpl.
    Intros y.
    replace (Zlength (a :: l) * 2) with (2 + Zlength l * 2) by (rewrite Zlength_cons; lia).
    sep_apply (store_int_align4 (&(x # "list" ->ₛ "data")) a).
    sep_apply (store_ptr_align4 (&(x # "list" ->ₛ "next")) y).
    sep_apply (IHl y).
    sep_apply (store_align4_merge 1 1).
    replace (1 + 1) with 2 by lia.
    sep_apply (store_align4_merge 2 (Zlength l * 2)).
    cancel (store_align4_n (2 + Zlength l * 2)).
Qed.
   
Lemma sll_length_max : forall x l, 
  sll x l |-- “ Zlength l * 2 <= Int.max_unsigned / 4 + 1 ”.
Proof.
  intros x l.
  sep_apply (sll_length x l).
  prop_apply store_align4_n_valid.
  Intros.
  dump_pre_spatial.
  exact H.
Qed. 


