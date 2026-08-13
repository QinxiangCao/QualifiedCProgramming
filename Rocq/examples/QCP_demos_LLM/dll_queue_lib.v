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

Fixpoint dlistrep (x prev: addr) (l: list Z): Assertion :=
  match l with
    | nil     => “ x = NULL ” && emp
    | a :: l0 => “ x <> NULL ” && 
                 EX y: addr,
                   &(x # "list" ->ₛ "data") # Int |-> a **
                   &(x # "list" ->ₛ "next") # Ptr |-> y **
                   &(x # "list" ->ₛ "prev") # Ptr |-> prev **
                   dlistrep y x l0
  end.

Fixpoint dllseg (x y px py: addr) (l: list Z): Assertion :=
  match l with
    | nil     => “ x = y ” && “ px = py ” && emp
    | a :: l0 => “ x <> NULL ” && 
                 EX z: addr,
                   &(x # "list" ->ₛ "data") # Int |-> a **
                   &(x # "list" ->ₛ "next") # Ptr |-> z **
                   &(x # "list" ->ₛ "prev") # Ptr |-> px **
                   dllseg z y x py l0
  end.

Definition store_queue (x: addr) (l: list Z): Assertion :=
  EX h t: addr,
    &(x # "queue" ->ₛ "head") # Ptr |-> h **
    &(x # "queue" ->ₛ "tail") # Ptr |-> t **
    dllseg h NULL NULL t l.

Lemma dllseg_len1: forall (x px nx: addr) (a: Z),
  x <> NULL ->
  &(x # "list" ->ₛ "data") # Int |-> a **
  &(x # "list" ->ₛ "next") # Ptr |-> nx **
  &(x # "list" ->ₛ "prev") # Ptr |-> px |--
  dllseg x nx px x [a].
Proof.
  intros x px nx a Hx.
  simpl.
  Exists nx.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      exact Hx.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma dllseg_dllseg: forall (x y z px py pz: addr) l1 l2,
  dllseg x y px py l1 **
  dllseg y z py pz l2 |--
  dllseg x z px pz (l1 ++ l2).
Proof.
  intros x y z px py pz l1.
  revert x y z px py pz.
  induction l1; intros x y z px py pz l2.
  - simpl.
    Intros_p Hxy.
    Intros_p Hpxpy.
    subst y.
    subst py.
    cancel.
  - simpl.
    Intros z0.
    Exists z0.
    split_pure_spatial.
    + cancel (&(x # "list" ->ₛ "data") # Int |-> a).
      cancel (&(x # "list" ->ₛ "next") # Ptr |-> z0).
      cancel (&(x # "list" ->ₛ "prev") # Ptr |-> px).
      apply (IHl1 z0 y z x py pz l2).
    + dump_pre_spatial.
      exact H.
Qed.

Lemma dllseg_head_zero: forall x y px py l,
  x = 0 ->
  dllseg x y px py l |--
  “ y = 0 ” && “ px = py ” && “ l = nil ” && emp.
Proof.
  intros x y px py l Hx.
  destruct l.
  - simpl.
    subst x.
    repeat (split_pure_spatial || split_pures).
    + Intros_p Hxy.
      Intros_p Hpxpy.
      cancel.
    + Intros_p Hxy.
      dump_pre_spatial.
      symmetry.
      exact Hxy.
    + Intros_p Hxy.
      Intros_p Hpxpy.
      dump_pre_spatial.
      exact Hpxpy.
    + Intros_p Hxy.
      Intros_p Hpxpy.
      dump_pre_spatial.
      reflexivity.
  - simpl.
    rename z into a.
    rename l into l0.
    subst x.
    Intros z.
    contradiction.
Qed.

Lemma dllseg_head_neq: forall x y px py l,
  x <> y ->
  dllseg x y px py l |--
  EX z a l0,
    “ l = a :: l0 ” &&
    &(x # "list" ->ₛ "data") # Int |-> a **
    &(x # "list" ->ₛ "next") # Ptr |-> z **
    &(x # "list" ->ₛ "prev") # Ptr |-> px **
    dllseg z y x py l0.
Proof.
  intros x y px py l Hxy.
  destruct l.
  - simpl.
    Intros_p Hxy0.
    contradiction.
  - simpl.
    rename z into a.
    rename l into l0.
    Intros z.
    Exists z.
    Exists a.
    Exists l0.
    split_pure_spatial.
    + cancel (&(x # "list" ->ₛ "data") # Int |-> a).
      cancel (&(x # "list" ->ₛ "next") # Ptr |-> z).
      cancel (&(x # "list" ->ₛ "prev") # Ptr |-> px).
      cancel (dllseg z y x py l0).
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma dllseg_head_neq_destruct_tail_aux: forall x y px py l,
  dllseg x y px py l |--
  “ x = y ” && “ px = py ” && “ l = nil ” && emp ||
  EX z l0 a,
    “ py <> 0 ” &&
    “ l = (l0 ++ a :: nil)%list ” &&
    dllseg x py px z l0 **
    &(py # "list" ->ₛ "data") # Int |-> a **
    &(py # "list" ->ₛ "next") # Ptr |-> y **
    &(py # "list" ->ₛ "prev") # Ptr |-> z.
Proof.
  intros x y px py l.
  revert x y px py.
  induction l; intros x y px py.
  - simpl.
    Left.
    repeat (split_pure_spatial || split_pures).
    + Intros_p Hxy.
      Intros_p Hpxpy.
      cancel.
    + Intros_p Hxy.
      dump_pre_spatial.
      exact Hxy.
    + Intros_p Hxy.
      Intros_p Hpxpy.
      dump_pre_spatial.
      exact Hpxpy.
    + Intros_p Hxy.
      Intros_p Hpxpy.
      dump_pre_spatial.
      reflexivity.
  - simpl.
    Intros z0.
    sep_apply (IHl z0 y x py).
    Split.
    + Right.
      Exists px.
      Exists (@nil Z).
      Exists a.
      repeat (split_pure_spatial || split_pures).
      * Intros_p Hz0y.
        Intros_p Hxpy.
        Intros_p Hl.
        subst y.
        subst py.
        simpl.
        repeat (split_pure_spatial || split_pures).
        -- cancel (&(x # "list" ->ₛ "data") # Int |-> a).
           cancel (&(x # "list" ->ₛ "next") # Ptr |-> z0).
           cancel (&(x # "list" ->ₛ "prev") # Ptr |-> px).
        -- dump_pre_spatial.
           reflexivity.
        -- dump_pre_spatial.
           reflexivity.
      * Intros_p Hz0y.
        Intros_p Hxpy.
        Intros_p Hl.
        dump_pre_spatial.
        subst py.
        exact H.
      * Intros_p Hz0y.
        Intros_p Hxpy.
        Intros_p Hl.
        dump_pre_spatial.
        subst l.
        reflexivity.
    + Intros z.
      Intros l0.
      Intros a0.
      Right.
      Exists z.
      Exists (a :: l0)%list.
      Exists a0.
      repeat (split_pure_spatial || split_pures).
      * cancel (&(py # "list" ->ₛ "data") # Int |-> a0).
        cancel (&(py # "list" ->ₛ "next") # Ptr |-> y).
        cancel (&(py # "list" ->ₛ "prev") # Ptr |-> z).
        simpl.
        Exists z0.
        split_pure_spatial.
        -- cancel (&(x # "list" ->ₛ "data") # Int |-> a).
           cancel (&(x # "list" ->ₛ "next") # Ptr |-> z0).
           cancel (&(x # "list" ->ₛ "prev") # Ptr |-> px).
           cancel (dllseg z0 py x z l0).
        -- dump_pre_spatial.
           exact H.
      * dump_pre_spatial.
        exact H0.
      * dump_pre_spatial.
        subst l.
        reflexivity.
Qed.

Lemma dllseg_head_neq_destruct_tail: forall x y px py l,
  x <> y ->
  dllseg x y px py l |--
  EX z l0 a,
    “ py <> 0 ” &&
    “ l = (l0 ++ a :: nil)%list ” &&
    dllseg x py px z l0 **
    &(py # "list" ->ₛ "data") # Int |-> a **
    &(py # "list" ->ₛ "next") # Ptr |-> y **
    &(py # "list" ->ₛ "prev") # Ptr |-> z.
Proof.
  intros x y px py l Hxy.
  sep_apply dllseg_head_neq_destruct_tail_aux.
  normalize.
  Split.
  - Intros_p Hxy'.
    contradiction.
  - cancel.
Qed.

Lemma dllseg_head_neq_destruct_tail': forall x y px py l,
  px <> py ->
  dllseg x y px py l |--
  EX z l0 a,
    “ py <> 0 ” &&
    “ l = (l0 ++ a :: nil)%list ” &&
    dllseg x py px z l0 **
    &(py # "list" ->ₛ "data") # Int |-> a **
    &(py # "list" ->ₛ "next") # Ptr |-> y **
    &(py # "list" ->ₛ "prev") # Ptr |-> z.
Proof.
  intros x y px py l Hpxpy.
  sep_apply dllseg_head_neq_destruct_tail_aux.
  normalize.
  Split.
  - Intros_p Hxy.
    Intros_p Hpxpy'.
    contradiction.
  - cancel.
Qed.

Lemma dll_zero : forall (x prev : addr) (l : list Z),
  x = NULL ->
  dlistrep x prev l |-- “ l = nil ” && emp.
Proof.
  intros x prev l Hx.
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

Lemma dll_not_zero: forall x prev l,
  x <> NULL ->
  dlistrep x prev l |--
    EX y a l0,
      “ l = a :: l0 ” &&
      &(x # "list" ->ₛ "data") # Int |-> a **
      &(x # "list" ->ₛ "next") # Ptr |-> y **
      &(x # "list" ->ₛ "prev") # Ptr |-> prev **
      dlistrep y x l0.
Proof.
  intros x prev l Hx.
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
      cancel (&(x # "list" ->ₛ "prev") # Ptr |-> prev).
      cancel (dlistrep y x l0).
    + dump_pre_spatial.
      reflexivity.
Qed.

Lemma dllseg_dlistrep : forall x y px py l1 l2,
  dllseg x y px py l1 ** dlistrep y py l2 |-- dlistrep x px (l1 ++ l2).
Proof.
  intros x y px py l1.
  revert x y px py.
  induction l1; intros x y px py l2.
  - simpl.
    Intros_p Hxy.
    Intros_p Hpxpy.
    subst x.
    subst px.
    cancel.
  - simpl.
    Intros z0.
    Exists z0.
    split_pure_spatial.
    + cancel (&(x # "list" ->ₛ "data") # Int |-> a).
      cancel (&(x # "list" ->ₛ "next") # Ptr |-> z0).
      cancel (&(x # "list" ->ₛ "prev") # Ptr |-> px).
      apply (IHl1 z0 y x py l2).
    + dump_pre_spatial.
      exact H.
Qed.
