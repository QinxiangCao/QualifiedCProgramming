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
From SimpleC.EE.QCP_demos_LLM Require Export dll_queue_lib.

Definition dlistrep_shape (x prev: addr) : Assertion :=
  EX l: list Z, dlistrep x prev l.

Definition dllseg_shape (x px py y: addr) : Assertion :=
  EX l: list Z, dllseg x y px py l.

Lemma dlistrep_zero : forall (x prev: Z), x = NULL -> dlistrep_shape x prev |-- emp.
Proof.
  intros x prev Hx.
  unfold dlistrep_shape.
  Intros l.
  sep_apply (dll_zero x prev l).
  - Intros_p Hl.
    subst l.
    cancel.
  - exact Hx.
Qed.

Lemma dlistrep_not_zero : forall (x prev: Z), x <> NULL -> dlistrep_shape x prev |-- EX v y, &(x # "list" ->ₛ "data") # Int |-> v **
  &(x # "list" ->ₛ "next") # Ptr |-> y **
  &(x # "list" ->ₛ "prev") # Ptr |-> prev ** dlistrep_shape y x.
Proof.
  intros x prev Hx.
  unfold dlistrep_shape.
  Intros l.
  sep_apply (dll_not_zero x prev l).
  - Intros y.
    Intros a.
    Intros l0.
    Exists a.
    Exists y.
    unfold dlistrep_shape.
    Exists l0.
    cancel (&(x # "list" ->ₛ "data") # Int |-> a).
    cancel (&(x # "list" ->ₛ "next") # Ptr |-> y).
    cancel (&(x # "list" ->ₛ "prev") # Ptr |-> prev).
    cancel (dlistrep y x l0).
  - exact Hx.
Qed.

Lemma dllseg_dlistrep_shape : forall x y px py, 
  dllseg_shape x px py y ** dlistrep_shape y py |-- dlistrep_shape x px.
Proof.
  intros x y px py.
  unfold dllseg_shape, dlistrep_shape.
  Intros l1.
  Intros l2.
  Exists (l1 ++ l2)%list.
  sep_apply (dllseg_dlistrep x y px py l1 l2).
  cancel.
Qed.

Lemma dllseg_shape_len1: forall (x px nx: addr) (a: Z),
  x <> NULL ->
  &(x # "list" ->ₛ "data") # Int |-> a **
  &(x # "list" ->ₛ "next") # Ptr |-> nx **
  &(x # "list" ->ₛ "prev") # Ptr |-> px |--
  dllseg_shape x px x nx.
Proof.
  intros x px nx a Hx.
  unfold dllseg_shape.
  Exists (a :: nil)%list.
  apply (dllseg_len1 x px nx a).
  exact Hx.
Qed.

Lemma dllseg_dllseg_shape: forall (x y z px py pz: addr),
  dllseg_shape x px py y **
  dllseg_shape y py pz z |--
  dllseg_shape x px pz z.
Proof.
  intros x y z px py pz.
  unfold dllseg_shape.
  Intros l1.
  Intros l2.
  Exists (l1 ++ l2)%list.
  sep_apply (dllseg_dllseg x y z px py pz l1 l2).
  cancel.
Qed.

Lemma dllseg_split_head : forall (x px py y: addr),
  x <> y -> 
  dllseg_shape x px py y |-- 
  EX z a, &(x # "list" ->ₛ "data") # Int |-> a **
  &(x # "list" ->ₛ "next") # Ptr |-> z **
  &(x # "list" ->ₛ "prev") # Ptr |-> px ** dllseg_shape z x py y.
Proof.
  intros x px py y Hxy.
  unfold dllseg_shape.
  Intros l.
  sep_apply (dllseg_head_neq x y px py l).
  - Intros z.
    Intros a.
    Intros l0.
    Exists z.
    Exists a.
    unfold dllseg_shape.
    Exists l0.
    cancel (&(x # "list" ->ₛ "data") # Int |-> a).
    cancel (&(x # "list" ->ₛ "next") # Ptr |-> z).
    cancel (&(x # "list" ->ₛ "prev") # Ptr |-> px).
    cancel (dllseg z y x py l0).
  - exact Hxy.
Qed.

Lemma dllseg_split_tail : forall (x px py y: addr),
  x <> y -> 
  dllseg_shape x px py y |-- 
  EX z a, “ py <> 0 ” && &(py # "list" ->ₛ "data") # Int |-> a **
  &(py # "list" ->ₛ "next") # Ptr |-> y **
  &(py # "list" ->ₛ "prev") # Ptr |-> z ** dllseg_shape x px z py.
Proof.
  intros x px py y Hxy.
  unfold dllseg_shape.
  Intros l.
  sep_apply (dllseg_head_neq_destruct_tail x y px py l).
  - Intros z.
    Intros l0.
    Intros a.
    Exists z.
    Exists a.
    unfold dllseg_shape.
    Exists l0.
    split_pure_spatial.
    + cancel (dllseg x py px z l0).
      cancel (&(py # "list" ->ₛ "data") # Int |-> a).
      cancel (&(py # "list" ->ₛ "next") # Ptr |-> y).
      cancel (&(py # "list" ->ₛ "prev") # Ptr |-> z).
    + dump_pre_spatial.
      exact H0.
  - exact Hxy.
Qed.

Lemma dllseg_split_tail' : forall (x px py y: addr),
  px <> py -> 
  dllseg_shape x px py y |-- 
  EX z a, “ py <> 0 ” && &(py # "list" ->ₛ "data") # Int |-> a **
  &(py # "list" ->ₛ "next") # Ptr |-> y **
  &(py # "list" ->ₛ "prev") # Ptr |-> z ** dllseg_shape x px z py.
Proof.
  intros x px py y Hpxy.
  unfold dllseg_shape.
  Intros l.
  sep_apply (dllseg_head_neq_destruct_tail' x y px py l).
  - Intros z.
    Intros l0.
    Intros a.
    Exists z.
    Exists a.
    unfold dllseg_shape.
    Exists l0.
    split_pure_spatial.
    + cancel (dllseg x py px z l0).
      cancel (&(py # "list" ->ₛ "data") # Int |-> a).
      cancel (&(py # "list" ->ₛ "next") # Ptr |-> y).
      cancel (&(py # "list" ->ₛ "prev") # Ptr |-> z).
    + dump_pre_spatial.
      exact H0.
  - exact Hpxy.
Qed.

