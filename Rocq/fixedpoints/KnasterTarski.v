Require Import ClassicalFacts.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.RelationPairs.
Require Import Coq.Program.Basics.
Require Import SetsClass.SetsDomain.
Require Import FP.PartialOrder_Setoid.
Require Import FP.LiftConstructors.

Local Open Scope order_scope.

(******************************************************************************)
(*                                                                            *)
(* This file contains the following parts:                                    *)
(*   Basic definitions                                                        *)
(*   Proof of the fixpoint theorem                                            *)
(*   Proof of extended properties                                             *)
(*   Instances of complete lattice                                            *)
(*   Other definition and proofs                                              *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(*                                                                            *)
(* Basic definitions                                                          *)
(*                                                                            *)
(******************************************************************************)

Definition upper_bound {A: Type} {RA: Order A} (T: A -> Prop) (bnd: A): Prop :=
  forall a, T a -> a <= bnd.
(*检查bnd是否是一个集合的上界*)

Definition least_upper_bound {A: Type} {RA: Order A} (T: A -> Prop) (bnd: A): Prop :=
  upper_bound T bnd /\
  forall bnd', upper_bound T bnd' -> bnd <= bnd'.
(*一个集合的上确界*)

Definition lower_bound {A:Type} {RA: Order A} (T: A -> Prop) (bnd: A): Prop :=
  forall a, T a -> bnd <= a.
(*检查bnd是否是一个集合的下界*)

Definition greatest_lower_bound {A:Type} {RA: Order A} (T: A -> Prop) (bnd: A): Prop :=
  lower_bound T bnd /\
  forall bnd', lower_bound T bnd' -> bnd' <= bnd.
(*一个集合的下确界*)

Class Lub (A: Type): Type :=
  lub: (A -> Prop) -> A. 

Class Glb (A: Type): Type :=
  glb: (A -> Prop) -> A. 

Class CompleteLattice_Setoid
        (A:Type) {RA: Order A} {EA: Equiv A}
        {LubA: Lub A} {glbA: Glb A}: Prop :=
{
  CL_PartialOrder: PartialOrder_Setoid A;
  CL_Complete_lub: forall T, least_upper_bound T (lub T);
  lub_congr: forall T1 T2, (forall a, T1 a <-> T2 a) -> lub T1 == lub T2;
}.

#[export] Existing Instance CL_PartialOrder.

Definition lower_than_fp {A: Type} {RA: Order A} (F: A -> A): A -> Prop :=
  fun x => x <= F x.

Definition greater_than_fp {A: Type} {RA: Order A} (F: A -> A): A -> Prop :=
  fun x => F x <= x.

Definition glb_of_lub {A: Type} {RA: Order A} {LubA: Lub A}: (A -> Prop) -> A :=
  fun X => lub (lower_bound X).

Definition KT_fix_g {A: Type} `{CL: CompleteLattice_Setoid A} (f: A -> A): A :=
  lub (lower_than_fp f).

Definition KT_fix_l {A: Type} `{CL: CompleteLattice_Setoid A} (f: A -> A): A :=
  glb_of_lub (greater_than_fp f).

(******************************************************************************)
(*                                                                            *)
(* Proof of the fixpoint theorem                                              *)
(*                                                                            *)
(******************************************************************************)

Lemma lower_bound_mono {A: Type} `{CL: CompleteLattice_Setoid A}: Proper (Sets.included --> Sets.included) (lower_bound).
Proof.
  unfold flip, Proper, respectful.
  sets_unfold.
  intros.
  hnf; intros.
  apply H0, H, H1.
Qed.

Lemma upper_bound_mono {A: Type} `{CL: CompleteLattice_Setoid A}: Proper (Sets.included --> Sets.included) (upper_bound).
Proof.
  unfold flip, Proper, respectful.
  sets_unfold.
  intros.
  hnf; intros.
  apply H0, H, H1.
Qed.

Lemma lub_less_than {A: Type} `{CL: CompleteLattice_Setoid A}: forall (X: A -> Prop) y,
  (forall x, X x -> x <= y) ->
  lub X <= y.
Proof.
  intros.
  pose proof CL_Complete_lub X as [? ?].
  apply H1.
  auto.
Qed.

Lemma less_than_lub {A: Type} `{CL: CompleteLattice_Setoid A}: forall x y (Y: A -> Prop),
  Y y ->
  x <= y ->
  x <= lub Y.
Proof.
  intros.
  pose proof CL_Complete_lub Y as [? ?].
  rewrite H0.
  apply H1.
  auto.
Qed.

Lemma element_less_than_lub {A: Type} `{CL: CompleteLattice_Setoid A}: forall x (X: A -> Prop),
  X x ->
  x <= lub X.
Proof.
  intros.
  pose proof CL_Complete_lub X as [? _].
  apply H0; auto.
Qed.

Lemma CL_Complete_glb {A: Type} `{CL: CompleteLattice_Setoid A}: forall T, greatest_lower_bound T (glb_of_lub T).
Proof.
  intros.
  hnf; intros.
  split.
  + hnf; intros.
    unfold glb_of_lub.
    apply lub_less_than.
    intros.
    auto.
  + intros.
    unfold glb_of_lub.
    apply element_less_than_lub; auto.
Qed.

Lemma lub_mono {A: Type} `{CL: CompleteLattice_Setoid A}: Proper (Sets.included ==> order_rel) lub.
Proof.
  hnf; intros.
  apply lub_less_than.
  intros.
  apply element_less_than_lub; auto.
  apply H, H0.
Qed.

Lemma glb_congr {A: Type} `{CL: CompleteLattice_Setoid A}: forall T1 T2, (forall a, T1 a <-> T2 a) -> glb_of_lub T1 == glb_of_lub T2.
Proof.
  intros.
  unfold glb_of_lub.
  apply lub_congr.
  intros.
  unfold lower_bound.
  apply all_iff_morphism; intros ?.
  rewrite H; tauto.
Qed.

Lemma less_than_glb {A: Type} `{CL: CompleteLattice_Setoid A}: forall (X: A -> Prop) y,
  (forall x, X x -> y <= x) ->
  y <= glb_of_lub X.
Proof.
  intros.
  pose proof CL_Complete_glb X as [? ?].
  apply H1.
  auto.
Qed.

Lemma glb_less_than {A: Type} `{CL: CompleteLattice_Setoid A}: forall x y (Y: A -> Prop),
  Y y ->
  y <= x ->
  glb_of_lub Y <= x.
Proof.
  intros.
  pose proof CL_Complete_glb Y as [? ?].
  rewrite <- H0.
  apply H1.
  auto.
Qed.

Lemma glb_mono {A: Type} `{CL: CompleteLattice_Setoid A}: Proper (Sets.included --> order_rel) glb_of_lub.
Proof.
  unfold flip; hnf; intros.
  unfold glb_of_lub.
  apply lub_mono.
  apply lower_bound_mono.
  auto.
Qed.

Lemma glb_less_than_element {A: Type} `{CL: CompleteLattice_Setoid A}: forall x (X: A -> Prop),
  X x ->
  glb_of_lub X <= x.
Proof.
  intros.
  unfold glb_of_lub.
  apply lub_less_than.
  intros.
  apply H0, H.
Qed.

Lemma KnasterTarski_fixpoint_theorem_g {A: Type} `{CL: CompleteLattice_Setoid A}: forall f,
  Proper (order_rel ==> order_rel) f ->
  KT_fix_g f == f (KT_fix_g f).
Proof.
  intros.
  assert (KT_fix_g f <= f (KT_fix_g f)).
  {
    unfold KT_fix_g.
    apply lub_less_than.
    intros.
    hnf in H0.
    rewrite H0.
    apply H.
    apply element_less_than_lub; auto.
  }
  apply antisymmetricity_setoid; auto.
  pose proof H _ _ H0: lower_than_fp f ((f (KT_fix_g f))).
  apply element_less_than_lub in H1.
  auto.
Qed.
  
Lemma KnasterTarski_fixpoint_greatest_fixpoint
        {A: Type}  {RA: Order A} {EA: Equiv A}
        {LubA: Lub A} {glbA: Glb A}
        {equ: Equivalence equiv}
        {CL: CompleteLattice_Setoid A}:
  forall f x,
    Proper (order_rel ==> order_rel) f ->
    x == f x ->
    x <= KT_fix_g f.
Proof.
  intros.
  pose proof CL_Complete_lub (lower_than_fp f) as [? ?].
  apply H1.
  unfold lower_than_fp.
  rewrite <- H0.
  reflexivity.
Qed.

Lemma KnasterTarski_fixpoint_theorem_l {A: Type} `{CL: CompleteLattice_Setoid A}:
  forall f,
    Proper (order_rel ==> order_rel) f ->
    KT_fix_l f == f (KT_fix_l f).
Proof.
  intros.
  assert (f (KT_fix_l f) <= KT_fix_l f).
  {
    unfold KT_fix_l.
    apply less_than_glb.
    intros.
    unfold greater_than_fp in H0.
    rewrite <- H0.
    apply H.
    apply glb_less_than_element; auto.
  }
  apply antisymmetricity_setoid; auto.
  pose proof H _ _ H0: greater_than_fp f ((f (KT_fix_l f))).
  apply glb_less_than_element in H1.
  auto.
Qed.

Lemma KnasterTarski_fixpoint_least_fixpoint
        {A: Type}  {RA: Order A} {EA: Equiv A}
        {LubA: Lub A} {glbA: Glb A}
        {equ: Equivalence equiv}
        {CL: CompleteLattice_Setoid A}:
  forall f x,
    Proper (order_rel ==> order_rel) f ->
    x == f x ->
    KT_fix_l f <= x.
Proof.
  intros.
  pose proof CL_Complete_glb (greater_than_fp f) as [? ?].
  apply H1.
  unfold greater_than_fp.
  rewrite <- H0.
  reflexivity.
Qed.

Lemma KnasterTarski_fixpoint_least_prefixpoint
        {A: Type}  {RA: Order A} {EA: Equiv A}
        {LubA: Lub A} {glbA: Glb A}
        {equ: Equivalence equiv}
        {CL: CompleteLattice_Setoid A}:
  forall f x,
    Proper (order_rel ==> order_rel) f ->
    f x <= x ->
    KT_fix_l f <= x.
Proof.
  intros.
  pose proof CL_Complete_glb (greater_than_fp f) as [? ?].
  apply H1.
  hnf.
  auto.
Qed.

(******************************************************************************)
(*                                                                            *)
(* Proof of extended properties                                               *)
(*                                                                            *)
(******************************************************************************)

Lemma KT_fix_l_mono_strong
        {A: Type}  {RA: Order A} {EA: Equiv A}
        {LubA: Lub A} {glbA: Glb A}
        {equ: Equivalence equiv}
        {CL: CompleteLattice_Setoid A}:
  Proper ((equiv ==> order_rel) ==> order_rel) KT_fix_l.
Proof.
  unfold Proper, respectful; intros.
  unfold KT_fix_l.
  apply glb_mono.
  unfold flip; sets_unfold.
  intros.
  unfold greater_than_fp.
  rewrite (H a a).
  + apply H0.
  + reflexivity.
Qed.

Lemma KT_fix_l_congr_strong
        {A: Type}  {RA: Order A} {EA: Equiv A}
        {LubA: Lub A} {glbA: Glb A}
        {equ: Equivalence equiv}
        {CL: CompleteLattice_Setoid A}:
  Proper ((equiv ==> equiv) ==> equiv) KT_fix_l.
Proof.
  unfold Proper, respectful; intros.
  apply antisymmetricity_setoid; apply KT_fix_l_mono_strong.
  + unfold respectful.
    intros; rewrite H by eauto.
    reflexivity.
  + unfold respectful.
    intros; rewrite H by (symmetry; eauto).
    reflexivity.
Qed.

Lemma KT_fix_l_mono
        {A: Type}  {RA: Order A} {EA: Equiv A}
        {LubA: Lub A} {glbA: Glb A}
        {equ: Equivalence equiv}
        {CL: CompleteLattice_Setoid A}:
  forall f g,
    Proper (order_rel ==> order_rel) f ->
    Proper (order_rel ==> order_rel) g ->
    lift_rel2 order_rel f g ->
    KT_fix_l f <= KT_fix_l g.
Proof.
  intros.
  apply KnasterTarski_fixpoint_least_prefixpoint; auto.
  rewrite (KnasterTarski_fixpoint_theorem_l g) at 2 by auto.
  apply H1.
Qed.

Lemma KT_fix_l_congr
        {A: Type}  {RA: Order A} {EA: Equiv A}
        {LubA: Lub A} {glbA: Glb A}
        {equ: Equivalence equiv}
        {CL: CompleteLattice_Setoid A}:
  forall f g,
    Proper (order_rel ==> order_rel) f ->
    Proper (order_rel ==> order_rel) g ->
    lift_rel2 equiv f g ->
    KT_fix_l f == KT_fix_l g.
Proof.
  intros.
  apply antisymmetricity_setoid; apply KT_fix_l_mono; auto.
  + hnf in H1 |- *.
    intros; rewrite H1; reflexivity.
  + hnf in H1 |- *.
    intros; rewrite H1; reflexivity.
Qed.

(****************************************)
(** For greatest fixed points           *)
(****************************************)

Lemma KT_fix_g_mono {A: Type} {RA: Order A} {EA: Equiv A}
        {LubA: Lub A} {glbA: Glb A}
        {equ: Equivalence equiv}
        {CL: CompleteLattice_Setoid A}:
  forall f g,
    lift_rel2 order_rel f g ->
    (KT_fix_g f) <= (KT_fix_g g).
Proof.
  intros. unfold KT_fix_g, lower_than_fp.
  apply CL_Complete_lub. intros until 1.
  pose proof CL_PartialOrder.
  assert (a <= (g a)).
  { eapply PO_Transitive. apply H0. apply H. }
  eapply less_than_lub;eauto. reflexivity.
Qed.

Lemma KT_fix_g_congr {A: Type} {RA: Order A} {EA: Equiv A}
        {LubA: Lub A} {glbA: Glb A}
        {equ: Equivalence equiv}
        {CL: CompleteLattice_Setoid A}:
  forall f g,
    lift_rel2 equiv f g ->
    (KT_fix_g f) == (KT_fix_g g).
Proof.
  intros.
  apply antisymmetricity_setoid; apply KT_fix_g_mono; auto.
  + hnf in H |- *.
    intros; rewrite H; reflexivity.
  + hnf in H |- *.
    intros; rewrite H; reflexivity.
Qed.


(******************************************************************************)
(*                                                                            *)
(* Instances of complete lattice                                              *)
(*                                                                            *)
(******************************************************************************)

Module CL_lift.
Import PO_lift.

Section CL_lift.

Context (A: Type) {B: Type} `{CLB: CompleteLattice_Setoid B}.

#[export] Instance Lub_lift: Lub (A -> B) :=
  lift_set_summary lub.

#[export] Instance Glb_lift: Glb (A -> B) :=
  lift_set_summary glb.

#[export] Instance CL_lift: CompleteLattice_Setoid (A -> B).
Proof.
  constructor.
  + apply PO_lift, CL_PartialOrder.
  + intros.
    split.
    - hnf; intros.
      intros ?.
      refine (proj1 (CL_Complete_lub _) _ _).
      eauto.
    - intros.
      intros ?.
      refine (proj2 (CL_Complete_lub _) _ _).
      hnf; intros.
      destruct H0 as [? [? ?]]; subst.
      apply (H x); auto.
  + intros.
    intros ?.
    unfold lift_set_summary.
    apply lub_congr.
    intros. apply ex_iff_morphism.
    intros ?.
    specialize (H a1); tauto.
Qed.

End CL_lift.

End CL_lift.

Module CL_sets.
Import PO_sets.

#[export] Instance Lub_sets
           {T: Type}
           {_SETS: Sets.SETS T}: Lub T :=
  Sets.general_union.

#[export] Instance Glb_sets
           {T: Type}
           {_SETS: Sets.SETS T}: Glb T :=
  Sets.general_intersect.

Ltac unfold_CL_defs :=
  unfold order_rel, equiv, lub, glb,
         R_sets, Equiv_sets, Lub_sets, Glb_sets.

#[export] Instance CL_sets
           {T: Type}
           {_SETS: Sets.SETS T}
           {_SETS_Properties: SETS_Properties T}: CompleteLattice_Setoid T.
Proof.
  split.
  + apply PO_sets.
  + intros; hnf; intros.
    split; intros.
    - hnf; intros. 
      apply Sets_included_general_union; intros.
      auto.
    - apply Sets_general_union_included.
      auto.
  + intros.
    apply Sets_equiv_Sets_included; auto.
    split; apply Sets_general_union_included; intros;
    apply Sets_included_general_union; apply H; auto.
Qed.

Arguments Lub_sets: simpl never.
Arguments Glb_sets: simpl never.

End CL_sets.

