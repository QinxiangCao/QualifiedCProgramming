Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Definition increasing
           {worlds: Type}
           {R: Relation worlds}
           {J: Join worlds}: worlds -> Prop :=
  fun m => forall n n', join m n n' -> n <= n'.

Definition increasing'
           {worlds: Type}
           {R: Relation worlds}
           {J: Join worlds}: worlds -> Prop :=
  fun m => forall n, m <= n -> increasing n.

Lemma incr_incr'
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}:
  forall m, increasing' m -> increasing m.
Proof.
  intros.
  apply H.
  reflexivity.
Qed.

(* 
 * In a separation algebra with discrete order, 
 * an element is increasing iff it is a unit.*)
Lemma disc_incr_unit
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}:
  IdentityKripkeIntuitionisticModel worlds ->
  forall e, increasing e <-> unit_element e.
Proof.
  intros;
  split; intros; hnf; intros.
  - hnf; intros.
    apply H.
    apply H0; auto.
  - apply H0 in H1; subst;
    reflexivity.
Qed.

Class IncreasingSeparationAlgebra
      (worlds: Type)
      {R: Relation worlds}
      {J: Join worlds }:=
{
  all_increasing: forall x: worlds, increasing x
}.

(*
  (* -Legacy definition-            *
   * Garbage Collected algebra      *
   * Is equivalent to increasing *)  
Class GarbageCollectSeparationAlgebra(worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {J: Join worlds }:=
  {
    join_has_order1: forall (m1 m2 m: worlds), join m1 m2 m -> m1 <= m
  }.
Lemma Increasing2GarbageCollect:
  forall
    (worlds: Type) {kiM: KripkeIntuitionisticModel worlds}
    {J: Join worlds }{SA: SeparationAlgebra worlds},
    GarbageCollectSeparationAlgebra worlds ->
    IncreasingSeparationAlgebra worlds.
Proof.
  intros.
  constructor; intros; hnf; intros.
  eapply join_has_order1.
  eapply join_comm. eassumption.
Qed.

Lemma GarbageCollect2Increasing:
  forall (worlds: Type) {kiM: KripkeIntuitionisticModel worlds}
    {J: Join worlds }{SA: SeparationAlgebra worlds},
    IncreasingSeparationAlgebra worlds ->
    GarbageCollectSeparationAlgebra worlds.
Proof.
  intros.
  constructor; intros.
  pose (all_increasing m2).
  apply i; apply join_comm; assumption.
Qed.
*)
Definition residue
           {worlds: Type}
           {R: Relation worlds}
           {J: Join worlds}
           (m n: worlds): Prop :=
  exists n', join n n' m /\ m <= n'.

Class ResidualSeparationAlgebra
      (worlds: Type)
      {R: Relation worlds}
      {J: Join worlds}:=
{
  residue_exists: forall n: worlds, exists m, residue n m;
}.

Class UnitalSeparationAlgebra
      (worlds: Type)
      {R: Relation worlds}
      {J: Join worlds}:=
{
  incr_exists: forall n: worlds, exists m, residue n m /\ increasing m
}.

Class UnitalSeparationAlgebra'
      (worlds: Type)
      {R: Relation worlds}
      {J: Join worlds}:=
{
  incr'_exists: forall n: worlds, exists m, residue n m /\ increasing' m
}.

(* A unital separation algebra is residual. *)
Lemma unital_is_residual
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}:
  UnitalSeparationAlgebra worlds ->
  ResidualSeparationAlgebra worlds.
Proof.
  constructor; intros.
  destruct (incr_exists n) as [m [RES _]].
  exists m; auto.
Qed.

(*A increasing separation algebras is unital 
 * iff it is residual.*)
Lemma incr_unital_iff_residual
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}:
  IncreasingSeparationAlgebra worlds ->
  UnitalSeparationAlgebra worlds <->
  ResidualSeparationAlgebra worlds.
Proof.
  intros; split.
  - apply unital_is_residual; auto.
  - constructor; intros.
    destruct (residue_exists n) as [m RES].
    exists m; split; auto.
    apply all_increasing.
Qed.

Class IncreasingJoinSelfSeparationAlgebra
      (worlds: Type)
      {R: Relation worlds}
      {U: Unit worlds}
      {J: Join worlds}:=
  incr_join_self:
    forall m, is_unit m -> join m m m.

Class IncreasingSplitSmallerSeparationAlgebra
      (worlds: Type)
      {R: Relation worlds}
      {J: Join worlds}
      {U: Unit worlds}:=
  incr_split_smaller:
    forall m1 m2 m, is_unit m -> join m1 m2 m -> m1 <= m.

Class UpwardsClosedSeparationAlgebra
      (worlds: Type)
      {R: Relation worlds}
      {J: Join worlds}:=
  join_Korder_up: forall m n m1 m2: worlds,
    join m1 m2 m -> m <= n ->
    exists n1 n2, join n1 n2 n /\ m1 <= n1 /\ m2 <= n2.

Class DownwardsClosedSeparationAlgebra
      (worlds: Type)
      {R: Relation worlds}
      {J: Join worlds}:=
  join_Korder_down: forall m1 m2 m n1 n2: worlds,
    join m1 m2 m -> n1 <= m1 -> n2 <= m2 ->
    exists n, join n1 n2 n /\ n <= m.

Class UnitJoinOrderRelation (worlds : Type)
{ U : Unit worlds}
{ J : Join worlds}
{ R : Relation worlds} := {
    unit_join_order_min_1: forall n : worlds, exists m1 m2 : worlds, join m1 m2 n /\ n <= m1 /\ is_unit m2;
    unit_join_order_min_2:
    forall m1 m2 u, is_unit m1 -> join m2 m1 u -> m2 <= u;
    mono_unit: forall m1 m2, is_unit m1 -> m1 <= m2 -> is_unit m2
}.

(* Lemma split_unit_ref
  {worlds: Type}
  {U: Unit worlds}
  {J: Join worlds}
  {R: Relation worlds}
  {po_R: PreOrder Krelation}
  {SA: SeparationAlgebra worlds}
  {UJORel: UnitJoinOrderRelation worlds}: forall m1 m2 n, is_unit n -> join m1 n m2 -> m1 = m2.
Proof.
  intros. 
  assert(forall n:worlds, is_unit n -> increasing n). {intros; unfold increasing. intros. apply join_comm in H2. apply (unit_join_order_min_2 _ _ _ H1 H2). }
  assert(m1 <= m2). { apply H1 in H. unfold increasing in H. apply join_comm in H0. apply H in H0. auto. }
  assert(m2 <= m1). { apply (unit_join_order_min_2 _ _ _ H H0). }   *)

Lemma incr_mono
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}
      {U: Unit worlds}
      {UJO_Rel: UnitJoinOrderRelation worlds}
      {SA: SeparationAlgebra worlds}
      {dSA: DownwardsClosedSeparationAlgebra worlds}:
forall m n, increasing m -> m <= n -> increasing n.
Proof.
  intros.
  hnf; intros.
  destruct (join_Korder_down _ _ _ _ _ H1 H0 ltac:(reflexivity)) as [n'' [? ?]].
  etransitivity; eauto.
Qed.

Lemma split_unit_ref
  {worlds: Type}
  {U: Unit worlds}
  {J: Join worlds}
  {R: Relation worlds}
  {po_R: PreOrder Krelation}
  {SA: SeparationAlgebra worlds}
  {UJORel: UnitJoinOrderRelation worlds}: forall n, exists m n', is_unit m /\ join m n' n /\ n <= n' /\ n' <= n.
Proof.
  intros. destruct (unit_join_order_min_1 n) as [ m1 [ m2 [ ? [ ? ? ] ] ] ].
  exists m2,m1; split; [auto|]. apply join_comm in H.
  assert(forall n:worlds, is_unit n -> increasing n). {intros; unfold increasing. intros. apply join_comm in H3. apply (unit_join_order_min_2 _ _ _ H2 H3). }
  assert(m1 <= n). { apply H2 in H1. unfold increasing in H1. apply H1 in H. auto. }
  auto.
Qed.
(* not use *)

Lemma is_unit_iff_increasing
  {worlds: Type}
  {U: Unit worlds}
  {J: Join worlds}
  {R: Relation worlds}
  {po_R: PreOrder Krelation}
  {SA: SeparationAlgebra worlds}
  {dSA: DownwardsClosedSeparationAlgebra worlds}
  {UJORel: UnitJoinOrderRelation worlds}: forall n:worlds, is_unit n <-> increasing n.
Proof.
  intros; split. 
  +intros; unfold increasing. intros. apply join_comm in H0. apply (unit_join_order_min_2 _ _ _ H H0).
  +intros. destruct (unit_join_order_min_1 n) as [ ? [? [? [ ? ? ] ] ] ]. pose proof incr_mono _ _ H H1. apply H3 in H0. eapply mono_unit; eauto.
Qed.

(* David J. Pym, Peter W. O’Hearn, and Hongseok Yang. Possible worlds and resources: the semantics of BI. *)

(* This join_Korder is equivalent with the following because Korder is reflexive.
  join_Korder: forall M (m1 m2 m n1 : Kworlds M), join m1 m2 m -> Korder m1 n1 -> exists n, join n1 m2 n /\ Korder m n;

It is necessary to be this strong, or else provable_sepcon_assoc will be unsound, e.g. the following weaker version causes unsoundness:
  join_Korder: forall M (m1 m2 m n1: Kworlds M), join m1 m2 m -> Korder m1 n1 -> exists n2 n, join n1 n2 n /\ Korder m2 n2 /\ Korder m n;  *)

Lemma residue_extensible
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}
      {dSA: DownwardsClosedSeparationAlgebra worlds}:
  forall e u,
    residue u e ->
    exists v, join e u v.
Proof.
  intros.
  destruct H as [u' [? ?]].
  pose proof join_Korder_down.
  pose proof H1 _ _ _ _ _ H ltac:(reflexivity) H0.
  firstorder.
Qed.

Lemma residual_extensible
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}
      {SA: SeparationAlgebra worlds}
      {dSA: DownwardsClosedSeparationAlgebra worlds}
      {resSA: ResidualSeparationAlgebra worlds}:
  forall u, exists e v, join u e v.
Proof.
  intros.
  destruct (residue_exists u) as [e ?].
  apply residue_extensible in H.
  destruct H as [v ?].
  apply join_comm in H.
  exists e, v; auto.
Qed.

Record sem_corable
       {worlds: Type}
       {R: Relation worlds}
       {J: Join worlds} (X: worlds -> Prop): Prop := {
  local2global: forall w1 w2 w3,
    join w1 w2 w3 -> X w1 -> X w3;
  global2local: forall w1 w2 w3,
    join w1 w2 w3 -> X w3 ->
    exists w1' w2', join w1' w2' w3 /\ w1 <= w1' /\ w2 <= w2' /\ X w1
}.
