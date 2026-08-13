/-
Coq inventory from `unifysl-prp/GeneralLogic/KripkeModel.v`.

Definitions/classes:
- KI.Relation, KI.Krelation
- upwards_closed_Kdenote
- Krelation_stable_Kdenote
- MonoEnsemble
- IdentityKripkeIntuitionisticModel, Korder_identity
- NoBranchKripkeIntuitionisticModel, Korder_no_branch
- BranchJoinKripkeIntuitionisticModel, Korder_branch_join

Instances:
- prod_BranchJoinKripkeIntuitionisticModel
- fun_BranchJoinKripkeIntuitionisticModel
- option00_BranchJoinKripkeIntuitionisticModel
- NoBranch2BranchJoin
- eq_ikiM
-/

import Unifysl.GeneralLogic.Base
import Unifysl.Lib.RelationPairs_ext

universe u v

namespace Unifysl

open Relation_ext

namespace KI

class Relation (worlds : Type u) : Type u where
  Krelation : worlds -> Ensemble worlds

export Relation (Krelation)

end KI

export KI (Relation Krelation)

def upwards_closed_Kdenote {worlds : Type u} [Relation worlds]
    (d : Ensemble worlds) : Prop :=
  forall n m, Krelation n m -> d n -> d m

def Krelation_stable_Kdenote {worlds : Type u} [Relation worlds]
    (d : Ensemble worlds) : Prop :=
  forall w1 w2, Krelation w1 w2 -> (d w1 <-> d w2)

def MonoEnsemble (A : Type u) [Relation A] : Type u :=
  { d : A -> Prop // upwards_closed_Kdenote d }

class IdentityKripkeIntuitionisticModel (worlds : Type u) [Relation worlds] :
    Prop where
  Korder_identity : forall m n : worlds, Krelation m n -> m = n

export IdentityKripkeIntuitionisticModel (Korder_identity)

class NoBranchKripkeIntuitionisticModel (worlds : Type u) [Relation worlds] :
    Prop where
  Korder_no_branch :
    forall m1 m2 n : worlds,
      Krelation n m1 -> Krelation n m2 -> Krelation m1 m2 \/ Krelation m2 m1

export NoBranchKripkeIntuitionisticModel (Korder_no_branch)

class BranchJoinKripkeIntuitionisticModel (worlds : Type u) [Relation worlds] :
    Prop where
  Korder_branch_join :
    forall m1 m2 n : worlds,
      Krelation n m1 -> Krelation n m2 ->
        exists m, Krelation m1 m /\ Krelation m2 m

export BranchJoinKripkeIntuitionisticModel (Korder_branch_join)

instance prod_BranchJoinKripkeIntuitionisticModel (A : Type u) (B : Type v)
    [RA : Relation A] [RB : Relation B]
    [bkiMA : BranchJoinKripkeIntuitionisticModel A]
    [bkiMB : BranchJoinKripkeIntuitionisticModel B] :
    (letI : Relation (A × B) :=
      { Krelation := RelProd (@Krelation A RA) (@Krelation B RB) }
     BranchJoinKripkeIntuitionisticModel (A × B)) := by
  letI : Relation (A × B) :=
    { Krelation := RelProd (@Krelation A RA) (@Krelation B RB) }
  constructor
  intro m1 m2 n hn1 hn2
  rcases m1 with ⟨m11, m12⟩
  rcases m2 with ⟨m21, m22⟩
  rcases n with ⟨n1, n2⟩
  rcases hn1 with ⟨hn11, hn12⟩
  rcases hn2 with ⟨hn21, hn22⟩
  rcases Korder_branch_join m11 m21 n1 hn11 hn21 with ⟨m1', hm11, hm21⟩
  rcases Korder_branch_join m12 m22 n2 hn12 hn22 with ⟨m2', hm12, hm22⟩
  exact ⟨(m1', m2'), ⟨hm11, hm12⟩, ⟨hm21, hm22⟩⟩

instance fun_BranchJoinKripkeIntuitionisticModel (A : Type u) (B : Type v)
    [RB : Relation B]
    [bkiMB : BranchJoinKripkeIntuitionisticModel B] :
    (letI : Relation (A -> B) :=
      { Krelation := pointwise_relation A (@Krelation B RB) }
     BranchJoinKripkeIntuitionisticModel (A -> B)) := by
  letI : Relation (A -> B) :=
    { Krelation := pointwise_relation A (@Krelation B RB) }
  constructor
  classical
  intro m1 m2 n hn1 hn2
  let m : A -> B := fun x =>
    Classical.choose (Korder_branch_join (m1 x) (m2 x) (n x) (hn1 x) (hn2 x))
  refine ⟨m, ?_, ?_⟩
  · intro x
    exact (Classical.choose_spec
      (Korder_branch_join (m1 x) (m2 x) (n x) (hn1 x) (hn2 x))).left
  · intro x
    exact (Classical.choose_spec
      (Korder_branch_join (m1 x) (m2 x) (n x) (hn1 x) (hn2 x))).right

instance option00_BranchJoinKripkeIntuitionisticModel (A : Type u)
    [R : Relation A]
    [bkiM : BranchJoinKripkeIntuitionisticModel A] :
    (letI : Relation (Option A) :=
      { Krelation := option00_relation (@Krelation A R) }
     BranchJoinKripkeIntuitionisticModel (Option A)) := by
  letI : Relation (Option A) :=
    { Krelation := option00_relation (@Krelation A R) }
  constructor
  intro m1 m2 n hn1 hn2
  cases hn1 with
  | None_None_option00 =>
      cases hn2 with
      | None_None_option00 =>
          exact ⟨none, None_None_option00, None_None_option00⟩
  | Some_Some_option00 a b hab =>
      cases hn2 with
      | Some_Some_option00 _ c hac =>
          rcases Korder_branch_join b c a hab hac with ⟨b', hbb', hcb'⟩
          exact ⟨some b',
            Some_Some_option00 b b' hbb',
            Some_Some_option00 c b' hcb'⟩

instance NoBranch2BranchJoin (A : Type u) [R : Relation A]
    [po_R : PreOrder (@Krelation A R)]
    [nkiM : NoBranchKripkeIntuitionisticModel A] :
    BranchJoinKripkeIntuitionisticModel A where
  Korder_branch_join := by
    intro m1 m2 n hn1 hn2
    cases Korder_no_branch m1 m2 n hn1 hn2 with
    | inl hm12 =>
        exact ⟨m2, hm12, po_R.refl m2⟩
    | inr hm21 =>
        exact ⟨m1, po_R.refl m1, hm21⟩

instance eq_ikiM {worlds : Type u} :
    (letI : Relation worlds := { Krelation := fun m n => m = n }
     IdentityKripkeIntuitionisticModel worlds) := by
  letI : Relation worlds := { Krelation := fun m n => m = n }
  constructor
  intro m n h
  exact h

end Unifysl
