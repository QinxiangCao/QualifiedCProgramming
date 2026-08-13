/-
Coq inventory from `unifysl-prp/SeparationLogic/Model/OrderedSA.v`.

Definitions:
- increasing
- increasing'
- residue

Classes/fields:
- IncreasingSeparationAlgebra.all_increasing
- ResidualSeparationAlgebra.residue_exists
- UnitalSeparationAlgebra.incr_exists
- UnitalSeparationAlgebra'.incr'_exists
- IncreasingJoinSelfSeparationAlgebra.incr_join_self
- IncreasingSplitSmallerSeparationAlgebra.incr_split_smaller
- UpwardsClosedSeparationAlgebra.join_Korder_up
- DownwardsClosedSeparationAlgebra.join_Korder_down
- UnitJoinOrderRelation.unit_join_order_min_1
- UnitJoinOrderRelation.unit_join_order_min_2
- UnitJoinOrderRelation.mono_unit

Theorems:
- incr_incr'
- disc_incr_unit
- unital_is_residual
- incr_unital_iff_residual
- incr_mono
- split_unit_ref
- is_unit_iff_increasing
- residue_extensible
- residual_extensible

Structures:
- sem_corable.local2global
- sem_corable.global2local

Notes:
- The commented-out Coq `GarbageCollectSeparationAlgebra` legacy block is
  intentionally omitted.
- Coq order notation `<=` is written explicitly as `Krelation`.
-/

import Unifysl.GeneralLogic.KripkeModel
import Unifysl.Lib.RelationPairs_ext
import Unifysl.SeparationLogic.Model.SeparationAlgebra

universe u

namespace Unifysl

def increasing {worlds : Type u} [Relation worlds] [Join worlds]
    (m : worlds) : Prop :=
  forall n n', join m n n' -> Krelation n n'

def increasing' {worlds : Type u} [Relation worlds] [Join worlds]
    (m : worlds) : Prop :=
  forall n, Krelation m n -> increasing n

theorem incr_incr' {worlds : Type u} [Relation worlds]
    [po_R : PreOrder (@Krelation worlds _)] [Join worlds] :
    forall m : worlds, increasing' m -> increasing m := by
  intro m hm
  exact hm m (PreOrder.refl m)

theorem disc_incr_unit {worlds : Type u} [Relation worlds]
    [po_R : PreOrder (@Krelation worlds _)] [Join worlds] :
    IdentityKripkeIntuitionisticModel worlds ->
      forall e : worlds, increasing e <-> unit_element e := by
  intro ikiM e
  constructor
  · intro he n n' hj
    exact Korder_identity n n' (he n n' hj)
  · intro he n n' hj
    rw [he n n' hj]
    exact po_R.refl n'

class IncreasingSeparationAlgebra (worlds : Type u)
    [Relation worlds] [Join worlds] : Prop where
  all_increasing : forall x : worlds, increasing x

export IncreasingSeparationAlgebra (all_increasing)

def residue {worlds : Type u} [Relation worlds] [Join worlds]
    (m n : worlds) : Prop :=
  exists n', join n n' m /\ Krelation m n'

class ResidualSeparationAlgebra (worlds : Type u)
    [Relation worlds] [Join worlds] : Prop where
  residue_exists : forall n : worlds, exists m, residue n m

export ResidualSeparationAlgebra (residue_exists)

class UnitalSeparationAlgebra (worlds : Type u)
    [Relation worlds] [Join worlds] : Prop where
  incr_exists : forall n : worlds, exists m, residue n m /\ increasing m

export UnitalSeparationAlgebra (incr_exists)

class UnitalSeparationAlgebra' (worlds : Type u)
    [Relation worlds] [Join worlds] : Prop where
  incr'_exists : forall n : worlds, exists m, residue n m /\ increasing' m

export UnitalSeparationAlgebra' (incr'_exists)

theorem unital_is_residual {worlds : Type u} [Relation worlds]
    [_po_R : PreOrder (@Krelation worlds _)] [Join worlds] :
    UnitalSeparationAlgebra worlds ->
      ResidualSeparationAlgebra worlds := by
  intro hU
  constructor
  intro n
  rcases hU.incr_exists n with ⟨m, hres, _⟩
  exact ⟨m, hres⟩

theorem incr_unital_iff_residual {worlds : Type u} [Relation worlds]
    [po_R : PreOrder (@Krelation worlds _)] [Join worlds] :
    IncreasingSeparationAlgebra worlds ->
      (UnitalSeparationAlgebra worlds <-> ResidualSeparationAlgebra worlds) := by
  intro hInc
  constructor
  · intro hU
    exact unital_is_residual (worlds := worlds) hU
  · intro hR
    constructor
    intro n
    rcases hR.residue_exists n with ⟨m, hres⟩
    exact ⟨m, hres, hInc.all_increasing m⟩

class IncreasingJoinSelfSeparationAlgebra (worlds : Type u)
    [Relation worlds] [Unit worlds] [Join worlds] : Prop where
  incr_join_self : forall m : worlds, is_unit m -> join m m m

export IncreasingJoinSelfSeparationAlgebra (incr_join_self)

class IncreasingSplitSmallerSeparationAlgebra (worlds : Type u)
    [Relation worlds] [Join worlds] [Unit worlds] : Prop where
  incr_split_smaller :
    forall m1 m2 m : worlds, is_unit m -> join m1 m2 m -> Krelation m1 m

export IncreasingSplitSmallerSeparationAlgebra (incr_split_smaller)

class UpwardsClosedSeparationAlgebra (worlds : Type u)
    [Relation worlds] [Join worlds] : Prop where
  join_Korder_up : forall m n m1 m2 : worlds,
    join m1 m2 m -> Krelation m n ->
    exists n1 n2, join n1 n2 n /\ Krelation m1 n1 /\ Krelation m2 n2

export UpwardsClosedSeparationAlgebra (join_Korder_up)

class DownwardsClosedSeparationAlgebra (worlds : Type u)
    [Relation worlds] [Join worlds] : Prop where
  join_Korder_down : forall m1 m2 m n1 n2 : worlds,
    join m1 m2 m -> Krelation n1 m1 -> Krelation n2 m2 ->
    exists n, join n1 n2 n /\ Krelation n m

export DownwardsClosedSeparationAlgebra (join_Korder_down)

class UnitJoinOrderRelation (worlds : Type u)
    [Unit worlds] [Join worlds] [Relation worlds] : Prop where
  unit_join_order_min_1 :
    forall n : worlds, exists m1 m2 : worlds,
      join m1 m2 n /\ Krelation n m1 /\ is_unit m2
  unit_join_order_min_2 :
    forall m1 m2 u : worlds, is_unit m1 -> join m2 m1 u -> Krelation m2 u
  mono_unit :
    forall m1 m2 : worlds, is_unit m1 -> Krelation m1 m2 -> is_unit m2

export UnitJoinOrderRelation
  (unit_join_order_min_1 unit_join_order_min_2 mono_unit)

theorem incr_mono {worlds : Type u} [Relation worlds]
    [po_R : PreOrder (@Krelation worlds _)] [Join worlds]
    [Unit worlds] [UnitJoinOrderRelation worlds]
    [SeparationAlgebra worlds] [DownwardsClosedSeparationAlgebra worlds] :
    forall m n : worlds, increasing m -> Krelation m n -> increasing n := by
  intro m n hm hmn a b hj
  rcases join_Korder_down n a b m a hj hmn (PreOrder.refl a) with
    ⟨n'', hj', hn''b⟩
  exact PreOrder.trans a n'' b (hm a n'' hj') hn''b

theorem split_unit_ref {worlds : Type u} [Unit worlds] [Join worlds]
    [Relation worlds] [_po_R : PreOrder (@Krelation worlds _)]
    [SeparationAlgebra worlds] [UnitJoinOrderRelation worlds] :
    forall n : worlds, exists m n',
      is_unit m /\ join m n' n /\ Krelation n n' /\ Krelation n' n := by
  intro n
  rcases unit_join_order_min_1 n with ⟨m1, m2, hj, hnm1, hum2⟩
  refine ⟨m2, m1, hum2, ?_, hnm1, ?_⟩
  · exact join_comm m1 m2 n hj
  · exact unit_join_order_min_2 m2 m1 n hum2 hj

theorem is_unit_iff_increasing {worlds : Type u} [Unit worlds] [Join worlds]
    [Relation worlds] [po_R : PreOrder (@Krelation worlds _)]
    [SeparationAlgebra worlds] [DownwardsClosedSeparationAlgebra worlds]
    [UnitJoinOrderRelation worlds] :
    forall n : worlds, is_unit n <-> increasing n := by
  intro n
  constructor
  · intro hn a b hj
    exact unit_join_order_min_2 n a b hn (join_comm n a b hj)
  · intro hn
    rcases unit_join_order_min_1 n with ⟨m1, m2, hj, hnm1, hum2⟩
    have hm1 : increasing m1 := incr_mono n m1 hn hnm1
    have hm2n : Krelation m2 n := hm1 m2 n hj
    exact mono_unit m2 n hum2 hm2n

theorem residue_extensible {worlds : Type u} [Relation worlds]
    [po_R : PreOrder (@Krelation worlds _)] [Join worlds]
    [DownwardsClosedSeparationAlgebra worlds] :
    forall e u : worlds, residue u e -> exists v, join e u v := by
  intro e u hres
  rcases hres with ⟨u', hj, huu'⟩
  rcases join_Korder_down e u' u e u hj (PreOrder.refl e) huu' with
    ⟨v, hv, _⟩
  exact ⟨v, hv⟩

theorem residual_extensible {worlds : Type u} [Relation worlds]
    [po_R : PreOrder (@Krelation worlds _)] [Join worlds]
    [SeparationAlgebra worlds] [DownwardsClosedSeparationAlgebra worlds]
    [resSA : ResidualSeparationAlgebra worlds] :
    forall u : worlds, exists e v, join u e v := by
  intro u
  rcases residue_exists u with ⟨e, hres⟩
  rcases residue_extensible e u hres with ⟨v, hv⟩
  exact ⟨e, v, join_comm e u v hv⟩

structure sem_corable {worlds : Type u} [Relation worlds] [Join worlds]
    (X : worlds -> Prop) : Prop where
  local2global :
    forall w1 w2 w3, join w1 w2 w3 -> X w1 -> X w3
  global2local :
    forall w1 w2 w3, join w1 w2 w3 -> X w3 ->
      exists w1' w2',
        join w1' w2' w3 /\ Krelation w1 w1' /\ Krelation w2 w2' /\ X w1

export sem_corable (local2global global2local)

end Unifysl
