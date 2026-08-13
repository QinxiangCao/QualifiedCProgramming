import Unifysl.Lib.Bisimulation

/-
Coq inventory from `unifysl-prp/lib/RelationPairs_ext.v`.

Definitions/classes/helpers:
- PreOrder, RelProd, RelProd_Reflexive, RelProd_Transitive
- pointwise_reflexive, pointwise_transitive
- true_relation

Instances/theorems:
- eq_preorder
- RelProd_Preorder, RelProd_PartialFunctional, RelProd_Bisimulation, RelProd_Inclusion
- pointwise_preorder
- option00_reflexive, option01_reflexive, option00_symmetric
- option00_transitive, option01_transitive
- option00_preorder, option01_preorder, option00_equiv
- sum00_reflexive, sum01_reflexive, sum00_transitive, sum01_transitive
- sum00_preorder, sum01_preorder
- true_reflexive, true_transitive, true_preorder

Inductives and constructors:
- option00_relation: None_None_option00, Some_Some_option00
- option01_relation: None_None_option01, None_Some_option01, Some_Some_option01
- sum00_relation: sum00_ll, sum00_rr
- sum01_relation: sum01_ll, sum01_lr, sum01_rr

Coverage: all Coq declarations listed above are migrated in this file.
-/

universe u v

namespace Unifysl

open Relation_ext

class PreOrder {A : Type u} (R : relation A) : Prop where
  refl : Reflexive R
  trans : Transitive R

theorem PreOrder_Reflexive {A : Type u} {R : relation A} [PR : PreOrder R] :
    Reflexive R :=
  PR.refl

theorem PreOrder_Transitive {A : Type u} {R : relation A} [PR : PreOrder R] :
    Transitive R :=
  PR.trans

theorem eq_Reflexive {A : Type u} : Reflexive (@Eq A) := by
  intro x
  rfl

theorem eq_Transitive {A : Type u} : Transitive (@Eq A) := by
  intro x y z hxy hyz
  exact hxy.trans hyz

instance eq_preorder (A : Type u) : PreOrder (@Eq A) where
  refl := eq_Reflexive
  trans := eq_Transitive

def RelProd {A : Type u} {B : Type v} (RA : relation A) (RB : relation B) :
    relation (A × B) :=
  fun x y => RA x.1 y.1 /\ RB x.2 y.2

theorem RelProd_Reflexive {A : Type u} {B : Type v}
    (RA : relation A) (RB : relation B)
    {RRA : Reflexive RA} {RRB : Reflexive RB} :
    Reflexive (RelProd RA RB) := by
  intro x
  exact ⟨RRA x.1, RRB x.2⟩

theorem RelProd_Transitive {A : Type u} {B : Type v}
    (RA : relation A) (RB : relation B)
    {TRA : Transitive RA} {TRB : Transitive RB} :
    Transitive (RelProd RA RB) := by
  intro x y z hxy hyz
  exact ⟨TRA x.1 y.1 z.1 hxy.left hyz.left,
    TRB x.2 y.2 z.2 hxy.right hyz.right⟩

instance RelProd_Preorder {A : Type u} {B : Type v}
    (RA : relation A) (RB : relation B)
    [PRA : PreOrder RA] [PRB : PreOrder RB] :
    PreOrder (RelProd RA RB) where
  refl := RelProd_Reflexive RA RB (RRA := PRA.refl) (RRB := PRB.refl)
  trans := RelProd_Transitive RA RB (TRA := PRA.trans) (TRB := PRB.trans)

instance RelProd_PartialFunctional {A : Type u} {B : Type v}
    (RA : relation A) (RB : relation B)
    [PFA : PartialFunctional RA] [PFB : PartialFunctional RB] :
    PartialFunctional (RelProd RA RB) where
  partial_functionality := by
    intro m n n' hmn hmn'
    apply Prod.ext
    · exact PFA.partial_functionality m.1 n.1 n'.1 hmn.left hmn'.left
    · exact PFB.partial_functionality m.2 n.2 n'.2 hmn.right hmn'.right

instance RelProd_Bisimulation {A : Type u} {B : Type v}
    (bisA RA : relation A) (bisB RB : relation B)
    [BA : Bisimulation bisA RA] [BB : Bisimulation bisB RB] :
    Bisimulation (RelProd bisA bisB) (RelProd RA RB) where
  bis_l := by
    intro m n hmn m' hm'
    rcases BA.bis_l m.1 n.1 hmn.left m'.1 hm'.left with
      ⟨n1', hn1', hbis1'⟩
    rcases BB.bis_l m.2 n.2 hmn.right m'.2 hm'.right with
      ⟨n2', hn2', hbis2'⟩
    exact ⟨(n1', n2'), ⟨hn1', hn2'⟩, ⟨hbis1', hbis2'⟩⟩
  bis_r := by
    intro m n hmn n' hn'
    rcases BA.bis_r m.1 n.1 hmn.left n'.1 hn'.left with
      ⟨m1', hm1', hbis1'⟩
    rcases BB.bis_r m.2 n.2 hmn.right n'.2 hn'.right with
      ⟨m2', hm2', hbis2'⟩
    exact ⟨(m1', m2'), ⟨hm1', hm2'⟩, ⟨hbis1', hbis2'⟩⟩

instance RelProd_Inclusion {A : Type u} {B : Type v}
    (RA1 RA2 : relation A) (RB1 RB2 : relation B)
    [IA : Inclusion RA1 RA2] [IB : Inclusion RB1 RB2] :
    Inclusion (RelProd RA1 RB1) (RelProd RA2 RB2) where
  including := by
    intro x y h
    exact ⟨IA.including x.1 y.1 h.left, IB.including x.2 y.2 h.right⟩

theorem pointwise_reflexive (A : Type u) {B : Type v}
    (RB : relation B) {RR : Reflexive RB} :
    Reflexive (pointwise_relation A RB) := by
  intro f a
  exact RR (f a)

theorem pointwise_transitive (A : Type u) {B : Type v}
    (RB : relation B) {TR : Transitive RB} :
    Transitive (pointwise_relation A RB) := by
  intro f g h hfg hgh a
  exact TR (f a) (g a) (h a) (hfg a) (hgh a)

instance pointwise_preorder (A : Type u) {B : Type v}
    (RB : relation B) [PRB : PreOrder RB] :
    PreOrder (pointwise_relation A RB) where
  refl := pointwise_reflexive A RB (RR := PRB.refl)
  trans := pointwise_transitive A RB (TR := PRB.trans)

inductive option00_relation {A : Type u} (R : relation A) :
    relation (Option A) where
  | None_None_option00 : option00_relation R none none
  | Some_Some_option00 :
      forall a b, R a b -> option00_relation R (some a) (some b)

export option00_relation (None_None_option00 Some_Some_option00)

inductive option01_relation {A : Type u} (R : relation A) :
    relation (Option A) where
  | None_None_option01 : option01_relation R none none
  | None_Some_option01 : forall a, option01_relation R none (some a)
  | Some_Some_option01 :
      forall a b, R a b -> option01_relation R (some a) (some b)

export option01_relation
  (None_None_option01 None_Some_option01 Some_Some_option01)

instance option00_reflexive {A : Type u} (R : relation A) {RR : Reflexive R} :
    Reflexive (option00_relation R) := by
  intro x
  cases x with
  | none =>
      exact None_None_option00
  | some a =>
      exact Some_Some_option00 a a (RR a)

instance option01_reflexive {A : Type u} (R : relation A) {RR : Reflexive R} :
    Reflexive (option01_relation R) := by
  intro x
  cases x with
  | none =>
      exact None_None_option01
  | some a =>
      exact Some_Some_option01 a a (RR a)

instance option00_symmetric {A : Type u} (R : relation A) {SR : Symmetric R} :
    Symmetric (option00_relation R) := by
  intro x y hxy
  cases hxy with
  | None_None_option00 =>
      exact None_None_option00
  | Some_Some_option00 a b hab =>
      exact Some_Some_option00 b a (SR a b hab)

instance option00_transitive {A : Type u} (R : relation A) {TR : Transitive R} :
    Transitive (option00_relation R) := by
  intro x y z hxy hyz
  cases hxy with
  | None_None_option00 =>
      cases hyz with
      | None_None_option00 =>
          exact None_None_option00
  | Some_Some_option00 a b hab =>
      cases hyz with
      | Some_Some_option00 _ c hbc =>
          exact Some_Some_option00 a c (TR a b c hab hbc)

instance option01_transitive {A : Type u} (R : relation A) {TR : Transitive R} :
    Transitive (option01_relation R) := by
  intro x y z hxy hyz
  cases hxy with
  | None_None_option01 =>
      cases hyz with
      | None_None_option01 =>
          exact None_None_option01
      | None_Some_option01 c =>
          exact None_Some_option01 c
  | None_Some_option01 a =>
      cases hyz with
      | Some_Some_option01 _ c _ =>
          exact None_Some_option01 c
  | Some_Some_option01 a b hab =>
      cases hyz with
      | Some_Some_option01 _ c hbc =>
          exact Some_Some_option01 a c (TR a b c hab hbc)

instance option00_preorder {A : Type u} (R : relation A) [PR : PreOrder R] :
    PreOrder (option00_relation R) where
  refl := option00_reflexive R (RR := PR.refl)
  trans := option00_transitive R (TR := PR.trans)

instance option01_preorder {A : Type u} (R : relation A) [PR : PreOrder R] :
    PreOrder (option01_relation R) where
  refl := option01_reflexive R (RR := PR.refl)
  trans := option01_transitive R (TR := PR.trans)

instance option00_equiv {A : Type u} (R : relation A) {ER : Equivalence R} :
    Equivalence (option00_relation R) where
  refl := option00_reflexive R (RR := ER.refl)
  symm := by
    intro x y hxy
    exact option00_symmetric R
      (SR := fun a b hab => ER.symm hab) x y hxy
  trans := by
    intro x y z hxy hyz
    exact option00_transitive R
      (TR := fun a b c hab hbc => ER.trans hab hbc) x y z hxy hyz

inductive sum00_relation {A : Type u} {B : Type v}
    (RA : relation A) (RB : relation B) : relation (Sum A B) where
  | sum00_ll (a1 a2 : A) :
      RA a1 a2 -> sum00_relation RA RB (Sum.inl a1) (Sum.inl a2)
  | sum00_rr (b1 b2 : B) :
      RB b1 b2 -> sum00_relation RA RB (Sum.inr b1) (Sum.inr b2)

export sum00_relation (sum00_ll sum00_rr)

inductive sum01_relation {A : Type u} {B : Type v}
    (RA : relation A) (RB : relation B) : relation (Sum A B) where
  | sum01_ll (a1 a2 : A) :
      RA a1 a2 -> sum01_relation RA RB (Sum.inl a1) (Sum.inl a2)
  | sum01_lr (a : A) (b : B) :
      sum01_relation RA RB (Sum.inl a) (Sum.inr b)
  | sum01_rr (b1 b2 : B) :
      RB b1 b2 -> sum01_relation RA RB (Sum.inr b1) (Sum.inr b2)

export sum01_relation (sum01_ll sum01_lr sum01_rr)

instance sum00_reflexive {A : Type u} {B : Type v}
    (RA : relation A) (RB : relation B)
    {RRA : Reflexive RA} {RRB : Reflexive RB} :
    Reflexive (sum00_relation RA RB) := by
  intro x
  cases x with
  | inl a =>
      exact sum00_ll a a (RRA a)
  | inr b =>
      exact sum00_rr b b (RRB b)

instance sum01_reflexive {A : Type u} {B : Type v}
    (RA : relation A) (RB : relation B)
    {RRA : Reflexive RA} {RRB : Reflexive RB} :
    Reflexive (sum01_relation RA RB) := by
  intro x
  cases x with
  | inl a =>
      exact sum01_ll a a (RRA a)
  | inr b =>
      exact sum01_rr b b (RRB b)

instance sum00_transitive {A : Type u} {B : Type v}
    (RA : relation A) (RB : relation B)
    {TRA : Transitive RA} {TRB : Transitive RB} :
    Transitive (sum00_relation RA RB) := by
  intro x y z hxy hyz
  cases hxy with
  | sum00_ll a1 a2 ha12 =>
      cases hyz with
      | sum00_ll _ a3 ha23 =>
          exact sum00_ll a1 a3 (TRA a1 a2 a3 ha12 ha23)
  | sum00_rr b1 b2 hb12 =>
      cases hyz with
      | sum00_rr _ b3 hb23 =>
          exact sum00_rr b1 b3 (TRB b1 b2 b3 hb12 hb23)

instance sum01_transitive {A : Type u} {B : Type v}
    (RA : relation A) (RB : relation B)
    {TRA : Transitive RA} {TRB : Transitive RB} :
    Transitive (sum01_relation RA RB) := by
  intro x y z hxy hyz
  cases hxy with
  | sum01_ll a1 a2 ha12 =>
      cases hyz with
      | sum01_ll _ a3 ha23 =>
          exact sum01_ll a1 a3 (TRA a1 a2 a3 ha12 ha23)
      | sum01_lr _ b =>
          exact sum01_lr a1 b
  | sum01_lr a b =>
      cases hyz with
      | sum01_rr _ b2 _ =>
          exact sum01_lr a b2
  | sum01_rr b1 b2 hb12 =>
      cases hyz with
      | sum01_rr _ b3 hb23 =>
          exact sum01_rr b1 b3 (TRB b1 b2 b3 hb12 hb23)

instance sum00_preorder {A : Type u} {B : Type v}
    (RA : relation A) (RB : relation B)
    [PRA : PreOrder RA] [PRB : PreOrder RB] :
    PreOrder (sum00_relation RA RB) where
  refl := sum00_reflexive RA RB (RRA := PRA.refl) (RRB := PRB.refl)
  trans := sum00_transitive RA RB (TRA := PRA.trans) (TRB := PRB.trans)

instance sum01_preorder {A : Type u} {B : Type v}
    (RA : relation A) (RB : relation B)
    [PRA : PreOrder RA] [PRB : PreOrder RB] :
    PreOrder (sum01_relation RA RB) where
  refl := sum01_reflexive RA RB (RRA := PRA.refl) (RRB := PRB.refl)
  trans := sum01_transitive RA RB (TRA := PRA.trans) (TRB := PRB.trans)

def true_relation (A : Type u) : relation A :=
  fun _ _ => True

instance true_reflexive (A : Type u) : Reflexive (true_relation A) := by
  intro _
  trivial

instance true_transitive (A : Type u) : Transitive (true_relation A) := by
  intro _ _ _ _ _
  trivial

instance true_preorder (A : Type u) : PreOrder (true_relation A) where
  refl := true_reflexive A
  trans := true_transitive A

end Unifysl
