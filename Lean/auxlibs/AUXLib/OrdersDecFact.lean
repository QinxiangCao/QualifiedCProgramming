import Std
import Init.Data.Order.Lemmas
import Lean.Elab.Tactic.Omega

namespace AUXLib

/-- Computational two-way proof object corresponding to Coq's `sumbool`. -/
inductive Sumbool (P Q : Prop) : Type where
  | left (h : P)
  | right (h : Q)

/-- A decidable setoid equality, corresponding to the `eq` field of Coq's
`OrderedTypeFull'`.  It is deliberately separate from Lean's native `Eq`. -/
class DecidableSetoid (α : Type u) where
  eqv : α -> α -> Prop
  refl : forall x, eqv x x
  symm : forall {x y}, eqv x y -> eqv y x
  trans : forall {x y z}, eqv x y -> eqv y z -> eqv x z
  decEqv : forall x y, Decidable (eqv x y)

@[reducible] def setoidEq {α : Type u} [DecidableSetoid α] (x y : α) : Prop :=
  DecidableSetoid.eqv x y

@[reducible] def setoidNe {α : Type u} [DecidableSetoid α] (x y : α) : Prop :=
  Not (setoidEq x y)

instance instDecidableSetoidEq {α : Type u} [DecidableSetoid α] (x y : α) :
    Decidable (setoidEq x y) :=
  DecidableSetoid.decEqv x y

theorem setoidEq_refl {α : Type u} [DecidableSetoid α] (x : α) :
    setoidEq x x :=
  DecidableSetoid.refl x

theorem setoidEq_symm {α : Type u} [DecidableSetoid α] {x y : α}
    (h : setoidEq x y) : setoidEq y x :=
  DecidableSetoid.symm h

theorem setoidEq_trans {α : Type u} [DecidableSetoid α] {x y z : α}
    (hxy : setoidEq x y) (hyz : setoidEq y z) : setoidEq x z :=
  DecidableSetoid.trans hxy hyz

def DecidableSetoid.ofEq (α : Type u) [DecidableEq α] : DecidableSetoid α where
  eqv := Eq
  refl := fun _ => rfl
  symm := Eq.symm
  trans := Eq.trans
  decEqv := fun x y => inferInstanceAs (Decidable (x = y))

@[reducible] instance intDecidableSetoid : DecidableSetoid Int :=
  DecidableSetoid.ofEq Int

theorem int_setoidEq_iff (x y : Int) : setoidEq x y <-> x = y := by
  change DecidableSetoid.eqv x y <-> x = y
  rfl

theorem int_setoidNe_iff (x y : Int) : setoidNe x y <-> x ≠ y := by
  simp only [setoidNe, int_setoidEq_iff]

/-- Lean representation of the three-way decision returned by the Coq
    `OrderedTypeFullDecFacts.dec` functor. -/
inductive OrderDecision {α : Type u} [LT α] [DecidableSetoid α]
    (x y : α) : Type where
  | lt (h : x < y)
  | gt (h : x > y)
  | eq (h : setoidEq x y)

/-- Decision interface supplied by Coq's `OrderedTypeFull'` facts.  Keeping it
as a class allows equality to be a genuine setoid relation rather than forcing
it to be Lean's native equality. -/
class OrderedTypeFullDecision (α : Type u) [LT α] [LE α]
    [DecidableSetoid α] where
  dec : forall x y : α, OrderDecision x y
  ltDec : forall x y : α, Decidable (x < y)
  leDec : forall x y : α, Decidable (x ≤ y)
  gtDec : forall x y : α, Decidable (x > y)
  geDec : forall x y : α, Decidable (x ≥ y)
  ltGeDec : forall x y : α, Sumbool (x < y) (x ≥ y)
  ltLeDec : forall x y : α, Sumbool (x < y) (y ≤ x)
  leGtDec : forall x y : α, Sumbool (x ≤ y) (x > y)
  gtLeDec : forall x y : α, Sumbool (x > y) (x ≤ y)
  geLtDec : forall x y : α, Sumbool (x ≥ y) (x < y)

instance intOrderedTypeFullDecision : OrderedTypeFullDecision Int where
  dec := fun x y =>
    if hlt : x < y then
      .lt hlt
    else if hgt : x > y then
      .gt hgt
    else
      .eq (by
        change x = y
        omega)
  ltDec := fun x y => inferInstanceAs (Decidable (x < y))
  leDec := fun x y => inferInstanceAs (Decidable (x ≤ y))
  gtDec := fun x y => inferInstanceAs (Decidable (x > y))
  geDec := fun x y => inferInstanceAs (Decidable (x ≥ y))
  ltGeDec := fun x y => if h : x < y then .left h else .right (by omega)
  ltLeDec := fun x y => if h : x < y then .left h else .right (by omega)
  leGtDec := fun x y => if h : x ≤ y then .left h else .right (by omega)
  gtLeDec := fun x y => if h : x > y then .left h else .right (by omega)
  geLtDec := fun x y => if h : x ≥ y then .left h else .right (by omega)

def order_dec {α : Type u} [LT α] [LE α] [DecidableSetoid α]
    [OrderedTypeFullDecision α] (x y : α) :
    OrderDecision x y :=
  OrderedTypeFullDecision.dec x y

/- Source-shaped facade for the output of `OrderedTypeFullDecFacts`. -/
namespace OrderedTypeFullDecFacts

def dec {α : Type u} [LT α] [LE α] [DecidableSetoid α]
    [OrderedTypeFullDecision α] (x y : α) :
    OrderDecision x y :=
  order_dec x y

def lt_dec {α : Type u} [LT α] [LE α] [DecidableSetoid α]
    [OrderedTypeFullDecision α] (x y : α) : Decidable (x < y) :=
  OrderedTypeFullDecision.ltDec x y

def le_dec {α : Type u} [LT α] [LE α] [DecidableSetoid α]
    [OrderedTypeFullDecision α] (x y : α) : Decidable (x ≤ y) :=
  OrderedTypeFullDecision.leDec x y

def gt_dec {α : Type u} [LT α] [LE α] [DecidableSetoid α]
    [OrderedTypeFullDecision α] (x y : α) : Decidable (x > y) :=
  OrderedTypeFullDecision.gtDec x y

def ge_dec {α : Type u} [LT α] [LE α] [DecidableSetoid α]
    [OrderedTypeFullDecision α] (x y : α) : Decidable (x ≥ y) :=
  OrderedTypeFullDecision.geDec x y

def lt_ge_dec {α : Type u} [LT α] [LE α] [DecidableSetoid α]
    [OrderedTypeFullDecision α] (x y : α) :
    Sumbool (x < y) (x ≥ y) :=
  OrderedTypeFullDecision.ltGeDec x y

def lt_le_dec {α : Type u} [LT α] [LE α] [DecidableSetoid α]
    [OrderedTypeFullDecision α] (x y : α) :
    Sumbool (x < y) (y ≤ x) :=
  OrderedTypeFullDecision.ltLeDec x y

def le_gt_dec {α : Type u} [LT α] [LE α] [DecidableSetoid α]
    [OrderedTypeFullDecision α] (x y : α) :
    Sumbool (x ≤ y) (x > y) :=
  OrderedTypeFullDecision.leGtDec x y

def gt_le_dec {α : Type u} [LT α] [LE α] [DecidableSetoid α]
    [OrderedTypeFullDecision α] (x y : α) :
    Sumbool (x > y) (x ≤ y) :=
  OrderedTypeFullDecision.gtLeDec x y

def ge_lt_dec {α : Type u} [LT α] [LE α] [DecidableSetoid α]
    [OrderedTypeFullDecision α] (x y : α) :
    Sumbool (x ≥ y) (x < y) :=
  OrderedTypeFullDecision.geLtDec x y

end OrderedTypeFullDecFacts

end AUXLib
