import AUXLib.OrdersDecFact
import Lean.Util.CollectAxioms
import Std.Tactic
import Lean.Elab.Tactic.Omega

open AUXLib

#check order_dec
#check OrderedTypeFullDecFacts.dec
#check OrderedTypeFullDecFacts.lt_dec
#check OrderedTypeFullDecFacts.le_dec
#check OrderedTypeFullDecFacts.gt_dec
#check OrderedTypeFullDecFacts.ge_dec
#check OrderedTypeFullDecFacts.lt_ge_dec
#check OrderedTypeFullDecFacts.lt_le_dec
#check OrderedTypeFullDecFacts.le_gt_dec
#check OrderedTypeFullDecFacts.gt_le_dec
#check OrderedTypeFullDecFacts.ge_lt_dec

namespace SetoidFixture

structure Mod2Key where
  value : Int
deriving DecidableEq

instance : DecidableSetoid Mod2Key where
  eqv x y := x.value % 2 = y.value % 2
  refl _ := rfl
  symm := Eq.symm
  trans := Eq.trans
  decEqv x y := inferInstanceAs (Decidable (x.value % 2 = y.value % 2))

instance : LT Mod2Key where
  lt x y := x.value % 2 < y.value % 2

instance : LE Mod2Key where
  le x y := x.value % 2 <= y.value % 2

instance : DecidableLT Mod2Key := fun x y =>
  inferInstanceAs (Decidable (x.value % 2 < y.value % 2))

instance : DecidableLE Mod2Key := fun x y =>
  inferInstanceAs (Decidable (x.value % 2 <= y.value % 2))

instance : OrderedTypeFullDecision Mod2Key where
  dec := fun x y =>
    if hlt : x.value % 2 < y.value % 2 then
      .lt hlt
    else if hgt : x.value % 2 > y.value % 2 then
      .gt hgt
    else
      .eq (by
        change x.value % 2 = y.value % 2
        omega)
  ltDec := fun x y => inferInstanceAs (Decidable (x.value % 2 < y.value % 2))
  leDec := fun x y => inferInstanceAs (Decidable (x.value % 2 <= y.value % 2))
  gtDec := fun x y => inferInstanceAs (Decidable (x.value % 2 > y.value % 2))
  geDec := fun x y => inferInstanceAs (Decidable (x.value % 2 >= y.value % 2))
  ltGeDec := fun x y =>
    if h : x.value % 2 < y.value % 2 then
      .left h
    else
      .right (show y.value % 2 <= x.value % 2 by omega)
  ltLeDec := fun x y =>
    if h : x.value % 2 < y.value % 2 then
      .left h
    else
      .right (show y.value % 2 <= x.value % 2 by omega)
  leGtDec := fun x y =>
    if h : x.value % 2 <= y.value % 2 then
      .left h
    else
      .right (show y.value % 2 < x.value % 2 by omega)
  gtLeDec := fun x y =>
    if h : x.value % 2 > y.value % 2 then
      .left h
    else
      .right (show x.value % 2 <= y.value % 2 by omega)
  geLtDec := fun x y =>
    if h : x.value % 2 >= y.value % 2 then
      .left h
    else
      .right (show x.value % 2 < y.value % 2 by omega)

def zero : Mod2Key := ⟨0⟩
def two : Mod2Key := ⟨2⟩

example : zero ≠ two := by decide
example : setoidEq zero two := by decide

example : setoidEq zero two := by
  cases order_dec zero two with
  | lt h =>
      change (0 : Int) % 2 < 2 % 2 at h
      omega
  | gt h =>
      change (0 : Int) % 2 > 2 % 2 at h
      omega
  | eq h => exact h

end SetoidFixture

example : (1 : Int) < 2 := by
  cases OrderedTypeFullDecFacts.dec (1 : Int) 2 with
  | lt h => exact h
  | gt h => omega
  | eq h => omega

example : (2 : Int) > 1 := by
  cases OrderedTypeFullDecFacts.dec (2 : Int) 1 with
  | lt h => omega
  | gt h => exact h
  | eq h => omega

example : (2 : Int) = 2 := by
  cases OrderedTypeFullDecFacts.dec (2 : Int) 2 with
  | lt h => omega
  | gt h => omega
  | eq h => exact h

example : (1 : Int) < 2 := by
  exact of_decide_eq_true rfl

example : (2 : Int) ≤ 2 := by
  cases OrderedTypeFullDecFacts.le_dec (2 : Int) 2 with
  | isTrue h => exact h
  | isFalse h => omega

example : (2 : Int) > 1 := by
  cases OrderedTypeFullDecFacts.gt_dec (2 : Int) 1 with
  | isTrue h => exact h
  | isFalse h => omega

example : (2 : Int) ≥ 2 := by
  cases OrderedTypeFullDecFacts.ge_dec (2 : Int) 2 with
  | isTrue h => exact h
  | isFalse h => omega

example : (2 : Int) ≥ 2 := by
  cases OrderedTypeFullDecFacts.lt_ge_dec (2 : Int) 2 with
  | left h => omega
  | right h => exact h

example : (1 : Int) < 2 := by
  cases OrderedTypeFullDecFacts.lt_le_dec (1 : Int) 2 with
  | left h => exact h
  | right h => omega

example : (3 : Int) > 2 := by
  cases OrderedTypeFullDecFacts.le_gt_dec (3 : Int) 2 with
  | left h => omega
  | right h => exact h

example : (1 : Int) ≤ 2 := by
  cases OrderedTypeFullDecFacts.gt_le_dec (1 : Int) 2 with
  | left h => omega
  | right h => exact h

example : (1 : Int) < 2 := by
  cases OrderedTypeFullDecFacts.ge_lt_dec (1 : Int) 2 with
  | left h => omega
  | right h => exact h

#print axioms AUXLib.order_dec
#print axioms AUXLib.OrderedTypeFullDecFacts.ge_lt_dec
