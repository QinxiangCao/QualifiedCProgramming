import Std.Tactic

namespace AUXLib

universe u

abbrev EqDec (A : Type u) := DecidableEq A

def equiv_decb {A : Type u} [EqDec A] (x y : A) : Bool :=
  decide (x = y)

@[simp] theorem equiv_decb_true_eq {A : Type u} [EqDec A] (x y : A) :
    equiv_decb x y = true -> x = y := by
  simp [equiv_decb]

@[simp] theorem eq_equiv_decb_true {A : Type u} [EqDec A] (x y : A) :
    x = y -> equiv_decb x y = true := by
  simp [equiv_decb]

@[simp] theorem equiv_decb_false_neq {A : Type u} [EqDec A] (x y : A) :
    equiv_decb x y = false -> x ≠ y := by
  simp [equiv_decb]

@[simp] theorem neq_equiv_decb_false {A : Type u} [EqDec A] (x y : A) :
    x ≠ y -> equiv_decb x y = false := by
  simp [equiv_decb]

end AUXLib
