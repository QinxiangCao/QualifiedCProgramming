import Std.Tactic

namespace AUXLib

inductive positive : Type where
  | xH
  | xO (p : positive)
  | xI (p : positive)
  deriving DecidableEq, Repr

export positive (xH xO xI)

abbrev ident := positive

def ident_eq_dec (x y : ident) : Decidable (x = y) :=
  inferInstance

def ident_eqb (x y : ident) : Bool :=
  decide (x = y)

theorem ident_eqb_refl (x : ident) : ident_eqb x x = true := by
  simp [ident_eqb]

theorem ident_eqb_eq (x y : ident) : ident_eqb x y = true <-> x = y := by
  simp [ident_eqb]

abbrev var : Type := positive
abbrev func : Type := positive

def var_eqb (x y : var) : Bool :=
  decide (x = y)

def func_eqb (x y : func) : Bool :=
  decide (x = y)

def var_dec (x y : var) : Decidable (x = y) :=
  inferInstance

def func_dec (x y : var) : Decidable (x = y) :=
  inferInstance

theorem var_eqb_eq (x y : var) : var_eqb x y = true <-> x = y := by
  simp [var_eqb]

theorem var_eqb_neq (x y : var) : var_eqb x y = false <-> x ≠ y := by
  simp [var_eqb]

theorem func_eqb_eq (f1 f2 : func) : func_eqb f1 f2 = true <-> f1 = f2 := by
  simp [func_eqb]

theorem func_eqb_neq (f1 f2 : func) : func_eqb f1 f2 = false <-> f1 ≠ f2 := by
  simp [func_eqb]

theorem var_eqb_refl (x : var) : var_eqb x x = true := by
  simp [var_eqb]

theorem func_eqb_refl (f : func) : func_eqb f f = true := by
  simp [func_eqb]

syntax "var_destruct " term:max term:max : tactic

macro_rules
  | `(tactic| var_destruct $x:term $y:term) =>
      `(tactic| by_cases E : $x = $y)

end AUXLib
