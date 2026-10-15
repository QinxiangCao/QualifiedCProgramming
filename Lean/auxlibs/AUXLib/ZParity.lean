import AUXLib.Arithmetic

/-! The reached boolean parity interface from Coq.ZArith.BinIntDef.
Coq inspects the last binary digit; divisibility by two gives the same result
for positive, zero, and negative integers. -/
namespace Z

def even (n : Int) : Bool := decide (n % 2 = 0)

def odd (n : Int) : Bool := decide (n % 2 = 1)

theorem even_spec (n : Int) : even n = true ↔ ∃ k : Int, n = 2 * k := by
  simp only [even, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨n / 2, by omega⟩
  · rintro ⟨k, rfl⟩
    omega

theorem odd_spec (n : Int) : odd n = true ↔ ∃ k : Int, n = 2 * k + 1 := by
  simp only [odd, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨n / 2, by omega⟩
  · rintro ⟨k, rfl⟩
    omega

end Z

example : Z.even 0 = true ∧ Z.even (-4) = true ∧ Z.even (-3) = false := by decide
