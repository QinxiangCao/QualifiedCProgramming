import AUXLib.ListLib.Sequence
import Std.Tactic
import Lean.Elab.Tactic.Omega

namespace AUXLib

universe u v

private def nat_factorial : Nat -> Nat
  | 0 => 1
  | n + 1 => nat_factorial n * (n + 1)

def factorial (n : Int) : Int :=
  Int.ofNat (nat_factorial n.toNat)

theorem factorial_inc (n : Int) (hn : n >= 0) :
    factorial (n + 1) = factorial n * (n + 1) := by
  unfold factorial
  have htoNat : (n + 1).toNat = n.toNat + 1 := by omega
  rw [htoNat]
  simp only [nat_factorial]
  have hnback : Int.ofNat n.toNat = n := Int.toNat_of_nonneg hn
  change (↑(nat_factorial n.toNat * (n.toNat + 1)) : Int) =
    (↑(nat_factorial n.toNat) : Int) * (n + 1)
  rw [Int.natCast_mul]
  have hcast : (↑(n.toNat + 1) : Int) = n + 1 := by
    rw [show n.toNat + 1 = Nat.succ n.toNat by omega, Int.natCast_succ]
    change Int.ofNat n.toNat + 1 = n + 1
    rw [hnback]
  rw [hcast]

def zeros (n : Int) : List Int :=
  «repeat» 0 n.toNat

def sum (l : List Int) : Int :=
  l.foldr (.+.) 0

theorem sum_app (l1 l2 : List Int) :
    sum (l1 ++ l2) = sum l1 + sum l2 := by
  induction l1 with
  | nil => simp [sum]
  | cons x xs ih =>
      change x + sum (xs ++ l2) = x + sum xs + sum l2
      rw [ih]
      omega

theorem sum_bound (b : Int) (l : List Int)
    (hbound : forall i, 0 <= i -> 0 <= Znth i l 0 ∧ Znth i l 0 <= b) :
    0 <= sum l ∧ sum l <= Int.ofNat l.length * b := by
  induction l with
  | nil => simp [sum]
  | cons a l ih =>
      have ha : 0 <= a ∧ a <= b := by
        simpa [Znth] using hbound 0 (by omega)
      have htail : forall i, 0 <= i ->
          0 <= Znth i l 0 ∧ Znth i l 0 <= b := by
        intro i hi
        have h := hbound (i + 1) (by omega)
        rw [Znth_cons (d := 0) (n := i + 1) (a := a) (l := l) (by omega)] at h
        simpa using h
      have hsum := ih htail
      constructor
      · change 0 <= a + sum l
        omega
      · change a + sum l <= Int.ofNat (l.length + 1) * b
        have hcast : Int.ofNat (l.length + 1) = Int.ofNat l.length + 1 := by
          exact (Int.ofNat_add_one_out l.length).symm
        rw [hcast, Int.add_mul]
        omega

theorem sum_bound_lt (b : Int) (l : List Int) (hne : l ≠ [])
    (hbound : forall i, 0 <= i ∧ i < Int.ofNat l.length ->
      0 <= Znth i l 0 ∧ Znth i l 0 < b) :
    0 <= sum l ∧ sum l < Int.ofNat l.length * b := by
  induction l with
  | nil => exact False.elim (hne rfl)
  | cons a l ih =>
      have ha : 0 <= a ∧ a < b := by
        have hzero : (0 : Int) < Int.ofNat (a :: l).length := by simp
        simpa [Znth] using hbound 0 ⟨by omega, hzero⟩
      have htail : forall i, 0 <= i ∧ i < Int.ofNat l.length ->
          0 <= Znth i l 0 ∧ Znth i l 0 < b := by
        intro i hi
        have hlen : i + 1 < Int.ofNat (a :: l).length := by
          simp only [List.length_cons]
          have hcast : Int.ofNat (l.length + 1) = Int.ofNat l.length + 1 :=
            (Int.ofNat_add_one_out l.length).symm
          rw [hcast]
          omega
        have h := hbound (i + 1) ⟨by omega, hlen⟩
        rw [Znth_cons (d := 0) (n := i + 1) (a := a) (l := l) (by omega)] at h
        simpa using h
      constructor
      · change 0 <= a + sum l
        by_cases hl : l = []
        · subst l
          simp [sum]
          exact ha.1
        · have hsum := ih hl htail
          omega
      · change a + sum l < Int.ofNat (l.length + 1) * b
        have hcast : Int.ofNat (l.length + 1) = Int.ofNat l.length + 1 :=
          (Int.ofNat_add_one_out l.length).symm
        rw [hcast, Int.add_mul]
        by_cases hl : l = []
        · subst l
          change a + 0 < 0 * b + 1 * b
          omega
        · have hsum := ih hl htail
          omega
