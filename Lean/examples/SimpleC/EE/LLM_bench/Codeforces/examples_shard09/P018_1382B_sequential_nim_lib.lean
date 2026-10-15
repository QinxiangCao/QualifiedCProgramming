import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ZParity
import AUXLib.ListLib.LengthCompat
import MaxMinLib.Interface

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_lib
open AUXLib

def LeadingOnes (piles : List Int) (k : Int) : Prop :=
  (0 ≤ k ∧ k ≤ Zlength piles) ∧
  (∀ i : Int, (0 ≤ i ∧ i < k) → Znth i piles 0 = 1) ∧
  (k = Zlength piles ∨ Znth k piles 0 ≠ 1)

def FirstWins (piles : List Int) : Prop :=
  ∃ k, LeadingOnes piles k ∧
    ((k = Zlength piles ∧ Z.even k = false) ∨ (k < Zlength piles ∧ Z.even k = true))

def Pre (piles : List Int) : Prop := True

def Spec (piles : List Int) (out : Int) : Prop :=
  (out = 1 ∧ FirstWins piles) ∨ (out = 0 ∧ ¬ FirstWins piles)

def SolverReturnBridge (out ret : Int) : Prop :=
  (out = 1 ∧ ret = 1) ∨ (out = 0 ∧ ret = 0)


theorem leading_ones_unique__return_semantics (piles : List Int) (k1 k2 : Int)
    (h1 : LeadingOnes piles k1) (h2 : LeadingOnes piles k2) : k1 = k2 := by
  rcases h1 with ⟨⟨h10, h1n⟩, hp1, he1⟩
  rcases h2 with ⟨⟨h20, h2n⟩, hp2, he2⟩
  by_cases hlt : k1 < k2
  · have hp := hp2 k1 ⟨h10, hlt⟩
    rcases he1 with he1 | he1
    · omega
    · exact False.elim (he1 hp)
  · by_cases hgt : k2 < k1
    · have hp := hp1 k2 ⟨h20, hgt⟩
      rcases he2 with he2 | he2
      · omega
      · exact False.elim (he2 hp)
    · omega

theorem even_of_nonnegative_rem_zero__return_semantics (n : Int)
    (hn : 0 ≤ n) (hr : Z.rem n 2 = 0) : Z.even n = true := by
  apply (Z.even_spec n).mpr
  rcases (Z.rem_divide n 2 (by decide)).mp hr with ⟨k, hk⟩
  exact ⟨k, by omega⟩

theorem odd_of_nonnegative_rem_nonzero__return_semantics (n : Int)
    (hn : 0 ≤ n) (hr : Z.rem n 2 ≠ 0) : Z.even n = false := by
  cases he : Z.even n with
  | false => rfl
  | true =>
    rcases (Z.even_spec n).mp he with ⟨k, hk⟩
    exact False.elim (hr ((Z.rem_divide n 2 (by decide)).mpr ⟨k, by omega⟩))

theorem even_of_nonnegative_rem_not_one__return_semantics (n : Int)
    (hn : 0 ≤ n) (hr : Z.rem n 2 ≠ 1) : Z.even n = true := by
  have hb := AUXLib.rem_nonneg_bounds n 2 hn (by omega)
  exact even_of_nonnegative_rem_zero__return_semantics n hn (by omega)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P018_1382B_sequential_nim_lib
