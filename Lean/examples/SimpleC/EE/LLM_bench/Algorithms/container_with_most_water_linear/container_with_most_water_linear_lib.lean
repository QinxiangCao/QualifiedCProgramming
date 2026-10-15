import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
namespace SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear.container_with_most_water_linear_lib
open AUXLib

def LinearContainerHeight (l : List Int) (i j : Int) : Int := min (Znth i l 0) (Znth j l 0)
def LinearContainerArea (l : List Int) (i j : Int) : Int := (j-i) * LinearContainerHeight l i j
def LinearContainerPair (l : List Int) (i j : Int) : Prop := 0 ≤ i ∧ i < j ∧ j < Zlength l

def MaximumContainerArea (l : List Int) (ans : Int) : Prop :=
  (∃ i j, LinearContainerPair l i j ∧ ans = LinearContainerArea l i j) ∧
  ∀ i j, LinearContainerPair l i j → LinearContainerArea l i j ≤ ans

def LinearContainerBest (l : List Int) (best : Int) : Prop :=
  best = 0 ∨ ∃ i j, LinearContainerPair l i j ∧ best = LinearContainerArea l i j

def LinearContainerRemaining (l : List Int) (left right i j : Int) : Prop :=
  LinearContainerPair l i j ∧ left ≤ i ∧ j ≤ right

def LinearContainerTwoPointerInvariant (l : List Int) (left right best : Int) : Prop :=
  LinearContainerBest l best ∧ ∀ i j, LinearContainerPair l i j →
    LinearContainerArea l i j ≤ best ∨ ∃ p q, LinearContainerRemaining l left right p q ∧
      LinearContainerArea l i j ≤ LinearContainerArea l p q

theorem linear_container_invariant_update_best__best_update
    (l : List Int) (left right old_best : Int)
    (h : LinearContainerTwoPointerInvariant l left right old_best)
    (hp : LinearContainerPair l left right) (hb : old_best < LinearContainerArea l left right) :
    LinearContainerTwoPointerInvariant l left right (LinearContainerArea l left right) := by
  refine ⟨Or.inr ⟨left, right, hp, rfl⟩, ?_⟩
  intro i j hij
  rcases h.2 i j hij with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

theorem linear_container_invariant_advance_left__pointer_transitions
    (l : List Int) (left right best : Int)
    (hn : ∀ k, (0 ≤ k ∧ k < Zlength l) → 0 ≤ Znth k l 0)
    (hc : LinearContainerPair l left right) (hh : Znth left l 0 < Znth right l 0)
    (hb : LinearContainerArea l left right ≤ best)
    (h : LinearContainerTwoPointerInvariant l left right best) :
    LinearContainerTwoPointerInvariant l (left+1) right best := by
  refine ⟨h.1, ?_⟩
  intro i j hij
  rcases h.2 i j hij with hijb | ⟨p, q, ⟨hpq, hlp, hqr⟩, hijpq⟩
  · exact Or.inl hijb
  · by_cases hp : left+1 ≤ p
    · exact Or.inr ⟨p, q, ⟨hpq, hp, hqr⟩, hijpq⟩
    · have heq : p = left := by omega
      subst p
      apply Or.inl
      apply Int.le_trans hijpq
      apply Int.le_trans ?_ hb
      have hnleft := hn left ⟨hc.1, by have := hc.2; omega⟩
      have hmin : min (Znth left l 0) (Znth q l 0) ≤ Znth left l 0 := Int.min_le_left _ _
      simp only [LinearContainerArea, LinearContainerHeight, Int.min_eq_left (Int.le_of_lt hh)]
      exact Int.le_trans (Int.mul_le_mul_of_nonneg_left (c := q-left) hmin (by have := hpq.2.1; omega))
        (Int.mul_le_mul_of_nonneg_right (a := q-left) (b := right-left) (by omega) hnleft)

theorem linear_container_invariant_retreat_right__pointer_transitions
    (l : List Int) (left right best : Int)
    (hn : ∀ k, (0 ≤ k ∧ k < Zlength l) → 0 ≤ Znth k l 0)
    (hc : LinearContainerPair l left right) (hh : Znth left l 0 ≥ Znth right l 0)
    (hb : LinearContainerArea l left right ≤ best)
    (h : LinearContainerTwoPointerInvariant l left right best) :
    LinearContainerTwoPointerInvariant l left (right-1) best := by
  refine ⟨h.1, ?_⟩
  intro i j hij
  rcases h.2 i j hij with hijb | ⟨p, q, ⟨hpq, hlp, hqr⟩, hijpq⟩
  · exact Or.inl hijb
  · by_cases hq : q ≤ right-1
    · exact Or.inr ⟨p, q, ⟨hpq, hlp, hq⟩, hijpq⟩
    · have heq : q = right := by omega
      subst q
      apply Or.inl
      apply Int.le_trans hijpq
      apply Int.le_trans ?_ hb
      have hnright := hn right ⟨by have := hc.1; have := hc.2.1; omega, hc.2.2⟩
      have hmin : min (Znth p l 0) (Znth right l 0) ≤ Znth right l 0 := Int.min_le_right _ _
      simp only [LinearContainerArea, LinearContainerHeight, Int.min_eq_right hh]
      exact Int.le_trans (Int.mul_le_mul_of_nonneg_left (c := right-p) hmin (by have := hpq.2.1; omega))
        (Int.mul_le_mul_of_nonneg_right (a := right-p) (b := right-left) (by omega) hnright)

theorem linear_container_closed_invariant_maximum__final_result
    (l : List Int) (left right best : Int) (hc : left = right) (hl : 2 ≤ Zlength l)
    (hn : ∀ k, (0 ≤ k ∧ k < Zlength l) → 0 ≤ Znth k l 0)
    (h : LinearContainerTwoPointerInvariant l left right best) : MaximumContainerArea l best := by
  have hdom : ∀ i j, LinearContainerPair l i j → LinearContainerArea l i j ≤ best := by
    intro i j hij
    rcases h.2 i j hij with hb | ⟨p, q, ⟨⟨hp, hpq, hq⟩, hlp, hqr⟩, ha⟩
    · exact hb
    · omega
  refine ⟨?_, hdom⟩
  rcases h.1 with hb | hb
  · have hp : LinearContainerPair l 0 1 := ⟨by omega, by omega, by omega⟩
    refine ⟨0, 1, hp, ?_⟩
    have hd := hdom 0 1 hp
    have hn0 := hn 0 ⟨by omega, by omega⟩
    have hn1 := hn 1 ⟨by omega, by omega⟩
    simp only [LinearContainerArea, LinearContainerHeight] at *
    omega
  · exact hb

end SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear.container_with_most_water_linear_lib
namespace SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear
export container_with_most_water_linear_lib (LinearContainerHeight LinearContainerArea LinearContainerPair
  MaximumContainerArea LinearContainerBest LinearContainerRemaining LinearContainerTwoPointerInvariant)
end SimpleC.EE.LLM_bench.Algorithms.container_with_most_water_linear
