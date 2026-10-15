import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.Prime

namespace SimpleC.EE.LLM_bench.Algorithms.integer_divide.integer_divide_lib
open AUXLib
export AUXLib.Prime (prime prime_alt prime_ge_2)

/-- Coq `Sorting.Sorted.HdRel`: only the relation to the first list element. -/
inductive HdRel {A : Type u} (R : A → A → Prop) (a : A) : List A → Prop where
  | HdRel_nil : HdRel R a []
  | HdRel_cons (b : A) (l : List A) : R a b → HdRel R a (b :: l)

/-- Coq `Sorting.Sorted.Sorted`, preserving both constructor arguments. -/
inductive Sorted {A : Type u} (R : A → A → Prop) : List A → Prop where
  | Sorted_nil : Sorted R []
  | Sorted_cons (a : A) (l : List A) : Sorted R l → HdRel R a l → Sorted R (a :: l)

def PrimeFactorization (original : Int) (factors : List Int) : Prop :=
  Forall prime factors ∧ Sorted (· ≤ ·) factors ∧
  factors.foldr (· * ·) 1 = original ∧
  ∀ q : Int, q ∈ factors ↔ prime q ∧ Z.divide q original

def FactorizationProgress (original : Int) (factors : List Int)
    (remaining candidate : Int) : Prop :=
  factors.foldr (· * ·) 1 * remaining = original ∧
  Forall prime factors ∧ Sorted (· ≤ ·) factors ∧
  Forall (fun factor => factor ≤ candidate) factors ∧
  ∀ d : Int, 2 ≤ d ∧ d < candidate → ¬ Z.divide d remaining

theorem prime_product_exceeds_length__progress_transitions (factors : List Int)
    (h : Forall prime factors) : Zlength factors < factors.foldr (· * ·) 1 := by
  induction h with
  | nil => simp [Zlength]
  | @cons factor factors hf hfs ih =>
    simp only [Zlength_cons, List.foldr_cons]
    have hf2 := prime_ge_2 factor hf
    have hl : 0 ≤ Zlength factors := by simp [Zlength]
    have hm := Int.mul_le_mul_of_nonneg_right hf2 (show 0 ≤ factors.foldr (· * ·) 1 by omega)
    omega

theorem fold_right_mul_snoc__progress_transitions (factors : List Int) (factor : Int) :
    (factors ++ [factor]).foldr (· * ·) 1 = factors.foldr (· * ·) 1 * factor := by
  induction factors with
  | nil => simp
  | cons head tail ih => simp only [List.cons_append, List.foldr_cons, ih, Int.mul_assoc]

theorem sorted_snoc_le__progress_transitions (factors : List Int) (factor : Int)
    (hs : Sorted (· ≤ ·) factors) (hb : Forall (fun x => x ≤ factor) factors) :
    Sorted (· ≤ ·) (factors ++ [factor]) := by
  induction hs with
  | Sorted_nil => exact .Sorted_cons factor [] .Sorted_nil .HdRel_nil
  | Sorted_cons head tail ht hh ih =>
    cases hb with
    | cons hhead htail =>
      apply Sorted.Sorted_cons head (tail ++ [factor]) (ih htail)
      cases tail with
      | nil => exact .HdRel_cons factor [] hhead
      | cons next rest =>
        cases hh with
        | HdRel_cons _ _ h => exact .HdRel_cons next (rest ++ [factor]) h

theorem factorization_progress_room__progress_transitions
    (original : Int) (factors : List Int) (remaining candidate : Int)
    (hc : 2 ≤ candidate) (hr : candidate ≤ remaining)
    (hp : FactorizationProgress original factors remaining candidate) :
    Zlength factors + 1 < original := by
  obtain ⟨hprod, hprime, _⟩ := hp
  have hb := prime_product_exceeds_length__progress_transitions factors hprime
  have hl : 0 ≤ Zlength factors := by simp [Zlength]
  have hm := Int.mul_le_mul_of_nonneg_left (show 2 ≤ remaining by omega)
    (show 0 ≤ factors.foldr (· * ·) 1 by omega)
  omega

theorem factorization_progress_extract__progress_transitions
    (original : Int) (factors : List Int) (remaining candidate : Int)
    (hr : 1 ≤ remaining) (hc : 2 ≤ candidate) (hcr : candidate ≤ remaining)
    (hmod : Z.rem remaining candidate = 0)
    (hp : FactorizationProgress original factors remaining candidate) :
    FactorizationProgress original (factors ++ [candidate])
      (Z.quot remaining candidate) candidate ∧
    (Z.quot remaining candidate = 1 ∨ candidate ≤ Z.quot remaining candidate) := by
  obtain ⟨hprod, hprimes, hsorted, hbounds, hexc⟩ := hp
  have hdiv : remaining = candidate * Z.quot remaining candidate := by
    have h := Z.quot_rem remaining candidate (by omega)
    omega
  have hprime : prime candidate := by
    apply (prime_alt candidate).mp
    refine ⟨by omega, ?_⟩
    intro d hd hdvd
    apply hexc d (by omega)
    obtain ⟨q, hq⟩ := hdvd
    exact ⟨q * Z.quot remaining candidate, by grind⟩
  have hqpos : 1 ≤ Z.quot remaining candidate :=
    Z.quot_le_lower_bound remaining candidate 1 (by omega) (by omega)
  have hcases : Z.quot remaining candidate = 1 ∨ candidate ≤ Z.quot remaining candidate := by
    by_cases h1 : Z.quot remaining candidate = 1
    · exact .inl h1
    · right
      apply Classical.byContradiction
      intro hlt
      apply hexc (Z.quot remaining candidate) (by omega)
      exact ⟨candidate, hdiv⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hcases⟩
  · rw [fold_right_mul_snoc__progress_transitions]
    grind
  · apply Forall.iff_forall_mem.mpr
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hprimes.mem hq
    · have heq := List.mem_singleton.mp hq
      subst q
      exact hprime
  · exact sorted_snoc_le__progress_transitions factors candidate hsorted hbounds
  · apply Forall.iff_forall_mem.mpr
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hbounds.mem hq
    · have := List.mem_singleton.mp hq; omega
  · intro d hd hdvd
    apply hexc d hd
    obtain ⟨q, hq⟩ := hdvd
    exact ⟨candidate * q, by grind⟩

theorem factorization_progress_advance__progress_transitions
    (original : Int) (factors : List Int) (remaining candidate : Int)
    (hc : 2 ≤ candidate) (hm : Z.rem remaining candidate ≠ 0)
    (hp : FactorizationProgress original factors remaining candidate) :
    FactorizationProgress original factors remaining (candidate + 1) := by
  obtain ⟨hprod, hprimes, hs, hb, hexc⟩ := hp
  refine ⟨hprod, hprimes, hs, ?_, ?_⟩
  · apply Forall.iff_forall_mem.mpr
    intro q hq
    have := hb.mem hq
    omega
  · intro d hd hdvd
    by_cases hlt : d < candidate
    · exact hexc d (by omega) hdvd
    · have heq : d = candidate := by omega
      subst d
      exact hm ((Z.rem_divide remaining candidate (by omega)).2 hdvd)

private theorem prime_mul_dvd {q a b : Int} (hq : prime q) (hd : q ∣ a * b) :
    q ∣ a ∨ q ∣ b := by
  by_cases hqa : q ∣ a
  · exact .inl hqa
  · right
    have hq2 := prime_ge_2 q hq
    have hgpos := Int.gcd_pos_of_ne_zero_left a (show q ≠ 0 by omega)
    have hgle := Int.gcd_le_left a (show 0 < q by omega)
    have hgd := Int.gcd_dvd_left q a
    have hgda := Int.gcd_dvd_right q a
    have hgne : (Int.gcd q a : Int) ≠ q := by
      intro heq
      exact hqa (heq ▸ hgda)
    have hg1 : Int.gcd q a = 1 := by
      apply Classical.byContradiction
      intro hn
      exact ((prime_alt q).mpr hq).2 (Int.gcd q a) (by omega) ((Z.divide_iff_dvd _ _).2 hgd)
    have hm := (Int.dvd_gcd_mul_iff_dvd_mul (k := q) (n := a) (m := b)).2 hd
    simpa [hg1] using hm

theorem prime_divides_factor_product_iff_in__final_result (q : Int) (factors : List Int)
    (hq : prime q) (hall : Forall prime factors) :
    Z.divide q (factors.foldr (· * ·) 1) ↔ q ∈ factors := by
  rw [Z.divide_iff_dvd]
  induction hall with
  | nil =>
    simp only [List.foldr_nil, List.not_mem_nil, iff_false]
    intro hd
    have := Int.le_of_dvd (show (0 : Int) < 1 by decide) hd
    have := prime_ge_2 q hq
    omega
  | @cons a factors ha hall ih =>
    simp only [List.foldr_cons, List.mem_cons]
    constructor
    · intro hd
      rcases prime_mul_dvd hq hd with hda | hdf
      · left
        have hq2 := prime_ge_2 q hq
        have ha2 := prime_ge_2 a ha
        have hle := Int.le_of_dvd (show 0 < a by omega) hda
        apply Classical.byContradiction
        intro hne
        exact ((prime_alt a).mpr ha).2 q (by omega) ((Z.divide_iff_dvd _ _).2 hda)
      · exact .inr (ih.1 hdf)
    · rintro (heq | hin)
      · subst a
        exact Int.dvd_mul_right _ _
      · exact Int.dvd_trans (ih.2 hin) (Int.dvd_mul_left _ _)

theorem factorization_progress_complete__final_result
    (original : Int) (factors : List Int) (remaining candidate : Int)
    (hr : 1 ≤ remaining) (hfinished : remaining = 1 ∨ remaining < candidate)
    (hp : FactorizationProgress original factors remaining candidate) :
    PrimeFactorization original factors := by
  obtain ⟨hprod, hprimes, hs, hb, hexc⟩ := hp
  have hr1 : remaining = 1 := by
    rcases hfinished with h1 | hlt
    · exact h1
    · apply Classical.byContradiction
      intro hne
      exact hexc remaining (by omega) ⟨1, by simp⟩
  subst remaining
  simp only [Int.mul_one] at hprod
  refine ⟨hprimes, hs, hprod, ?_⟩
  intro q
  constructor
  · intro hq
    have hprime := hprimes.mem hq
    refine ⟨hprime, ?_⟩
    rw [← hprod]
    exact (prime_divides_factor_product_iff_in__final_result q factors hprime hprimes).2 hq
  · rintro ⟨hprime, hdiv⟩
    rw [← hprod] at hdiv
    exact (prime_divides_factor_product_iff_in__final_result q factors hprime hprimes).1 hdiv

end SimpleC.EE.LLM_bench.Algorithms.integer_divide.integer_divide_lib
namespace SimpleC.EE.LLM_bench.Algorithms.integer_divide
export integer_divide_lib (PrimeFactorization FactorizationProgress)
end SimpleC.EE.LLM_bench.Algorithms.integer_divide
