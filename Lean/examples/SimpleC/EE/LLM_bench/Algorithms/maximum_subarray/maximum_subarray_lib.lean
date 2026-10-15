import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_lib
open AUXLib

def max_Z (a b : Int) : Int := max a b

def SubarraySum (l : List Int) (lo hi s : Int) : Prop :=
  0 ≤ lo ∧ lo < hi ∧ hi ≤ Zlength l ∧ s = sum (sublist lo hi l)

def MaxSuffixSumPrefix (l : List Int) (i ans : Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·) (fun lo : Int => 0 ≤ lo ∧ lo < i)
    (fun lo => sum (sublist lo i l)) ans

def MaxSubarraySumPrefix (l : List Int) (i ans : Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·)
    (fun p : Int × Int => let (lo, hi) := p; 0 ≤ lo ∧ lo < hi ∧ hi ≤ i)
    (fun p : Int × Int => let (lo, hi) := p; sum (sublist lo hi l)) ans

theorem sum_sublist_single (l : List Int) (n : Int)
    (hn : 0 ≤ n ∧ n < Zlength l) :
    sum (sublist n (n + 1) l) = Znth n l 0 := by
  rw [sublist_single 0 n l hn]
  simp [sum]

theorem sum_sublist_snoc (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi + 1 ≤ Zlength l) :
    sum (sublist lo (hi + 1) l) = sum (sublist lo hi l) + Znth hi l 0 := by
  rw [sublist_split lo (hi + 1) hi l hlo (by omega), sum_app,
    sum_sublist_single l hi (by omega)]

theorem MaxSuffixSumPrefix_single (l : List Int) (hlen : 1 ≤ Zlength l) :
    MaxSuffixSumPrefix l 1 (Znth 0 l 0) := by
  refine ⟨0, ⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩
  · intro b hb
    have : b = 0 := by change 0 ≤ b ∧ b < 1 at hb; omega
    subst b
    exact le_rfl
  · exact sum_sublist_single l 0 (by omega)

theorem MaxSubarraySumPrefix_single (l : List Int) (hlen : 1 ≤ Zlength l) :
    MaxSubarraySumPrefix l 1 (Znth 0 l 0) := by
  refine ⟨(0, 1), ⟨⟨by omega, by omega, by omega⟩, ?_⟩, ?_⟩
  · intro ⟨lo, hi⟩ hb
    change 0 ≤ lo ∧ lo < hi ∧ hi ≤ 1 at hb
    have hlo : lo = 0 := by omega
    have hhi : hi = 1 := by omega
    subst lo; subst hi
    exact le_rfl
  · exact sum_sublist_single l 0 (by omega)

theorem MaxSuffixSumPrefix_step (l : List Int) (i cur : Int)
    (hi : 0 ≤ i) (hlen : i + 1 ≤ Zlength l)
    (hcur : MaxSuffixSumPrefix l i cur) :
    MaxSuffixSumPrefix l (i + 1) (max_Z (Znth i l 0) (cur + Znth i l 0)) := by
  rcases hcur with ⟨a, ⟨ha, hmax⟩, heq⟩
  change 0 ≤ a ∧ a < i at ha
  change ∀ b, (0 ≤ b ∧ b < i) → sum (sublist b i l) ≤ sum (sublist a i l) at hmax
  change sum (sublist a i l) = cur at heq
  by_cases hle : Znth i l 0 ≤ cur + Znth i l 0
  · refine ⟨a, ⟨⟨ha.1, by omega⟩, ?_⟩, ?_⟩
    · intro b hb
      change 0 ≤ b ∧ b < i + 1 at hb
      change sum (sublist b (i + 1) l) ≤ sum (sublist a (i + 1) l)
      rw [sum_sublist_snoc l a i (by omega) hlen, heq]
      by_cases hbi : b = i
      · subst b
        rw [sum_sublist_single l i (by omega)]
        exact hle
      · rw [sum_sublist_snoc l b i (by omega) hlen]
        have := hmax b (by omega)
        omega
    · change sum (sublist a (i + 1) l) = max_Z _ _
      rw [sum_sublist_snoc l a i (by omega) hlen, heq]
      exact (max_eq_right hle).symm
  · refine ⟨i, ⟨⟨hi, by omega⟩, ?_⟩, ?_⟩
    · intro b hb
      change 0 ≤ b ∧ b < i + 1 at hb
      change sum (sublist b (i + 1) l) ≤ sum (sublist i (i + 1) l)
      rw [sum_sublist_single l i (by omega)]
      by_cases hbi : b = i
      · subst b
        rw [sum_sublist_single l i (by omega)]
      · rw [sum_sublist_snoc l b i (by omega) hlen]
        have := hmax b (by omega)
        omega
    · change sum (sublist i (i + 1) l) = max_Z _ _
      rw [sum_sublist_single l i (by omega)]
      exact (max_eq_left (by omega : cur + Znth i l 0 ≤ Znth i l 0)).symm

theorem MaxSubarraySumPrefix_step (l : List Int) (i res cur : Int)
    (hres : MaxSubarraySumPrefix l i res) (hcur : MaxSuffixSumPrefix l (i + 1) cur) :
    MaxSubarraySumPrefix l (i + 1) (max_Z res cur) := by
  rcases hres with ⟨⟨lo, hi⟩, ⟨hp, hmax⟩, heq⟩
  rcases hcur with ⟨s, ⟨hs, hsmax⟩, hseq⟩
  change 0 ≤ lo ∧ lo < hi ∧ hi ≤ i at hp
  change 0 ≤ s ∧ s < i + 1 at hs
  change ∀ p : Int × Int, (0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ i) →
    sum (sublist p.1 p.2 l) ≤ sum (sublist lo hi l) at hmax
  change ∀ b, (0 ≤ b ∧ b < i + 1) → sum (sublist b (i + 1) l) ≤ sum (sublist s (i + 1) l) at hsmax
  change sum (sublist lo hi l) = res at heq
  change sum (sublist s (i + 1) l) = cur at hseq
  by_cases hle : cur ≤ res
  · refine ⟨(lo, hi), ⟨⟨hp.1, hp.2.1, by omega⟩, ?_⟩, ?_⟩
    · intro ⟨blo, bhi⟩ hb
      change 0 ≤ blo ∧ blo < bhi ∧ bhi ≤ i + 1 at hb
      change sum (sublist blo bhi l) ≤ sum (sublist lo hi l)
      by_cases hbi : bhi = i + 1
      · subst bhi
        have := hsmax blo (by omega)
        omega
      · exact hmax (blo, bhi) (by dsimp; omega)
    · change sum (sublist lo hi l) = max_Z res cur
      rw [heq]
      exact (max_eq_left hle).symm
  · refine ⟨(s, i + 1), ⟨⟨hs.1, hs.2, le_rfl⟩, ?_⟩, ?_⟩
    · intro ⟨blo, bhi⟩ hb
      change 0 ≤ blo ∧ blo < bhi ∧ bhi ≤ i + 1 at hb
      change sum (sublist blo bhi l) ≤ sum (sublist s (i + 1) l)
      by_cases hbi : bhi = i + 1
      · subst bhi
        exact hsmax blo (by omega)
      · have := hmax (blo, bhi) (by dsimp; omega)
        dsimp at this
        omega
    · change sum (sublist s (i + 1) l) = max_Z res cur
      rw [hseq]
      exact (max_eq_right (by omega : res ≤ cur)).symm

theorem sum_upper_bound (l : List Int) (b : Int) (hb : 0 ≤ b)
    (hbound : ∀ i, (0 ≤ i ∧ i < Zlength l) → Znth i l 0 ≤ b) :
    sum l ≤ Zlength l * b := by
  induction l with
  | nil => simp [sum, Zlength]
  | cons a l ih =>
    have ha : a ≤ b := by
      have := hbound 0 (by simp [Zlength])
      simpa [Znth] using this
    have htail : ∀ i, (0 ≤ i ∧ i < Zlength l) → Znth i l 0 ≤ b := by
      intro i hi
      have := hbound (i + 1) (by rw [Zlength_cons]; omega)
      rw [Znth_cons (d := 0) (n := i + 1) (a := a) (l := l) (by omega)] at this
      simpa using this
    have hsum := ih htail
    change a + sum l ≤ Zlength (a :: l) * b
    rw [Zlength_cons, Int.add_mul]
    omega

theorem sum_sublist_upper_bound (l : List Int) (lo hi n b : Int)
    (hb : 0 ≤ b) (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ n)
    (hn : n ≤ Zlength l)
    (hbound : ∀ k, (0 ≤ k ∧ k < n) → Znth k l 0 ≤ b) :
    sum (sublist lo hi l) ≤ (hi - lo) * b := by
  have hlen : Zlength (sublist lo hi l) = hi - lo := by
    unfold Zlength
    rw [sublist_length lo hi l hlo (by omega)]
    exact Int.toNat_of_nonneg (by omega)
  rw [← hlen]
  apply sum_upper_bound _ b hb
  intro j hj
  rw [hlen] at hj
  rw [Znth_sublist 0 lo j hi l hlo.1 hj]
  exact hbound (j + lo) (by omega)

theorem MaxSuffixSumPrefix_upper_bound (l : List Int) (i ans n : Int)
    (hi : 0 ≤ i ∧ i ≤ n) (hn : n ≤ Zlength l) (hnmax : n ≤ 100000)
    (hbound : ∀ k, (0 ≤ k ∧ k < n) → Znth k l 0 ≤ 10000)
    (hmax : MaxSuffixSumPrefix l i ans) : ans ≤ 1000000000 := by
  rcases hmax with ⟨lo, ⟨hlo, _⟩, heq⟩
  change 0 ≤ lo ∧ lo < i at hlo
  change sum (sublist lo i l) = ans at heq
  have := sum_sublist_upper_bound l lo i n 10000 (by omega) (by omega) hi.2 hn hbound
  omega

end SimpleC.EE.LLM_bench.Algorithms.maximum_subarray.maximum_subarray_lib
