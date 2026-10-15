import SimpleC.EE.LLM_bench.Algorithms.SelectionMinimum
import AUXLib.Sorting
import SimpleC.SL.SeparationLogic
import Init.Data.List.Nat.Pairwise
namespace SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_lib
open AUXLib
export AUXLib.Sorting (increasing_aux increasing lowerbound strict_lowerbound)

private theorem increasing_aux_iff (l : List Int) (x : Int) :
    increasing_aux l x ↔ lowerbound x l ∧ increasing l := by
  induction l generalizing x with
  | nil => simp [Sorting.increasing_aux, Sorting.lowerbound, Sorting.increasing]
  | cons y l ih =>
    constructor
    · intro h
      have hh := (ih y).mp h.2
      refine ⟨⟨h.1, ?_⟩, h.2⟩
      apply Sorting.lowerbound_iff x l |>.2
      intro z hz
      exact Int.le_trans h.1 ((Sorting.lowerbound_iff y l).mp hh.1 z hz)
    · intro h
      exact ⟨h.1.1, h.2⟩

private theorem increasing_pairwise (l : List Int) :
    increasing l ↔ l.Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp [Sorting.increasing]
  | cons x l ih =>
    change increasing_aux l x ↔ (x::l).Pairwise (· ≤ ·)
    rw [increasing_aux_iff, List.pairwise_cons, Sorting.lowerbound_iff, ih]

private theorem increasing_Znth (l : List Int) (h : increasing l) (i j : Int)
    (hr : 0 ≤ i ∧ i ≤ j ∧ j < Zlength l) : Znth i l 0 ≤ Znth j l 0 := by
  have hi : i.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hr; omega
  have hj : j.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hr; omega
  by_cases hij : i = j
  · subst j; exact Int.le_refl _
  have hlt : i.toNat < j.toNat := by omega
  have hp := (List.pairwise_iff_getElem.mp ((increasing_pairwise l).mp h)) i.toNat j.toNat hi hj hlt
  simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj, Option.getD_some] using hp

private theorem increasing_of_Znth (l : List Int)
    (h : ∀ i j : Int, (0 ≤ i ∧ i ≤ j ∧ j < Zlength l) → Znth i l 0 ≤ Znth j l 0) :
    increasing l := by
  apply (increasing_pairwise l).mpr
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hz := h i j (by simp only [Zlength, Int.ofNat_eq_coe]; omega)
  simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some] using hz

private theorem sublist_length (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l) :
    Zlength (sublist lo hi l) = hi-lo := by
  simp only [Zlength, sublist, List.length_drop, List.length_take, Int.ofNat_eq_coe] at *
  omega

theorem increasing_sublist_elim (l : List Int) (lo hi i j : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l)
    (h : increasing (sublist lo hi l)) (hr : lo ≤ i ∧ i ≤ j ∧ j < hi) :
    Znth i l 0 ≤ Znth j l 0 := by
  have hz := increasing_Znth (sublist lo hi l) h (i-lo) (j-lo)
    (by rw [sublist_length l lo hi hlo hhi]; omega)
  rw [Znth_sublist 0 lo (i-lo) hi l hlo.1 (by omega),
      Znth_sublist 0 lo (j-lo) hi l hlo.1 (by omega)] at hz
  simpa using hz

theorem increasing_sublist_intro (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l)
    (h : ∀ i j, (lo ≤ i ∧ i ≤ j ∧ j < hi) → Znth i l 0 ≤ Znth j l 0) :
    increasing (sublist lo hi l) := by
  apply increasing_of_Znth
  intro i j hr
  rw [sublist_length l lo hi hlo hhi] at hr
  rw [Znth_sublist 0 lo i hi l hlo.1 (by omega), Znth_sublist 0 lo j hi l hlo.1 (by omega)]
  exact h _ _ (by omega)

private theorem perm_replace_head (l : List Int) (k : Nat) (x d : Int) (hk : k < l.length) :
    Permutation (x :: l) (l.getD k d :: replace_nth k l x) := by
  induction l generalizing k x with
  | nil => simp at hk
  | cons y l ih =>
    cases k with
    | zero => exact List.Perm.swap y x l
    | succ k =>
      simp only [List.getD_cons_succ, replace_nth]
      exact (List.Perm.swap y x l).trans
        ((ih k x (by simpa using hk)).cons y |>.trans (List.Perm.swap _ _ _))

private theorem permutation_swap_nat (l : List Int) (i j : Nat) (d : Int)
    (hij : i < j) (hj : j < l.length) :
    Permutation l (replace_nth j (replace_nth i l (l.getD j d)) (l.getD i d)) := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons x l ih =>
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j => simpa only [replace_nth, List.getD_cons_zero, List.getD_cons_succ] using
          perm_replace_head l j x d (by simpa using hj)
    | succ i =>
      cases j with
      | zero => omega
      | succ j => simpa only [replace_nth, List.getD_cons_succ] using
          (ih i j (by omega) (by simpa using hj)).cons x

theorem permutation_swap_Znth_lt (l : List Int) (i j d : Int)
    (hr : 0 ≤ i ∧ i < j ∧ j < Zlength l) :
    Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) := by
  apply permutation_swap_nat
  · omega
  · simp only [Zlength, Int.ofNat_eq_coe] at hr; omega

end SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_lib
namespace SimpleC.EE.LLM_bench.Algorithms.selection_sort
export selection_sort_lib (increasing_aux increasing lowerbound strict_lowerbound)
end SimpleC.EE.LLM_bench.Algorithms.selection_sort

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_lib
open AUXLib
export SimpleC.EE.LLM_bench.Algorithms.SelectionMinimum (selection_minimum)
end SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_lib
namespace SimpleC.EE.LLM_bench.Algorithms.selection_sort
export selection_sort_lib (selection_minimum)
end SimpleC.EE.LLM_bench.Algorithms.selection_sort
