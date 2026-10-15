import AUXLib.Sorting
import SimpleC.SL.SeparationLogic
import SimpleC.EE.LLM_bench.Algorithms.selection_sort.selection_sort_lib
import ListLib.General.Length

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
export AUXLib.Sorting (increasing increasing_aux)

def same_outside_range (l l1 : List Int) (left right : Int) : Prop :=
  Zlength l = Zlength l1 ∧ ∀ k, (0 ≤ k ∧ k < Zlength l) →
    (k < left ∨ right < k) → Znth k l1 0 = Znth k l 0

def partitioned_at (l : List Int) (low high p : Int) : Prop :=
  (low ≤ p ∧ p ≤ high) ∧
  Forall (fun x => x ≤ Znth p l 0) (sublist low p l) ∧
  Forall (fun x => Znth p l 0 ≤ x) (sublist (p + 1) (high + 1) l)

def range_nondecreasing (l : List Int) (left right : Int) : Prop :=
  ∀ i j, left ≤ i → i ≤ j → j ≤ right → Znth i l 0 ≤ Znth j l 0

private theorem sublist_lengthZ (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l) :
    Zlength (sublist lo hi l) = hi - lo := ListLib.Zlength_sublist lo hi l hlo hhi

private theorem Forall_Znth_d (P : Int → Prop) (l : List Int) (i d : Int)
    (hp : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l d) := by
  have hin : i.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega
  have hmem := List.getElem_mem (l := l) hin
  have h := hp.mem hmem
  simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin, Option.getD_some] using h

private theorem Forall_of_Znth (P : Int → Prop) (l : List Int)
    (h : ∀ i, (0 ≤ i ∧ i < Zlength l) → P (Znth i l 0)) : Forall P l := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hp := h i (by simp only [Zlength, Int.ofNat_eq_coe]; omega)
  simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some] using hp

private theorem app_Znth_left (d : Int) (l l' : List Int) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) : Znth i (l ++ l') d = Znth i l d :=
  ListLib.app_Znth1 d l l' i hi

private theorem decompose_at (d : Int) (l : List Int) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) :
    l = sublist 0 i l ++ (Znth i l d :: sublist (i + 1) (Zlength l) l) := by
  calc
    l = sublist 0 (Zlength l) l := (sublist_self l (Zlength l) rfl).symm
    _ = _ := by
      rw [sublist_split 0 (Zlength l) i l (by omega) (by omega),
        sublist_split i (Zlength l) (i + 1) l (by omega) (by omega), sublist_single d i l hi]
      rfl

theorem same_outside_range_trans_local (l l1 l2 : List Int) (left right : Int)
    (h1 : same_outside_range l l1 left right) (h2 : same_outside_range l1 l2 left right) :
    same_outside_range l l2 left right := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  intro k hk ho
  exact (h2.2 k (by have := h1.1; omega) ho).trans (h1.2 k hk ho)

theorem Forall_Znth_local (P : Int → Prop) (l : List Int) (i : Int)
    (hp : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l 0) :=
  Forall_Znth_d P l i 0 hp hi

theorem Forall_sublist_by_Znth_local (P : Int → Prop) (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l)
    (hp : ∀ k, (lo ≤ k ∧ k < hi) → P (Znth k l 0)) : Forall P (sublist lo hi l) := by
  apply Forall_of_Znth
  intro i hi'
  rw [sublist_lengthZ l lo hi hlo hhi] at hi'
  rw [Znth_sublist 0 lo i hi l hlo.1 hi']
  exact hp _ (by omega)

theorem same_outside_range_swap_inside_local (l : List Int) (low high i j : Int)
    (hlo : 0 ≤ low) (hi : low ≤ i ∧ i ≤ high) (hj : low ≤ j ∧ j ≤ high)
    (hh : high < Zlength l) :
    same_outside_range l (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l)) low high := by
  refine ⟨by simp only [Zlength_replace_Znth], ?_⟩
  intro k hk hout
  rw [Znth_replace_Znth_Diff 0 _ j k _ (by simp only [Zlength_replace_Znth] <;> omega)
    (by simp only [Zlength_replace_Znth]; omega) (by omega),
    Znth_replace_Znth_Diff 0 l i k _ (by omega) hk (by omega)]

theorem same_outside_range_replace_inside_local (l : List Int) (low high i v : Int)
    (hlo : 0 ≤ low) (hi : low ≤ i ∧ i ≤ high) (hh : high < Zlength l) :
    same_outside_range l (replace_Znth i v l) low high := by
  refine ⟨by simp only [Zlength_replace_Znth], ?_⟩
  intro k hk hout
  exact Znth_replace_Znth_Diff 0 l i k v (by omega) hk (by omega)

theorem list_split_around_two_indices_local (d : Int) (l : List Int) (i j : Int)
    (hr : 0 ≤ i ∧ i < j ∧ j < Zlength l) :
    l = sublist 0 i l ++ (Znth i l d :: (sublist (i + 1) j l ++
      (Znth j l d :: sublist (j + 1) (Zlength l) l))) := by
  calc
    l = sublist 0 i l ++ (Znth i l d :: sublist (i + 1) (Zlength l) l) := decompose_at d l i (by omega)
    _ = _ := by
      rw [sublist_split (i + 1) (Zlength l) j l (by omega) (by omega),
        sublist_split j (Zlength l) (j + 1) l (by omega) (by omega),
        sublist_single d j l (by omega)]
      rfl

theorem sublist_suffix_full_local (l : List Int) (lo : Int) (hlo : 0 ≤ lo ∧ lo ≤ Zlength l) :
    sublist lo (Zlength l) l = l.drop lo.toNat := by simp [sublist, Zlength]

theorem replace_Znth_decomp_local (d v : Int) (l : List Int) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) :
    replace_Znth i v l = sublist 0 i l ++ (v :: sublist (i + 1) (Zlength l) l) := by
  have hd := decompose_at d l i hi
  have hl : Zlength (sublist 0 i l) = i := by simpa using sublist_lengthZ l 0 i (by omega) (by omega)
  calc
    replace_Znth i v l = replace_Znth i v (sublist 0 i l ++ (Znth i l d :: sublist (i + 1) (Zlength l) l)) := congrArg (replace_Znth i v) hd
    _ = _ := by
      simpa only [hl] using Sorting.replace_Znth_boundary_local (sublist 0 i l) (sublist (i + 1) (Zlength l) l) v (Znth i l d)

theorem swap_Znth_perm_local (l : List Int) (i j : Int)
    (hr : 0 ≤ i ∧ i < j ∧ j < Zlength l) :
    Permutation l (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l)) :=
  selection_sort.selection_sort_lib.permutation_swap_Znth_lt l i j 0 hr

private theorem read_replace (l : List Int) (i k v : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hk : 0 ≤ k ∧ k < Zlength l) :
    Znth k (replace_Znth i v l) 0 = if k = i then v else Znth k l 0 := by
  by_cases h : k = i
  · subst k; simp only [ite_true]; exact Znth_replace_Znth_Same 0 l i v hi
  · rw [if_neg h]; exact Znth_replace_Znth_Diff 0 l i k v hi hk (Ne.symm h)

private theorem read_swap (l : List Int) (i j k : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l)
    (hk : 0 ≤ k ∧ k < Zlength l) :
    Znth k (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l)) 0 =
    if k = j then Znth i l 0 else if k = i then Znth j l 0 else Znth k l 0 := by
  rw [read_replace _ j k _ (by simpa only [Zlength_replace_Znth] using hj)
    (by simpa only [Zlength_replace_Znth] using hk), read_replace l i k _ hi hk]

theorem partition_outer_exit_swap_yields_partitioned_at (l l1 : List Int) (low high pivot i j : Int)
    (hlo : 0 ≤ low) (hh : high < Zlength l) (hij : low ≤ i ∧ i ≤ j) (hj : j ≤ high)
    (hpivot : Znth low l1 0 = pivot) (hperm : Permutation l l1)
    (hout : same_outside_range l l1 low high) (hi : Znth i l1 0 ≤ pivot)
    (hl : ∀ k, (low < k ∧ k < i) → Znth k l1 0 ≤ pivot)
    (hr : ∀ k, (j < k ∧ k ≤ high) → pivot ≤ Znth k l1 0) (hexit : i ≥ j) :
    partitioned_at (replace_Znth i (Znth low l1 0) (replace_Znth low (Znth i l1 0) l1)) low high i := by
  have hlen := hout.1
  have hread := read_swap l1 low i
  have heq : Znth i (replace_Znth i (Znth low l1 0) (replace_Znth low (Znth i l1 0) l1)) 0 = pivot := by
    rw [hread i (by omega) (by omega) (by omega)]; simp [hpivot]
  refine ⟨by omega, ?_, ?_⟩
  · apply Forall_sublist_by_Znth_local _ _ low i (by omega) (by simp only [Zlength_replace_Znth]; omega)
    intro k hk
    rw [heq, hread k (by omega) (by omega) (by omega), if_neg (by omega)]
    by_cases he : k = low
    · simp only [he, ite_true]; exact hi
    · rw [if_neg he]; exact hl k (by omega)
  · apply Forall_sublist_by_Znth_local _ _ (i + 1) (high + 1) (by omega) (by simp only [Zlength_replace_Znth]; omega)
    intro k hk
    rw [heq, hread k (by omega) (by omega) (by omega), if_neg (by omega), if_neg (by omega)]
    exact hr k (by omega)

theorem range_nondecreasing_full_to_increasing (l : List Int)
    (h : range_nondecreasing l 0 (Zlength l - 1)) : increasing l := by
  have hlen : 0 ≤ Zlength l := by simp [Zlength]
  have hs := selection_sort.selection_sort_lib.increasing_sublist_intro l 0 (Zlength l)
    (by omega) (by omega) (by intro i j hij; exact h i j (by omega) (by omega) (by omega))
  simpa only [sublist_self l (Zlength l) rfl] using hs

theorem same_outside_range_weaken_local (l l1 : List Int) (left1 right1 left2 right2 : Int)
    (hl : left2 ≤ left1) (hr : right1 ≤ right2) (h : same_outside_range l l1 left1 right1) :
    same_outside_range l l1 left2 right2 := by
  refine ⟨h.1, ?_⟩; intro k hk ho; exact h.2 k hk (by omega)

theorem Forall_permutation_local (P : Int → Prop) (l1 l2 : List Int)
    (hp : Permutation l1 l2) (h : Forall P l1) : Forall P l2 := h.perm hp

theorem sublist_eq_from_Znth_local (l1 l2 : List Int) (lo hi : Int)
    (hlen : Zlength l1 = Zlength l2) (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l1)
    (hp : ∀ k, (lo ≤ k ∧ k < hi) → Znth k l1 0 = Znth k l2 0) :
    sublist lo hi l1 = sublist lo hi l2 := by
  apply (ListLib.list_eq_ext _ _ 0).mpr
  refine ⟨?_, ?_⟩
  · exact (sublist_lengthZ l1 lo hi hlo hhi).trans (sublist_lengthZ l2 lo hi hlo (by omega)).symm
  · intro i hi'
    have hb : 0 ≤ i ∧ i < hi - lo := by have := sublist_lengthZ l1 lo hi hlo hhi; change 0 ≤ i ∧ i < Zlength (sublist lo hi l1) at hi'; omega
    change Znth i (sublist lo hi l1) 0 = Znth i (sublist lo hi l2) 0
    rw [Znth_sublist 0 lo i hi l1 hlo.1 hb, Znth_sublist 0 lo i hi l2 hlo.1 hb]
    exact hp _ (by omega)

theorem list_decompose_sublist_local (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l) :
    l = sublist 0 lo l ++ (sublist lo hi l ++ sublist hi (Zlength l) l) := by
  calc
    l = sublist 0 (Zlength l) l := (sublist_self l (Zlength l) rfl).symm
    _ = _ := by rw [sublist_split 0 (Zlength l) lo l (by omega) (by omega),
      sublist_split lo (Zlength l) hi l hlo (by omega)]

theorem same_outside_range_prefix_local (l l1 : List Int) (left right : Int)
    (h : same_outside_range l l1 left right) (hl : 0 ≤ left ∧ left ≤ Zlength l) :
    sublist 0 left l1 = sublist 0 left l := by
  apply sublist_eq_from_Znth_local l1 l 0 left h.1.symm (by omega) (by have := h.1; omega)
  intro k hk; exact h.2 k (by omega) (Or.inl hk.2)

theorem same_outside_range_suffix_local (l l1 : List Int) (left right : Int)
    (h : same_outside_range l l1 left right) (hr : 0 ≤ right + 1 ∧ right + 1 ≤ Zlength l) :
    sublist (right + 1) (Zlength l1) l1 = sublist (right + 1) (Zlength l) l := by
  rw [← h.1]
  apply sublist_eq_from_Znth_local l1 l (right + 1) (Zlength l) h.1.symm hr (by have := h.1; omega)
  intro k hk; exact h.2 k (by omega) (Or.inr (by omega))

theorem middle_permutation_of_same_outside_local (l l1 : List Int) (left right : Int)
    (hp : Permutation l l1) (h : same_outside_range l l1 left right)
    (hl : 0 ≤ left ∧ left ≤ right + 1) (hr : right + 1 ≤ Zlength l) :
    Permutation (sublist left (right + 1) l) (sublist left (right + 1) l1) := by
  have hd := list_decompose_sublist_local l left (right + 1) hl hr
  have hd1 := list_decompose_sublist_local l1 left (right + 1) hl (by have := h.1; omega)
  have hpfx := same_outside_range_prefix_local l l1 left right h (by omega)
  have hsfx := same_outside_range_suffix_local l l1 left right h (by omega)
  conv at hp => lhs; rw [hd]
  conv at hp => rhs; rw [hd1]
  rw [hpfx, hsfx] at hp
  exact (List.perm_append_right_iff _).mp ((List.perm_append_left_iff _).mp hp)

theorem partitioned_at_preserved_by_left_local (l l1 : List Int) (left right p : Int)
    (hp : Permutation l l1) (hl : 0 ≤ left) (h : same_outside_range l l1 left (p - 1))
    (hr : right < Zlength l) (hpart : partitioned_at l left right p) : partitioned_at l1 left right p := by
  have heq := h.2 p (by have := hpart.1; omega) (Or.inr (by omega))
  refine ⟨hpart.1, ?_, ?_⟩
  · rw [heq]
    have hm := middle_permutation_of_same_outside_local l l1 left (p - 1) hp h (by have := hpart.1; omega) (by have := hpart.1; omega)
    simp only [Int.sub_add_cancel] at hm
    exact Forall_permutation_local _ _ _ hm hpart.2.1
  · rw [heq]
    have hs : sublist (p + 1) (right + 1) l1 = sublist (p + 1) (right + 1) l := by
      apply sublist_eq_from_Znth_local l1 l _ _ h.1.symm (by have := hpart.1; omega) (by have := h.1; omega)
      intro k hk; exact h.2 k (by have := hpart.1; omega) (Or.inr (by omega))
    rw [hs]; exact hpart.2.2

theorem partitioned_at_preserved_by_right_local (l l1 : List Int) (left right p : Int)
    (hp : Permutation l l1) (hl : 0 ≤ left) (h : same_outside_range l l1 (p + 1) right)
    (hr : right < Zlength l) (hpart : partitioned_at l left right p) : partitioned_at l1 left right p := by
  have heq := h.2 p (by have := hpart.1; omega) (Or.inl (by omega))
  refine ⟨hpart.1, ?_, ?_⟩
  · rw [heq]
    have hs : sublist left p l1 = sublist left p l := by
      apply sublist_eq_from_Znth_local l1 l _ _ h.1.symm (by have := hpart.1; omega) (by have := h.1; have := hpart.1; omega)
      intro k hk; exact h.2 k (by have := hpart.1; omega) (Or.inl (by omega))
    rw [hs]; exact hpart.2.1
  · rw [heq]
    exact Forall_permutation_local _ _ _ (middle_permutation_of_same_outside_local l l1 (p + 1) right hp h (by have := hpart.1; omega) (by omega)) hpart.2.2

theorem partitioned_at_left_Znth_le_local (l : List Int) (left right p k : Int)
    (hl : 0 ≤ left) (hp : p ≤ Zlength l) (hpart : partitioned_at l left right p)
    (hk : left ≤ k ∧ k < p) : Znth k l 0 ≤ Znth p l 0 := by
  have hlen := sublist_lengthZ l left p (by omega) hp
  have h := Forall_Znth_local _ _ (k - left) hpart.2.1 (by omega)
  rw [Znth_sublist 0 left (k - left) p l hl (by omega)] at h
  simpa only [Int.sub_add_cancel] using h

theorem partitioned_at_right_Znth_ge_local (l : List Int) (left right p k : Int)
    (hl : 0 ≤ left) (hr : right < Zlength l) (hpart : partitioned_at l left right p)
    (hk : p < k ∧ k ≤ right) : Znth p l 0 ≤ Znth k l 0 := by
  have hlen := sublist_lengthZ l (p + 1) (right + 1) (by have := hpart.1; omega) (by omega)
  have h := Forall_Znth_local _ _ (k - (p + 1)) hpart.2.2 (by omega)
  rw [Znth_sublist 0 (p + 1) (k - (p + 1)) (right + 1) l (by have := hpart.1; omega) (by omega)] at h
  simpa only [Int.sub_add_cancel] using h

theorem range_nondecreasing_ext_local (l l1 : List Int) (left right : Int)
    (hlen : Zlength l = Zlength l1)
    (heq : ∀ k, (left ≤ k ∧ k ≤ right) → Znth k l1 0 = Znth k l 0)
    (hs : range_nondecreasing l left right) : range_nondecreasing l1 left right := by
  intro i j hi hij hj
  rw [heq i (by omega), heq j (by omega)]; exact hs i j hi hij hj

theorem quicksort_partition_combine_right_only_local (l : List Int) (left right p : Int)
    (hl : 0 ≤ left) (hr : right < Zlength l) (he : p = left)
    (hp : partitioned_at l left right p) (hs : range_nondecreasing l (p + 1) right) :
    range_nondecreasing l left right := by
  intro i j hi hij hj
  by_cases heq : i = j
  · rw [heq] <;> omega
  by_cases hip : i = p
  · rw [hip]; exact partitioned_at_right_Znth_ge_local l left right p j hl hr hp (by omega)
  · exact hs i j (by omega) hij hj

theorem quicksort_partition_combine_left_only_local (l : List Int) (left right p : Int)
    (hl : 0 ≤ left) (hr : right < Zlength l) (he : p = right)
    (hp : partitioned_at l left right p) (hs : range_nondecreasing l left (p - 1)) :
    range_nondecreasing l left right := by
  intro i j hi hij hj
  by_cases heq : i = j
  · rw [heq] <;> omega
  by_cases hjp : j = p
  · rw [hjp]; exact partitioned_at_left_Znth_le_local l left right p i hl (by omega) hp (by omega)
  · exact hs i j hi hij (by omega)

theorem quicksort_partition_combine_both_sides_local (l : List Int) (left right p : Int)
    (hl : 0 ≤ left) (hr : right < Zlength l) (hpr : left ≤ p ∧ p ≤ right)
    (hp : partitioned_at l left right p) (hls : range_nondecreasing l left (p - 1))
    (hrs : range_nondecreasing l (p + 1) right) : range_nondecreasing l left right := by
  intro i j hi hij hj
  by_cases hipl : i < p
  · by_cases hjpl : j < p
    · exact hls i j hi hij (by omega)
    · have hi' := partitioned_at_left_Znth_le_local l left right p i hl (by omega) hp ⟨hi, hipl⟩
      by_cases hjp : j = p
      · simpa only [hjp] using hi'
      · exact Int.le_trans hi' (partitioned_at_right_Znth_ge_local l left right p j hl hr hp (by omega))
  · by_cases hjp : i = j
    · rw [hjp] <;> omega
    by_cases hip : i = p
    · rw [hip]; exact partitioned_at_right_Znth_ge_local l left right p j hl hr hp (by omega)
    · exact hrs i j (by omega) hij hj

theorem replace_nth_comm_Z_local (ni nj : Nat) (l : List Int) (a b : Int) (hne : ni ≠ nj) :
    replace_nth nj (replace_nth ni l a) b = replace_nth ni (replace_nth nj l b) a := by
  induction ni generalizing nj l with
  | zero => cases l <;> cases nj <;> simp_all [replace_nth]
  | succ ni ih =>
    cases l with
    | nil => cases nj <;> rfl
    | cons x xs => cases nj with
      | zero => rfl
      | succ nj => simp only [replace_nth]; rw [ih nj xs (by omega)]

theorem replace_Znth_comm_local (l : List Int) (i j a b : Int)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hne : i ≠ j) :
    replace_Znth j b (replace_Znth i a l) = replace_Znth i a (replace_Znth j b l) := by
  exact replace_nth_comm_Z_local i.toNat j.toNat l a b (by omega)

theorem replace_nth_twice_Z_local (n : Nat) (l : List Int) (a b : Int) :
    replace_nth n (replace_nth n l a) b = replace_nth n l b := by
  induction n generalizing l with
  | zero => cases l <;> rfl
  | succ n ih => cases l <;> simp only [replace_nth]; rw [ih]

theorem replace_Znth_twice_local (l : List Int) (i a b : Int) :
    replace_Znth i b (replace_Znth i a l) = replace_Znth i b l := replace_nth_twice_Z_local i.toNat l a b

theorem partition_hole_outer_fill_left_perm_split_local (l l1 : List Int) (low high pivot i j : Int)
    (hl : 0 ≤ low) (hh : high < Zlength l) (hp : Permutation l (replace_Znth i pivot l1))
    (ho : same_outside_range l l1 low high) (hloi : low ≤ i) (hij : i ≤ j) (hj : j ≤ high) (hlt : i < j) :
    Permutation l (replace_Znth j pivot (replace_Znth i (Znth j l1 0) l1)) := by
  have hlen := ho.1
  have hs := swap_Znth_perm_local (replace_Znth i pivot l1) i j (by simp only [Zlength_replace_Znth]; omega)
  rw [Znth_replace_Znth_Same 0 l1 i pivot (by omega),
    Znth_replace_Znth_Diff 0 l1 i j pivot (by omega) (by omega) (by omega), replace_Znth_twice_local] at hs
  exact hp.trans hs

theorem partition_hole_left_fill_right_perm_split_local (l l1 : List Int) (low high pivot i j : Int)
    (hl : 0 ≤ low) (hh : high < Zlength l) (hp : Permutation l (replace_Znth j pivot l1))
    (ho : same_outside_range l l1 low high) (hloi : low ≤ i) (hij : i ≤ j) (hj : j ≤ high) (hlt : i < j) :
    Permutation l (replace_Znth i pivot (replace_Znth j (Znth i l1 0) l1)) := by
  have hlen := ho.1
  have hs := swap_Znth_perm_local (replace_Znth j pivot l1) i j (by simp only [Zlength_replace_Znth]; omega)
  rw [Znth_replace_Znth_Same 0 l1 j pivot (by omega),
    Znth_replace_Znth_Diff 0 l1 j i pivot (by omega) (by omega) (by omega),
    replace_Znth_comm_local (replace_Znth j pivot l1) i j pivot (Znth i l1 0) (by omega) (by omega) (by omega),
    replace_Znth_twice_local] at hs
  exact hp.trans hs

theorem partition_hole_outer_exit_partitioned_split_local (l l1 : List Int) (low high pivot i j : Int)
    (hl : 0 ≤ low) (hh : high < Zlength l) (ho : same_outside_range l l1 low high)
    (hli : low ≤ i) (hij : i ≤ j) (hjh : j ≤ high)
    (hleft : ∀ k, (low ≤ k ∧ k < i) → Znth k l1 0 ≤ pivot)
    (hright : ∀ k, (j < k ∧ k ≤ high) → pivot ≤ Znth k l1 0) (he : i ≥ j) :
    partitioned_at (replace_Znth i pivot l1) low high i := by
  have hlen := ho.1
  have hpr := Znth_replace_Znth_Same 0 l1 i pivot (by omega)
  refine ⟨by omega, ?_, ?_⟩
  · apply Forall_sublist_by_Znth_local _ _ low i (by omega) (by simp only [Zlength_replace_Znth]; omega)
    intro k hk
    rw [hpr, read_replace l1 i k pivot (by omega) (by omega), if_neg (by omega)]
    exact hleft k hk
  · apply Forall_sublist_by_Znth_local _ _ (i + 1) (high + 1) (by omega) (by simp only [Zlength_replace_Znth]; omega)
    intro k hk
    rw [hpr, read_replace l1 i k pivot (by omega) (by omega), if_neg (by omega)]
    exact hright k (by omega)

theorem partition_hole_left_exit_partitioned_split_local (l l1 : List Int) (low high pivot i j : Int)
    (hl : 0 ≤ low) (hh : high < Zlength l) (ho : same_outside_range l l1 low high)
    (hli : low ≤ i) (hij : i ≤ j) (hjh : j ≤ high)
    (hleft : ∀ k, (low ≤ k ∧ k < i) → Znth k l1 0 ≤ pivot)
    (hright : ∀ k, (j < k ∧ k ≤ high) → pivot ≤ Znth k l1 0) (he : i ≥ j) :
    partitioned_at (replace_Znth i pivot l1) low high i :=
  partition_hole_outer_exit_partitioned_split_local l l1 low high pivot i j hl hh ho hli hij hjh hleft hright he

theorem quicksort_partition_combine_right_guard_local (l : List Int) (left right p : Int)
    (hl : 0 ≤ left) (hr : right < Zlength l) (hp : left ≤ p ∧ p ≤ right) (hshort : p ≤ left + 1)
    (hpart : partitioned_at l left right p) (hs : range_nondecreasing l (p + 1) right) :
    range_nondecreasing l left right := by
  apply quicksort_partition_combine_both_sides_local l left right p hl hr hp hpart _ hs
  intro i j hi hij hj
  have he : i = j := by omega
  rw [he] <;> omega

theorem quicksort_partition_combine_left_guard_local (l : List Int) (left right p : Int)
    (hl : 0 ≤ left) (hr : right < Zlength l) (hp : left ≤ p ∧ p ≤ right) (hshort : right - 1 ≤ p)
    (hpart : partitioned_at l left right p) (hs : range_nondecreasing l left (p - 1)) :
    range_nondecreasing l left right := by
  apply quicksort_partition_combine_both_sides_local l left right p hl hr hp hpart hs
  intro i j hi hij hj
  have he : i = j := by omega
  rw [he] <;> omega

theorem quicksort_partition_combine_short_local (l : List Int) (left right p : Int)
    (hl : 0 ≤ left) (hr : right < Zlength l) (hp : left ≤ p ∧ p ≤ right)
    (hshortl : p ≤ left + 1) (hshortr : right - 1 ≤ p) (hpart : partitioned_at l left right p) :
    range_nondecreasing l left right := by
  apply quicksort_partition_combine_right_guard_local l left right p hl hr hp hshortl hpart
  intro i j hi hij hj
  have he : i = j := by omega
  rw [he] <;> omega

private noncomputable abbrev intArray := naive_C_Rules.IntArray

theorem int_array_full_merge_three_local (x n m k : Int) (l1 l2 l3 : List Int)
    (hn : 0 ≤ n) (hm : 0 ≤ m) (hk : 0 ≤ k) :
    intArray.full x n l1 ** intArray.full (x + n * sizeof(INT)) m l2 **
      intArray.full (x + (n + m) * sizeof(INT)) k l3 |--
    intArray.full x (n + m + k) (l1 ++ (l2 ++ l3)) := by
  have h1 := intArray.full_merge_to_full (x + n * sizeof(INT)) m (m + k) l2 l3 (by omega)
  have h2 := intArray.full_merge_to_full x n (n + m + k) l1 (l2 ++ l3) (by omega)
  simp only [show m + k - m = k by omega] at h1
  simp only [show n + m + k - n = m + k by omega] at h2
  have he : x + (n + m) * sizeof(INT) = x + n * sizeof(INT) + m * sizeof(INT) := by simp only [Int.add_mul, Int.add_assoc]
  rw [he]
  simp only [SimpleC.SL.CNotation.sizeof_int, SimpleC.SL.CommonAssertion.DerivedPredSig.sizeof_int] at *
  refine naive_C_Rules.toContext.derivable1_trans _
    (intArray.full x n l1 ** (intArray.full (x + n * 4) m l2 ** intArray.full (x + n * 4 + m * 4) k l3)) _ ?_ ?_
  · cancel
  refine naive_C_Rules.toContext.derivable1_trans _
    (intArray.full x n l1 ** intArray.full (x + n * 4) (m + k) (l2 ++ l3)) _ ?_ ?_
  · exact naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _
      (naive_C_Rules.toContext.derivable1_refl _) h1
  · exact h2

private theorem perm_Zlength (l l1 : List Int) (h : Permutation l l1) : Zlength l = Zlength l1 :=
  congrArg Int.ofNat h.length_eq

theorem quicksort_permuted_partition_combine_local (n p : Int) (base left right : List Int)
    (hlen : Zlength base = n) (hp : 0 ≤ p ∧ p < n) (hpart : partitioned_at base 0 (n - 1) p)
    (hpl : Permutation (sublist 0 p base) left) (hsl : range_nondecreasing left 0 (p - 1))
    (hpr : Permutation (sublist (p + 1) n base) right)
    (hsr : range_nondecreasing right 0 (n - p - 1 - 1)) :
    range_nondecreasing (left ++ (sublist p (p + 1) base ++ right)) 0 (n - 1) := by
  have hll : Zlength left = p := by
    have := perm_Zlength _ _ hpl
    rw [sublist_lengthZ base 0 p (by omega) (by omega)] at this; omega
  have hlr : Zlength right = n - p - 1 := by
    have := perm_Zlength _ _ hpr
    rw [sublist_lengthZ base (p + 1) n (by omega) (by omega)] at this; omega
  have hbl := Forall_permutation_local _ _ _ hpl hpart.2.1
  have hbr := hpart.2.2
  simp only [Int.sub_add_cancel] at hbr
  have hbr' := Forall_permutation_local _ _ _ hpr hbr
  rw [sublist_single 0 p base (by omega)]
  change range_nondecreasing (left ++ (Znth p base 0 :: right)) 0 (n - 1)
  have hreadl : ∀ k, (0 ≤ k ∧ k < p) → Znth k (left ++ (Znth p base 0 :: right)) 0 = Znth k left 0 := by
    intro k hk; exact app_Znth_left 0 left _ k (by omega)
  have hreadp : Znth p (left ++ (Znth p base 0 :: right)) 0 = Znth p base 0 := by
    simpa only [hll] using Sorting.Znth_boundary_d left right (Znth p base 0) 0
  have hreadr : ∀ k, (p < k ∧ k < n) → Znth k (left ++ (Znth p base 0 :: right)) 0 = Znth (k - (p + 1)) right 0 := by
    intro k hk
    rw [app_Znth2 0 left _ k (by omega), hll]
    change Znth (k - p) ([Znth p base 0] ++ right) 0 = _
    rw [app_Znth2 0 [Znth p base 0] right (k - p) (by change 1 ≤ k - p; omega)]
    have he : k - p - Zlength [Znth p base 0] = k - (p + 1) := by simp [Zlength]; omega
    rw [he]
  have hleft : ∀ k, (0 ≤ k ∧ k < p) → Znth k left 0 ≤ Znth p base 0 := by
    intro k hk; exact Forall_Znth_local _ left k hbl (by omega)
  have hright : ∀ k, (0 ≤ k ∧ k < n - p - 1) → Znth p base 0 ≤ Znth k right 0 := by
    intro k hk; exact Forall_Znth_local _ right k hbr' (by omega)
  intro i j hi hij hj
  by_cases hjl : j < p
  · rw [hreadl i (by omega), hreadl j (by omega)]; exact hsl i j hi hij (by omega)
  · by_cases hjp : j = p
    · subst j
      by_cases hip : i = p
      · rw [hip] <;> omega
      · rw [hreadl i (by omega), hreadp]; exact hleft i (by omega)
    · rw [hreadr j (by omega)]
      by_cases hil : i < p
      · rw [hreadl i (by omega)]
        exact Int.le_trans (hleft i (by omega)) (hright (j - (p + 1)) (by omega))
      · by_cases hip : i = p
        · rw [hip, hreadp]; exact hright _ (by omega)
        · rw [hreadr i (by omega)]; exact hsr _ _ (by omega) (by omega) (by omega)

theorem increasing_length_le_1 (l : List Int) (hl : Zlength l ≤ 1) : increasing l := by
  cases l with
  | nil => trivial
  | cons x xs => cases xs with
    | nil => trivial
    | cons y ys => simp only [Zlength, List.length_cons, Int.ofNat_eq_coe] at hl; omega

theorem lomuto_replace_Znth_swap_form (l1 l2 l3 : List Int) (xi xj : Int) :
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ (xi :: (l2 ++ (xj :: l3))))) =
    l1 ++ (xj :: (l2 ++ (xi :: l3))) := by
  rw [Sorting.replace_Znth_boundary_local]
  have he : Zlength l1 + 1 + Zlength l2 = Zlength (l1 ++ (xj :: l2)) := by simp [Zlength]; omega
  rw [he]
  have ha : l1 ++ (xj :: (l2 ++ (xj :: l3))) = (l1 ++ (xj :: l2)) ++ (xj :: l3) := by simp only [List.append_assoc, List.cons_append]
  rw [ha, Sorting.replace_Znth_boundary_local]
  simp only [List.append_assoc, List.cons_append]

theorem lomuto_permutation_swap_Znth_lt (l : List Int) (i j d : Int)
    (h : 0 ≤ i ∧ i < j ∧ j < Zlength l) :
    Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) :=
  selection_sort.selection_sort_lib.permutation_swap_Znth_lt l i j d h

theorem lomuto_replace_nth_comm_Z (ni nj : Nat) (l : List Int) (a b : Int) (hne : ni ≠ nj) :
    replace_nth nj (replace_nth ni l a) b = replace_nth ni (replace_nth nj l b) a :=
  replace_nth_comm_Z_local ni nj l a b hne

theorem lomuto_replace_Znth_comm (l : List Int) (i j a b : Int)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hne : i ≠ j) :
    replace_Znth j b (replace_Znth i a l) = replace_Znth i a (replace_Znth j b l) :=
  replace_Znth_comm_local l i j a b hi hj hne

private theorem replace_self (l : List Int) (i d : Int) (hi : 0 ≤ i ∧ i < Zlength l) :
    replace_Znth i (Znth i l d) l = l := by
  rw [replace_Znth_decomp_local d (Znth i l d) l i hi]
  exact (decompose_at d l i hi).symm

theorem lomuto_permutation_swap_Znth (l : List Int) (i j d : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) :
    Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) := by
  by_cases he : i = j
  · subst j; rw [replace_Znth_twice_local, replace_self l i d hi]
  · by_cases hlt : i < j
    · exact lomuto_permutation_swap_Znth_lt l i j d (by omega)
    · rw [replace_Znth_comm_local l i j _ _ hi.1 hj.1 he]
      exact lomuto_permutation_swap_Znth_lt l j i d (by omega)

theorem lomuto_permutation_swap_Znth_by_result_length (l : List Int) (i j n d : Int)
    (hi : 0 ≤ i ∧ i < n) (hj : 0 ≤ j ∧ j < n)
    (hlen : Zlength (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) = n) :
    Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) := by
  simp only [Zlength_replace_Znth] at hlen
  exact lomuto_permutation_swap_Znth l i j d (by omega) (by omega)

theorem same_outside_range_refl (l : List Int) (left right : Int) : same_outside_range l l left right :=
  ⟨rfl, fun _ _ _ => rfl⟩

theorem same_outside_range_trans : ∀ (l l1 l2 : List Int) (left right : Int)
    (h1 : same_outside_range l l1 left right) (h2 : same_outside_range l1 l2 left right),     same_outside_range l l2 left right :=
  same_outside_range_trans_local

theorem same_outside_range_weaken : ∀ (l l1 : List Int) (left1 right1 left2 right2 : Int)
    (hl : left2 ≤ left1) (hr : right1 ≤ right2) (h : same_outside_range l l1 left1 right1),     same_outside_range l l1 left2 right2 :=
  same_outside_range_weaken_local

theorem Forall_permutation : ∀ (P : Int → Prop) (l1 l2 : List Int)
    (hp : Permutation l1 l2) (h : Forall P l1), Forall P l2 :=
  Forall_permutation_local

theorem lomuto_Forall_Znth (P : Int → Prop) (l : List Int) (i d : Int)
    (h : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l d) := Forall_Znth_d P l i d h hi

theorem lomuto_Znth_replace_eq (l : List Int) (n a d : Int) (hn : 0 ≤ n ∧ n < Zlength l) :
    Znth n (replace_Znth n a l) d = a := Znth_replace_Znth_Same d l n a hn

theorem lomuto_Znth_replace_neq (l : List Int) (i j a d : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j) (hne : i ≠ j) :
    Znth i (replace_Znth j a l) d = Znth i l d := by
  by_cases h : j < Zlength l
  · exact Znth_replace_Znth_Diff d l j i a ⟨hj, h⟩ hi hne.symm
  · rw [replace_Znth_nothing j l a (by omega)]

theorem sublist_eq_from_Znth : ∀ (l1 l2 : List Int) (lo hi : Int)
    (hlen : Zlength l1 = Zlength l2) (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l1)
    (hp : ∀ k, (lo ≤ k ∧ k < hi) → Znth k l1 0 = Znth k l2 0),     sublist lo hi l1 = sublist lo hi l2 :=
  sublist_eq_from_Znth_local

theorem lomuto_list_decompose_sublist : ∀ (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l),     l = sublist 0 lo l ++ (sublist lo hi l ++ sublist hi (Zlength l) l) :=
  list_decompose_sublist_local

theorem same_outside_range_prefix : ∀ (l l1 : List Int) (left right : Int)
    (h : same_outside_range l l1 left right) (hl : 0 ≤ left ∧ left ≤ Zlength l),     sublist 0 left l1 = sublist 0 left l :=
  same_outside_range_prefix_local

theorem same_outside_range_suffix : ∀ (l l1 : List Int) (left right : Int)
    (h : same_outside_range l l1 left right) (hr : 0 ≤ right + 1 ∧ right + 1 ≤ Zlength l),     sublist (right + 1) (Zlength l1) l1 = sublist (right + 1) (Zlength l) l :=
  same_outside_range_suffix_local

theorem middle_permutation_of_same_outside : ∀ (l l1 : List Int) (left right : Int)
    (hp : Permutation l l1) (h : same_outside_range l l1 left right)
    (hl : 0 ≤ left ∧ left ≤ right + 1) (hr : right + 1 ≤ Zlength l),     Permutation (sublist left (right + 1) l) (sublist left (right + 1) l1) :=
  middle_permutation_of_same_outside_local

theorem lomuto_Forall_sublist_by_Znth : ∀ (P : Int → Prop) (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l)
    (hp : ∀ k, (lo ≤ k ∧ k < hi) → P (Znth k l 0)), Forall P (sublist lo hi l) :=
  Forall_sublist_by_Znth_local

theorem same_outside_range_swap_inside : ∀ (l : List Int) (low high i j : Int)
    (hlo : 0 ≤ low) (hi : low ≤ i ∧ i ≤ high) (hj : low ≤ j ∧ j ≤ high)
    (hh : high < Zlength l),     same_outside_range l (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l)) low high :=
  same_outside_range_swap_inside_local

theorem partitioned_at_after_lomuto_final_swap (l1 : List Int) (low high pivot i : Int)
    (hl : 0 ≤ low) (hh : high < Zlength l1) (hi : low - 1 ≤ i) (hih : i < high)
    (hpx : Znth high l1 0 = pivot)
    (hleft : ∀ k, (low ≤ k ∧ k ≤ i) → Znth k l1 0 ≤ pivot)
    (hright : ∀ k, (i < k ∧ k < high) → pivot < Znth k l1 0) :
    partitioned_at (replace_Znth high (Znth (i + 1) l1 0)
      (replace_Znth (i + 1) (Znth high l1 0) l1)) low high (i + 1) := by
  have hs := read_swap l1 (i + 1) high
  have hpr : Znth (i + 1) (replace_Znth high (Znth (i + 1) l1 0)
      (replace_Znth (i + 1) (Znth high l1 0) l1)) 0 = pivot := by
    rw [hs (i + 1) (by omega) (by omega) (by omega)]
    by_cases he : i + 1 = high
    · simp [he, hpx]
    · simp only [if_neg he, ite_true, hpx]
  refine ⟨by omega, ?_, ?_⟩
  · apply Forall_sublist_by_Znth_local _ _ low (i + 1) (by omega) (by simp only [Zlength_replace_Znth]; omega)
    intro k hk
    rw [hpr, hs k (by omega) (by omega) (by omega), if_neg (by omega), if_neg (by omega)]
    exact hleft k (by omega)
  · apply Forall_sublist_by_Znth_local _ _ (i + 1 + 1) (high + 1) (by omega) (by simp only [Zlength_replace_Znth]; omega)
    intro k hk
    rw [hpr, hs k (by omega) (by omega) (by omega)]
    by_cases he : k = high
    · rw [if_pos he]; have := hright (i + 1) (by omega); omega
    · rw [if_neg he, if_neg (by omega)]; have := hright k (by omega); omega

end SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib

namespace SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index
export quicksort_lib (same_outside_range partitioned_at range_nondecreasing increasing increasing_aux)
end SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index
