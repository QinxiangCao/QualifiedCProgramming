import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib

set_option maxHeartbeats 4000000
set_option maxRecDepth 6000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_lib
open AUXLib
open SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib

def permutation : List Int → List Int → Prop := Permutation

def increasing_aux : List Int → Int → Prop
  | [], _ => True
  | y :: l, x => x ≤ y ∧ increasing_aux l y

def increasing : List Int → Prop
  | [] => True
  | x :: l => increasing_aux l x

def same_outside_range (l l1 : List Int) (left right : Int) : Prop :=
  Zlength l = Zlength l1 ∧ ∀ k, (0 ≤ k ∧ k < Zlength l) → (k < left ∨ right < k) → Znth k l1 0 = Znth k l 0

def partitioned_at (l : List Int) (low high p : Int) : Prop :=
  (low ≤ p ∧ p ≤ high) ∧ Forall (fun x => x ≤ Znth p l 0) (sublist low p l) ∧
    Forall (fun x => Znth p l 0 < x) (sublist (p+1) (high+1) l)

def partition_scan_inv (l l1 : List Int) (low high pivot i j : Int) : Prop :=
  permutation l l1 ∧ same_outside_range l l1 low high ∧ Znth high l1 0 = pivot ∧
    (∀ k, (low ≤ k ∧ k ≤ i) → Znth k l1 0 ≤ pivot) ∧
    ∀ k, (i < k ∧ k < j) → pivot < Znth k l1 0

inductive sorted_range (l : List Int) : Int → Int → Prop where
  | sorted_range_base (left right : Int) : left ≥ right → sorted_range l left right
  | sorted_range_from_left (left right p : Int) :
      p ≥ right → partitioned_at l left right p → sorted_range l left (p-1) → sorted_range l left right
  | sorted_range_from_right (left right p : Int) :
      p ≤ left → partitioned_at l left right p → sorted_range l (p+1) right → sorted_range l left right
  | sorted_range_from_both (left right p : Int) :
      (left ≤ p ∧ p ≤ right) → partitioned_at l left right p →
        sorted_range l left (p-1) → sorted_range l (p+1) right → sorted_range l left right
@[match_pattern] abbrev sorted_range_base (l : List Int) (left right : Int) (h : left ≥ right) :=
  sorted_range.sorted_range_base (l := l) left right h
@[match_pattern] abbrev sorted_range_from_left (l : List Int) (left right p : Int) (h : p ≥ right)
    (hp : partitioned_at l left right p) (hs : sorted_range l left (p-1)) :=
  sorted_range.sorted_range_from_left (l := l) left right p h hp hs
@[match_pattern] abbrev sorted_range_from_right (l : List Int) (left right p : Int) (h : p ≤ left)
    (hp : partitioned_at l left right p) (hs : sorted_range l (p+1) right) :=
  sorted_range.sorted_range_from_right (l := l) left right p h hp hs
@[match_pattern] abbrev sorted_range_from_both (l : List Int) (left right p : Int) (h : left ≤ p ∧ p ≤ right)
    (hp : partitioned_at l left right p) (hl : sorted_range l left (p-1)) (hr : sorted_range l (p+1) right) :=
  sorted_range.sorted_range_from_both (l := l) left right p h hp hl hr

def strict_increasing_prefix (l : List Int) (len : Int) : Prop :=
  (0 ≤ len ∧ len ≤ Zlength l) ∧ ∀ i j, (0 ≤ i ∧ i < j) → j < len → Znth i l 0 < Znth j l 0

def strict_increasing (l : List Int) : Prop := strict_increasing_prefix l (Zlength l)

def same_values_prefix (out : List Int) (out_len : Int) (src : List Int) (src_len : Int) : Prop :=
  ∀ x, x ∈ sublist 0 out_len out ↔ x ∈ sublist 0 src_len src

def dedup_scan_inv (src sorted cur : List Int) (slow fast : Int) : Prop :=
  Zlength src = Zlength sorted ∧ Zlength cur = Zlength sorted ∧ permutation src sorted ∧ increasing sorted ∧
  (1 ≤ fast ∧ fast ≤ Zlength sorted) ∧ (0 ≤ slow ∧ slow < fast) ∧ strict_increasing_prefix cur (slow+1) ∧
  same_values_prefix cur (slow+1) sorted fast ∧
  (∀ k, (fast ≤ k ∧ k < Zlength sorted) → Znth k cur 0 = Znth k sorted 0) ∧
  Znth slow cur 0 = Znth (fast-1) sorted 0

def discretize_resultLegacy (src : List Int) (n : Int) (out : List Int) (ret : Int) : Prop :=
  Zlength src = n ∧ Zlength out = n ∧ 1 ≤ n ∧ (1 ≤ ret ∧ ret ≤ n) ∧ strict_increasing_prefix out ret ∧
  same_values_prefix out ret src n ∧
  (∀ i, (0 ≤ i ∧ i < n) → ∃ r, (0 ≤ r ∧ r < ret) ∧ Znth r out 0 = Znth i src 0) ∧
  (∀ r, (0 ≤ r ∧ r < ret) → ∃ i, (0 ≤ i ∧ i < n) ∧ Znth r out 0 = Znth i src 0) ∧
  ∀ i j ri rj, (0 ≤ i ∧ i < n) → (0 ≤ j ∧ j < n) → (0 ≤ ri ∧ ri < ret) → (0 ≤ rj ∧ rj < ret) →
    Znth ri out 0 = Znth i src 0 → Znth rj out 0 = Znth j src 0 →
    (Znth i src 0 = Znth j src 0 → ri = rj) ∧ (Znth i src 0 < Znth j src 0 → ri < rj)

def query_forward_resultLegacy (map : List Int) (map_size target ret : Int) : Prop :=
  ((∃ i, (0 ≤ i ∧ i < map_size) ∧ Znth i map 0 = target ∧ ret=i) ∧
    (∀ j, (0 ≤ j ∧ j < map_size) → Znth j map 0 = target → ret=j)) ∨
  ((∀ i, (0 ≤ i ∧ i < map_size) → Znth i map 0 ≠ target) ∧ ret = -1)

def query_forward_search_inv (map : List Int) (map_size target low high : Int) : Prop :=
  0 ≤ low ∧ high < map_size ∧ low ≤ high+1 ∧
  (∀ i, (0 ≤ i ∧ i < low) → Znth i map 0 < target) ∧
  ∀ i, (high < i ∧ i < map_size) → target < Znth i map 0

theorem same_outside_range_refl__partition_scan (l : List Int) (left right : Int) :
    same_outside_range l l left right := ⟨rfl, by intros; rfl⟩

theorem same_outside_range_swap_inside__partition_scan (l l1 : List Int) (low high i j : Int)
    (hs : same_outside_range l l1 low high) (hi : low ≤ i ∧ i ≤ high) (hj : low ≤ j ∧ j ≤ high)
    (hir : 0 ≤ i ∧ i < Zlength l1) (hjr : 0 ≤ j ∧ j < Zlength l1) :
    same_outside_range l (replace_Znth j (Znth i l1 0) (replace_Znth i (Znth j l1 0) l1)) low high := by
  refine ⟨by simpa only [Zlength_replace_Znth] using hs.1, ?_⟩
  intro k hk ho
  have hl := hs.1
  rw [Znth_replace_Znth_Diff 0 _ j k _ (by simpa only [Zlength_replace_Znth] using hjr)
    (by simp only [Zlength_replace_Znth]; omega) (by omega),
    Znth_replace_Znth_Diff 0 l1 i k _ hir (by omega) (by omega)]
  exact hs.2 k hk ho

theorem replace_Znth_swap_form__partition_scan (l1 l2 l3 : List Int) (xi xj : Int) :
    replace_Znth (Zlength l1+1+Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ (xi :: (l2 ++ (xj :: l3)))) ) =
        l1 ++ (xj :: (l2 ++ (xi :: l3))) := by
  rw [Sorting.replace_Znth_boundary_local]
  have hlen1 := Zlength_nonneg l1
  have hlen2 := Zlength_nonneg l2
  rw [replace_Znth_app_r (Zlength l1+1+Zlength l2) xi l1 (xj::(l2++(xj::l3))) (by omega),
    replace_Znth_nothing (Zlength l1+1+Zlength l2) l1 xi (by omega)]
  rw [show Zlength l1+1+Zlength l2-Zlength l1 = Zlength l2+1 by omega,
    replace_Znth_cons (Zlength l2+1) xi xj (l2++(xj::l3)) (by omega)]
  simp only [Int.add_sub_cancel, Sorting.replace_Znth_boundary_local]

theorem permutation_swap_Znth_lt__partition_scan (l : List Int) (i j d : Int)
    (h : 0 ≤ i ∧ i < j ∧ j < Zlength l) :
    permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) :=
  selection_sort.selection_sort_lib.permutation_swap_Znth_lt l i j d h

theorem replace_nth_comm_Z__partition_scan (ni nj : Nat) (l : List Int) (a b : Int) (hne : ni ≠ nj) :
    replace_nth nj (replace_nth ni l a) b = replace_nth ni (replace_nth nj l b) a := by
  induction l generalizing ni nj with
  | nil => cases ni <;> cases nj <;> rfl
  | cons x l ih =>
    cases ni with
    | zero => cases nj with
      | zero => omega
      | succ nj => rfl
    | succ ni => cases nj with
      | zero => rfl
      | succ nj => exact congrArg (List.cons x) (ih ni nj (by omega))

theorem replace_Znth_comm__partition_scan (l : List Int) (i j a b : Int)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hne : i ≠ j) :
    replace_Znth j b (replace_Znth i a l) = replace_Znth i a (replace_Znth j b l) :=
  replace_nth_comm_Z__partition_scan i.toNat j.toNat l a b (by omega)

theorem permutation_swap_Znth__partition_scan (l : List Int) (i j d : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) :
    permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)) := by
  by_cases he : i=j
  · subst j
    rw [replace_Znth_Znth, replace_Znth_Znth]
    exact List.Perm.refl l
  · by_cases hlt : i<j
    · exact permutation_swap_Znth_lt__partition_scan l i j d (by omega)
    · rw [replace_Znth_comm__partition_scan l i j _ _ hi.1 hj.1 he]
      exact permutation_swap_Znth_lt__partition_scan l j i d (by omega)

theorem partition_scan_inv_init__partition_scan (l : List Int) (low high : Int)
    (hlo : 0 ≤ low) (hh : low ≤ high) :
    partition_scan_inv l l low high (Znth high l 0) (low-1) low :=
  ⟨List.Perm.refl l, same_outside_range_refl__partition_scan l low high, rfl,
    by intro k hk; omega, by intro k hk; omega⟩

theorem partition_scan_inv_step_gt__partition_scan (l l1 : List Int) (low high pivot i j : Int)
    (hgt : pivot < Znth j l1 0) (hj : j < high) (hs : partition_scan_inv l l1 low high pivot i j) :
    partition_scan_inv l l1 low high pivot i (j+1) := by
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  intro k hk
  by_cases he : k=j
  · simpa only [he] using hgt
  · exact hs.2.2.2.2 k (by omega)

theorem Forall_sublist_by_Znth__partition_scan (P : Int → Prop) (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l)
    (h : ∀ k, (lo ≤ k ∧ k < hi) → P (Znth k l 0)) : Forall P (sublist lo hi l) :=
  Forall_sublist_by_Znth_local P l lo hi hlo hhi h

theorem same_outside_range_refl__quicksort_range (l : List Int) (left right : Int) :
    same_outside_range l l left right := same_outside_range_refl__partition_scan l left right

theorem same_outside_range_trans__quicksort_range (l l1 l2 : List Int) (left right : Int)
    (h : same_outside_range l l1 left right) (h1 : same_outside_range l1 l2 left right) :
    same_outside_range l l2 left right := same_outside_range_trans_local l l1 l2 left right h h1

theorem same_outside_range_weaken__quicksort_range (l l1 : List Int) (left1 right1 left2 right2 : Int)
    (hl : left2 ≤ left1) (hr : right1 ≤ right2) (h : same_outside_range l l1 left1 right1) :
    same_outside_range l l1 left2 right2 := same_outside_range_weaken_local l l1 left1 right1 left2 right2 hl hr h

theorem Forall_permutation__quicksort_range (P : Int → Prop) (l1 l2 : List Int)
    (hp : permutation l1 l2) (h : Forall P l1) : Forall P l2 := h.perm hp

theorem Forall_Znth__quicksort_range (P : Int → Prop) (l : List Int) (i d : Int)
    (hp : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l d) := by
  have hin : i.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega
  have h := hp.mem (List.getElem_mem (l := l) hin)
  simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin, Option.getD_some] using h

theorem sublist_eq_from_Znth__quicksort_range (l1 l2 : List Int) (lo hi : Int)
    (hlen : Zlength l1 = Zlength l2) (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l1)
    (h : ∀ k, (lo ≤ k ∧ k < hi) → Znth k l1 0 = Znth k l2 0) :
    sublist lo hi l1 = sublist lo hi l2 := sublist_eq_from_Znth_local l1 l2 lo hi hlen hlo hhi h

theorem list_decompose_sublist__quicksort_range (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l) :
    l = sublist 0 lo l ++ (sublist lo hi l ++ sublist hi (Zlength l) l) :=
  list_decompose_sublist_local l lo hi hlo hhi

theorem same_outside_range_prefix__quicksort_range (l l1 : List Int) (left right : Int)
    (h : same_outside_range l l1 left right) (hl : 0 ≤ left ∧ left ≤ Zlength l) :
    sublist 0 left l1 = sublist 0 left l := same_outside_range_prefix_local l l1 left right h hl

theorem same_outside_range_suffix__quicksort_range (l l1 : List Int) (left right : Int)
    (h : same_outside_range l l1 left right) (hr : 0 ≤ right+1 ∧ right+1 ≤ Zlength l) :
    sublist (right+1) (Zlength l1) l1 = sublist (right+1) (Zlength l) l := same_outside_range_suffix_local l l1 left right h hr

theorem middle_permutation_of_same_outside__quicksort_range (l l1 : List Int) (left right : Int)
    (hp : permutation l l1) (h : same_outside_range l l1 left right)
    (hl : 0 ≤ left ∧ left ≤ right+1) (hr : right+1 ≤ Zlength l) :
    permutation (sublist left (right+1) l) (sublist left (right+1) l1) :=
  middle_permutation_of_same_outside_local l l1 left right hp h hl hr

theorem Forall_sublist_by_Znth__quicksort_range (P : Int → Prop) (l : List Int) (lo hi : Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l)
    (h : ∀ k, (lo ≤ k ∧ k < hi) → P (Znth k l 0)) : Forall P (sublist lo hi l) :=
  Forall_sublist_by_Znth_local P l lo hi hlo hhi h

theorem partitioned_at_preserved_by_left__quicksort_range (l l1 : List Int) (left right p : Int)
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

theorem partitioned_at_preserved_by_right__quicksort_range (l l1 : List Int) (left right p : Int)
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

private theorem read_swap (l : List Int) (i j k : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hj : 0 ≤ j ∧ j < Zlength l) (hk : 0 ≤ k ∧ k < Zlength l) :
    Znth k (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l)) 0 =
      if k=j then Znth i l 0 else if k=i then Znth j l 0 else Znth k l 0 := by
  by_cases hkj : k=j
  · subst k
    rw [if_pos rfl, Znth_replace_Znth_Same 0 _ j _ (by simpa only [Zlength_replace_Znth] using hj)]
  · rw [if_neg hkj, Znth_replace_Znth_Diff 0 _ j k _ (by simpa only [Zlength_replace_Znth] using hj)
      (by simpa only [Zlength_replace_Znth] using hk) (Ne.symm hkj)]
    by_cases hki : k=i
    · subst k
      rw [if_pos rfl, Znth_replace_Znth_Same 0 l i _ hi]
    · rw [if_neg hki, Znth_replace_Znth_Diff 0 l i k _ hi hk (Ne.symm hki)]

theorem partition_scan_inv_step_le__partition_scan (l l1 : List Int) (low high pivot i j : Int)
    (hlo : 0 ≤ low) (hlh : low ≤ high) (hhl : high < Zlength l1) (hle : Znth j l1 0 ≤ pivot)
    (hjh : j < high) (hli : low-1 ≤ i) (hij : i < j) (hjle : j ≤ high)
    (hs : partition_scan_inv l l1 low high pivot i j) :
    partition_scan_inv l (replace_Znth j (Znth (i+1) l1 0) (replace_Znth (i+1) (Znth j l1 0) l1))
      low high pivot (i+1) (j+1) := by
  have hir : 0 ≤ i+1 ∧ i+1 < Zlength l1 := by omega
  have hjr : 0 ≤ j ∧ j < Zlength l1 := by omega
  have hread := read_swap l1 (i+1) j
  refine ⟨hs.1.trans (permutation_swap_Znth__partition_scan l1 (i+1) j 0 hir hjr),
    same_outside_range_swap_inside__partition_scan l l1 low high (i+1) j hs.2.1 (by omega) (by omega) hir hjr, ?_, ?_, ?_⟩
  · rw [hread high hir hjr (by omega), if_neg (by omega), if_neg (by omega)]
    exact hs.2.2.1
  · intro k hk
    rw [hread k hir hjr (by omega)]
    split
    · rename_i he
      have : i+1=j := by omega
      simpa only [this] using hle
    · split
      · exact hle
      · exact hs.2.2.2.1 k (by omega)
  · intro k hk
    rw [hread k hir hjr (by omega)]
    split
    · have hg := hs.2.2.2.2 (i+1) (by omega)
      exact hg
    · rw [if_neg (by omega)]
      exact hs.2.2.2.2 k (by omega)

theorem partition_scan_inv_final_swap_partitioned_at__partition_scan (l l1 : List Int) (low high pivot i j : Int)
    (hlo : 0 ≤ low) (hlh : low ≤ high) (hli : low-1 ≤ i) (hhl : high < Zlength l1)
    (hjd : j ≥ high) (hij : i < j) (hjh : j ≤ high)
    (hs : partition_scan_inv l l1 low high pivot i j) :
    partitioned_at (replace_Znth high (Znth (i+1) l1 0) (replace_Znth (i+1) (Znth high l1 0) l1)) low high (i+1) := by
  have hir : 0 ≤ i+1 ∧ i+1 < Zlength l1 := by omega
  have hhr : 0 ≤ high ∧ high < Zlength l1 := by omega
  have hread := read_swap l1 (i+1) high
  have hpiv : Znth (i+1) (replace_Znth high (Znth (i+1) l1 0) (replace_Znth (i+1) (Znth high l1 0) l1)) 0 = pivot := by
    rw [hread (i+1) hir hhr hir]
    split
    · rename_i he
      simpa only [he] using hs.2.2.1
    · rw [if_pos rfl]
      exact hs.2.2.1
  refine ⟨by omega, ?_, ?_⟩
  · apply Forall_sublist_by_Znth__partition_scan _ _ low (i+1) (by omega) (by simp only [Zlength_replace_Znth]; omega)
    intro k hk
    rw [hpiv, hread k hir hhr (by omega), if_neg (by omega), if_neg (by omega)]
    exact hs.2.2.2.1 k (by omega)
  · apply Forall_sublist_by_Znth__partition_scan _ _ (i+1+1) (high+1) (by omega) (by simp only [Zlength_replace_Znth]; omega)
    intro k hk
    rw [hpiv, hread k hir hhr (by omega)]
    split
    · exact hs.2.2.2.2 (i+1) (by omega)
    · rw [if_neg (by omega)]
      exact hs.2.2.2.2 k (by omega)

theorem partition_scan_inv_final_same_outside__partition_scan (l l1 : List Int) (low high pivot i j : Int)
    (hlo : 0 ≤ low) (hlh : low ≤ high) (hli : low-1 ≤ i) (hhl : high < Zlength l1)
    (hjd : j ≥ high) (hij : i < j) (hjh : j ≤ high)
    (hs : partition_scan_inv l l1 low high pivot i j) :
    same_outside_range l (replace_Znth high (Znth (i+1) l1 0) (replace_Znth (i+1) (Znth high l1 0) l1)) low high :=
  same_outside_range_swap_inside__partition_scan l l1 low high (i+1) high hs.2.1 (by omega) (by omega) (by omega) (by omega)

theorem partition_scan_inv_final_permutation__partition_scan (l l1 : List Int) (low high pivot i j : Int)
    (hlo : 0 ≤ low) (hlh : low ≤ high) (hli : low-1 ≤ i) (hhl : high < Zlength l1)
    (hjd : j ≥ high) (hij : i < j) (hjh : j ≤ high)
    (hs : partition_scan_inv l l1 low high pivot i j) :
    permutation l (replace_Znth high (Znth (i+1) l1 0) (replace_Znth (i+1) (Znth high l1 0) l1)) :=
  hs.1.trans (permutation_swap_Znth__partition_scan l1 (i+1) high 0 (by omega) (by omega))

theorem partitioned_at_ext__quicksort_range (l l1 : List Int) (left right p : Int)
    (hl : 0 ≤ left) (hr : right < Zlength l) (hlen : Zlength l = Zlength l1)
    (he : ∀ k, (left ≤ k ∧ k ≤ right) → Znth k l1 0 = Znth k l 0)
    (hs : partitioned_at l left right p) : partitioned_at l1 left right p := by
  have hp := hs.1
  have hpiv := he p hp
  refine ⟨hp, ?_, ?_⟩
  · rw [hpiv, sublist_eq_from_Znth__quicksort_range l1 l left p hlen.symm (by omega) (by omega)
      (fun k hk => he k (by omega))]
    exact hs.2.1
  · rw [hpiv, sublist_eq_from_Znth__quicksort_range l1 l (p+1) (right+1) hlen.symm (by omega) (by omega)
      (fun k hk => he k (by omega))]
    exact hs.2.2

theorem sorted_range_ext__quicksort_range (l l1 : List Int) (left right : Int)
    (hl : 0 ≤ left) (hr : right < Zlength l) (hlen : Zlength l = Zlength l1)
    (he : ∀ k, (left ≤ k ∧ k ≤ right) → Znth k l1 0 = Znth k l 0)
    (hs : sorted_range l left right) : sorted_range l1 left right := by
  induction hs with
  | sorted_range_base left right hb => exact .sorted_range_base left right hb
  | sorted_range_from_left left right p hpr hp hs ih =>
    have hpbound := hp.1
    exact .sorted_range_from_left left right p hpr (partitioned_at_ext__quicksort_range l l1 left right p hl hr hlen he hp)
      (ih hl (by omega) (fun k hk => he k (by omega)))
  | sorted_range_from_right left right p hpl hp hs ih =>
    have hpbound := hp.1
    exact .sorted_range_from_right left right p hpl (partitioned_at_ext__quicksort_range l l1 left right p hl hr hlen he hp)
      (ih (by omega) hr (fun k hk => he k (by omega)))
  | sorted_range_from_both left right p hpr hp hls hrs ihl ihr =>
    have hpbound := hp.1
    exact .sorted_range_from_both left right p hpr (partitioned_at_ext__quicksort_range l l1 left right p hl hr hlen he hp)
      (ihl hl (by omega) (fun k hk => he k (by omega))) (ihr (by omega) hr (fun k hk => he k (by omega)))

private theorem sublist_lengthZ (lo hi : Int) (l : List Int)
    (hlo : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength l) :
    Zlength (sublist lo hi l) = hi-lo := ListLib.Zlength_sublist lo hi l hlo hhi

theorem increasing_aux_tail_increasing__quicksort_range (l : List Int) (x : Int)
    (h : increasing_aux l x) : increasing l := by
  cases l with
  | nil => trivial
  | cons y l => exact h.2

theorem increasing_aux_head_le_all__quicksort_range (l : List Int) (x k : Int)
    (h : increasing_aux l x) (hk : 0 ≤ k ∧ k < Zlength l) : x ≤ Znth k l 0 := by
  induction l generalizing x k with
  | nil => simp only [Zlength_nil] at hk; omega
  | cons y l ih =>
    by_cases hz : k=0
    · subst k; exact h.1
    · rw [Znth_cons 0 k y l (by omega)]
      exact Int.le_trans h.1 (ih y (k-1) h.2 (by simp only [Zlength_cons] at hk; omega))

theorem partitioned_at_left_Znth_le__quicksort_range (l : List Int) (left right p k : Int)
    (hl : 0 ≤ left) (hp : p ≤ Zlength l) (hs : partitioned_at l left right p)
    (hk : left ≤ k ∧ k < p) : Znth k l 0 ≤ Znth p l 0 := by
  have hlen := sublist_lengthZ left p l (by have := hs.1; omega) hp
  have h := Forall_Znth__quicksort_range _ _ (k-left) 0 hs.2.1 (by omega)
  rw [Znth_sublist 0 left (k-left) p l hl (by omega)] at h
  simpa only [Int.sub_add_cancel] using h

theorem partitioned_at_right_Znth_lt__quicksort_range (l : List Int) (left right p k : Int)
    (hl : 0 ≤ left) (hr : right < Zlength l) (hs : partitioned_at l left right p)
    (hk : p < k ∧ k ≤ right) : Znth p l 0 < Znth k l 0 := by
  have hlen := sublist_lengthZ (p+1) (right+1) l (by have := hs.1; omega) (by omega)
  have h := Forall_Znth__quicksort_range _ _ (k-(p+1)) 0 hs.2.2 (by omega)
  rw [Znth_sublist 0 (p+1) (k-(p+1)) (right+1) l (by have := hs.1; omega) (by omega)] at h
  simpa only [Int.sub_add_cancel] using h

private theorem partition_relax (l : List Int) (left right p : Int) (hs : partitioned_at l left right p) :
    SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib.partitioned_at l left right p := by
  refine ⟨hs.1, hs.2.1, Forall.iff_forall_mem.mpr ?_⟩
  intro x hx
  exact Int.le_of_lt (hs.2.2.mem hx)

theorem sorted_range_ordered__quicksort_range (l : List Int) (left right : Int)
    (hl : 0 ≤ left) (hr : right < Zlength l) (hs : sorted_range l left right) :
    ∀ i j, left ≤ i → i ≤ j → j ≤ right → Znth i l 0 ≤ Znth j l 0 := by
  induction hs with
  | sorted_range_base left right hb =>
    intro i j hi hij hj
    have : i=j := by omega
    simpa only [this] using Int.le_refl (Znth j l 0)
  | sorted_range_from_left left right p hpr hp hs ih =>
    have hpb := hp.1
    exact quicksort_partition_combine_left_only_local l left right p hl hr (by omega) (partition_relax l left right p hp)
      (ih hl (by omega))
  | sorted_range_from_right left right p hpl hp hs ih =>
    have hpb := hp.1
    exact quicksort_partition_combine_right_only_local l left right p hl hr (by omega) (partition_relax l left right p hp)
      (ih (by omega) hr)
  | sorted_range_from_both left right p hpr hp hls hrs ihl ihr =>
    exact quicksort_partition_combine_both_sides_local l left right p hl hr hpr (partition_relax l left right p hp)
      (ihl hl (by omega)) (ihr (by omega) hr)

theorem ordered_full_implies_increasing__quicksort_range (l : List Int)
    (h : ∀ i j, 0 ≤ i → i ≤ j → j ≤ Zlength l-1 → Znth i l 0 ≤ Znth j l 0) : increasing l := by
  have haux : ∀ t : List Int, ∀ x : Int, Sorting.increasing_aux t x → increasing_aux t x := by
    intro t
    induction t with
    | nil => intros; trivial
    | cons y t ih => intro x hx; exact ⟨hx.1, ih y hx.2⟩
  have hs := range_nondecreasing_full_to_increasing l h
  cases l with
  | nil => trivial
  | cons x l => exact haux l x hs

theorem sorted_range_implies_increasing__quicksort_range (l : List Int)
    (h : sorted_range l 0 (Zlength l-1)) : increasing l :=
  ordered_full_implies_increasing__quicksort_range l (sorted_range_ordered__quicksort_range l 0 (Zlength l-1) (by decide) (by omega) h)

theorem dedup_scan_inv_init__discretize_dedup (src sorted : List Int) (n : Int)
    (hp : permutation src sorted) (hi : increasing sorted) (hn : Zlength src=n) (hn1 : 1 ≤ n) :
    dedup_scan_inv src sorted sorted 0 1 := by
  have hlen : Zlength src = Zlength sorted := congrArg Int.ofNat hp.length_eq
  refine ⟨hlen, rfl, hp, hi, by omega, by omega, ⟨by omega, ?_⟩, ?_, ?_, ?_⟩
  · intro i j hij hj; omega
  · intro x; rfl
  · intros; rfl
  · rfl

theorem increasing_aux_tail_increasing__discretize_dedup (l : List Int) (x : Int)
    (h : increasing_aux l x) : increasing l := increasing_aux_tail_increasing__quicksort_range l x h

theorem increasing_aux_head_le_all__discretize_dedup (l : List Int) (x k : Int)
    (h : increasing_aux l x) (hk : 0 ≤ k ∧ k < Zlength l) : x ≤ Znth k l 0 :=
  increasing_aux_head_le_all__quicksort_range l x k h hk

theorem increasing_order__discretize_dedup (l : List Int) (i j : Int)
    (h : increasing l) (hij : 0 ≤ i ∧ i ≤ j) (hj : j < Zlength l) : Znth i l 0 ≤ Znth j l 0 := by
  induction l generalizing i j with
  | nil => simp only [Zlength_nil] at hj; omega
  | cons x l ih =>
    have hlen : Zlength (x::l) = Zlength l+1 := Zlength_cons x l
    by_cases hi0 : i=0
    · subst i
      by_cases hj0 : j=0
      · subst j; exact Int.le_refl _
      · rw [Znth_cons 0 j x l (by omega)]
        exact increasing_aux_head_le_all__quicksort_range l x (j-1) h (by omega)
    · rw [Znth_cons 0 i x l (by omega), Znth_cons 0 j x l (by omega)]
      exact ih (i-1) (j-1) (increasing_aux_tail_increasing__quicksort_range l x h) (by omega) (by omega)

theorem sublist0_extend_in_iff__discretize_dedup (l : List Int) (n x : Int)
    (hn : 0 ≤ n ∧ n < Zlength l) : x ∈ sublist 0 (n+1) l ↔ x ∈ sublist 0 n l ∨ x=Znth n l 0 := by
  rw [sublist_split 0 (n+1) n l (by omega) (by omega), sublist_single 0 n l hn, List.mem_append, List.mem_singleton]

theorem sublist0_Znth_In__discretize_dedup (l : List Int) (n i : Int)
    (hi : 0 ≤ i ∧ i < n) (hn : n ≤ Zlength l) : Znth i l 0 ∈ sublist 0 n l := by
  have hlen := sublist_lengthZ 0 n l (by omega) hn
  have hin : i.toNat < (sublist 0 n l).length := by simp only [Zlength, Int.ofNat_eq_coe] at hlen; omega
  have hmem : Znth i (sublist 0 n l) 0 ∈ sublist 0 n l := by
    simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin, Option.getD_some] using List.getElem_mem hin
  rw [Znth_sublist 0 0 i n l (by decide) (by omega), Int.add_zero] at hmem
  exact hmem

theorem sublist0_In_Znth_exists__discretize_dedup (l : List Int) (n x : Int)
    (hn : 0 ≤ n ∧ n ≤ Zlength l) (hx : x ∈ sublist 0 n l) :
    ∃ i, (0 ≤ i ∧ i < n) ∧ Znth i l 0=x := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
  have hlen := sublist_lengthZ 0 n l (by omega) hn.2
  have hib : 0 ≤ (i : Int) ∧ (i : Int)<n := by simp only [Zlength, Int.ofNat_eq_coe] at hlen; omega
  refine ⟨i, hib, ?_⟩
  have heq : Znth (i : Int) (sublist 0 n l) 0=x := by
    simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using he
  rw [Znth_sublist 0 0 i n l (by decide) (by omega), Int.add_zero] at heq
  exact heq

theorem sublist0_replace_prefix__discretize_dedup (l : List Int) (i v : Int)
    (hi : 0 ≤ i ∧ i ≤ Zlength l) : sublist 0 i (replace_Znth i v l)=sublist 0 i l := by
  by_cases he : i=Zlength l
  · rw [replace_Znth_nothing i l v (by omega)]
  · apply sublist_eq_from_Znth__quicksort_range _ l 0 i (Zlength_replace_Znth l i v) (by omega) (by simp only [Zlength_replace_Znth]; omega)
    intro k hk
    exact Znth_replace_Znth_Diff 0 l i k v (by omega) (by omega) (by omega)

theorem sublist0_replace_next_in_iff__discretize_dedup (l : List Int) (i v x : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) :
    x ∈ sublist 0 (i+1) (replace_Znth i v l) ↔ x ∈ sublist 0 i l ∨ x=v := by
  rw [sublist0_extend_in_iff__discretize_dedup _ i x (by simpa only [Zlength_replace_Znth] using hi),
    sublist0_replace_prefix__discretize_dedup l i v (by omega), Znth_replace_Znth_Same 0 l i v hi]

theorem dedup_scan_inv_step_duplicate__discretize_dedup (src sorted cur : List Int) (slow fast : Int)
    (hs : dedup_scan_inv src sorted cur slow fast) (hf : fast < Zlength sorted)
    (he : Znth fast cur 0=Znth slow cur 0) : dedup_scan_inv src sorted cur slow (fast+1) := by
  obtain ⟨hsrc, hcur, hp, hi, hfb, hsb, hstrict, hsame, htail, hlast⟩ := hs
  have hfast := htail fast (by omega)
  refine ⟨hsrc, hcur, hp, hi, by omega, by omega, hstrict, ?_, ?_, ?_⟩
  · intro x
    rw [sublist0_extend_in_iff__discretize_dedup sorted fast x (by omega)]
    constructor
    · intro hx; exact Or.inl ((hsame x).mp hx)
    · rintro (hx|heq)
      · exact (hsame x).mpr hx
      · rw [heq, ← hfast, he]
        exact sublist0_Znth_In__discretize_dedup cur (slow+1) slow (by omega) (by omega)
  · intro k hk; exact htail k (by omega)
  · simp only [Int.add_sub_cancel]
    omega

theorem dedup_scan_inv_step_new__discretize_dedup (src sorted cur : List Int) (slow fast : Int)
    (hs : dedup_scan_inv src sorted cur slow fast) (hf : fast < Zlength sorted)
    (hne : Znth fast cur 0≠Znth slow cur 0) :
    dedup_scan_inv src sorted (replace_Znth (slow+1) (Znth fast cur 0) cur) (slow+1) (fast+1) := by
  obtain ⟨hsrc, hcur, hp, hi, hfb, hsb, hstrict, hsame, htail, hlast⟩ := hs
  have hfast := htail fast (by omega)
  have hsfl : Znth slow cur 0 < Znth fast cur 0 := by
    have ho := increasing_order__discretize_dedup sorted (fast-1) fast hi (by omega) hf
    omega
  have hir : 0 ≤ slow+1 ∧ slow+1 < Zlength cur := by omega
  refine ⟨hsrc, by simpa only [Zlength_replace_Znth] using hcur, hp, hi, by omega, by omega,
    ⟨by simp only [Zlength_replace_Znth]; omega, ?_⟩, ?_, ?_, ?_⟩
  · intro i j hij hj
    by_cases hjold : j < slow+1
    · rw [Znth_replace_Znth_Diff 0 cur (slow+1) i _ hir (by omega) (by omega),
        Znth_replace_Znth_Diff 0 cur (slow+1) j _ hir (by omega) (by omega)]
      exact hstrict.2 i j hij hjold
    · have hej : j=slow+1 := by omega
      subst j
      rw [Znth_replace_Znth_Same 0 cur (slow+1) _ hir,
        Znth_replace_Znth_Diff 0 cur (slow+1) i _ hir (by omega) (by omega)]
      by_cases his : i=slow
      · simpa only [his] using hsfl
      · have ho := hstrict.2 i slow (by omega) (by omega)
        omega
  · intro x
    rw [sublist0_replace_next_in_iff__discretize_dedup cur (slow+1) (Znth fast cur 0) x hir,
      sublist0_extend_in_iff__discretize_dedup sorted fast x (by omega), hsame x, hfast]
  · intro k hk
    rw [Znth_replace_Znth_Diff 0 cur (slow+1) k _ hir (by omega) (by omega)]
    exact htail k (by omega)
  · rw [Znth_replace_Znth_Same 0 cur (slow+1) _ hir, Int.add_sub_cancel]
    exact hfast

theorem dedup_scan_inv_to_discretize_result__discretize_dedup (src sorted cur : List Int) (slow n : Int)
    (hs : dedup_scan_inv src sorted cur slow n) (hlen : Zlength src=n) (hn : 1 ≤ n) :
    discretize_resultLegacy src n cur (slow+1) := by
  obtain ⟨hsrc, hcur, hp, hi, hnb, hsb, hstrict, hsame, htail, hlast⟩ := hs
  have hsorted : Zlength sorted=n := by omega
  have hcur_n : Zlength cur=n := by omega
  have hsame_src : same_values_prefix cur (slow+1) src n := by
    intro x
    have he := hsame x
    rw [sublist_self sorted n hsorted.symm] at he
    rw [sublist_self src n hlen.symm]
    exact he.trans (List.Perm.mem_iff hp).symm
  refine ⟨hlen, hcur_n, hn, by omega, hstrict, hsame_src, ?_, ?_, ?_⟩
  · intro i hi
    have hmem := sublist0_Znth_In__discretize_dedup src n i hi (by omega)
    exact sublist0_In_Znth_exists__discretize_dedup cur (slow+1) (Znth i src 0) (by omega) ((hsame_src _).mpr hmem)
  · intro r hr
    have hmem := sublist0_Znth_In__discretize_dedup cur (slow+1) r hr (by omega)
    obtain ⟨i, hi, he⟩ := sublist0_In_Znth_exists__discretize_dedup src n (Znth r cur 0) (by omega) ((hsame_src _).mp hmem)
    exact ⟨i, hi, he.symm⟩
  · intro i j ri rj hi hj hri hrj hei hej
    have hless : ri<rj → Znth ri cur 0<Znth rj cur 0 := fun hlt => hstrict.2 ri rj (by omega) (by omega)
    have hgreater : rj<ri → Znth rj cur 0<Znth ri cur 0 := fun hlt => hstrict.2 rj ri (by omega) (by omega)
    constructor
    · intro heq
      by_cases hlt : ri<rj
      · have := hless hlt; omega
      · by_cases hgt : rj<ri
        · have := hgreater hgt; omega
        · omega
    · intro hlt
      by_cases heq : ri=rj
      · subst rj; omega
      · by_cases hgt : rj<ri
        · have := hgreater hgt; omega
        · omega

theorem midpoint_between_bounds__query_forward_search (low high : Int) (h : low ≤ high) :
    low ≤ low+Z.quot (high-low) 2 ∧ low+Z.quot (high-low) 2 ≤ high := by
  have he := Z.quot_rem (high-low) 2 (by decide)
  have hb := rem_nonneg_bounds (high-low) 2 (by omega) (by decide)
  omega

theorem strict_increasing_Znth_lt__query_forward_search (l : List Int) (i j : Int)
    (hs : strict_increasing l) (hi : 0 ≤ i ∧ i<j) (hj : j<Zlength l) : Znth i l 0<Znth j l 0 := hs.2 i j hi hj

theorem query_forward_search_inv_init__query_forward_search (map : List Int) (map_size target : Int)
    (hm : 0 ≤ map_size) : query_forward_search_inv map map_size target 0 (map_size-1) :=
  ⟨by decide, by omega, by omega, by intro i hi; omega, by intro i hi; omega⟩

theorem query_forward_search_inv_step_right__query_forward_search (map : List Int) (map_size target low mid high : Int)
    (hlen : Zlength map=map_size) (hs : strict_increasing map) (hi : query_forward_search_inv map map_size target low high)
    (hlm : low ≤ mid) (hmh : mid ≤ high) (hlt : Znth mid map 0<target) :
    query_forward_search_inv map map_size target (mid+1) high := by
  obtain ⟨hl, hh, hlh, hbefore, hafter⟩ := hi
  refine ⟨by omega, hh, by omega, ?_, hafter⟩
  intro i hir
  by_cases hil : i<low
  · exact hbefore i (by omega)
  · by_cases him : i=mid
    · simpa only [him] using hlt
    · have ho := strict_increasing_Znth_lt__query_forward_search map i mid hs (by omega) (by omega)
      omega

theorem query_forward_search_inv_step_left__query_forward_search (map : List Int) (map_size target low mid high : Int)
    (hlen : Zlength map=map_size) (hs : strict_increasing map) (hi : query_forward_search_inv map map_size target low high)
    (hlm : low ≤ mid) (hmh : mid ≤ high) (hge : Znth mid map 0 ≥ target) (hne : Znth mid map 0≠target) :
    query_forward_search_inv map map_size target low (mid-1) := by
  obtain ⟨hl, hh, hlh, hbefore, hafter⟩ := hi
  refine ⟨hl, by omega, by omega, hbefore, ?_⟩
  intro i hir
  by_cases hhi : high<i
  · exact hafter i (by omega)
  · by_cases him : i=mid
    · subst i; omega
    · have ho := strict_increasing_Znth_lt__query_forward_search map mid i hs (by omega) (by omega)
      omega

theorem query_forward_result_not_found__query_forward_search (map : List Int) (map_size target low high : Int)
    (hi : query_forward_search_inv map map_size target low high) (hgt : low>high) (hle : low ≤ high+1) :
    query_forward_resultLegacy map map_size target (-1) := by
  obtain ⟨hl, hh, hlh, hbefore, hafter⟩ := hi
  refine Or.inr ⟨?_, rfl⟩
  intro i hir he
  by_cases hil : i<low
  · have := hbefore i (by omega); omega
  · have := hafter i (by omega); omega

theorem query_forward_result_found_unique__query_forward_search (map : List Int) (map_size target mid : Int)
    (hlen : Zlength map=map_size) (hs : strict_increasing map) (hm : 0 ≤ mid ∧ mid<map_size)
    (he : Znth mid map 0=target) : query_forward_resultLegacy map map_size target mid := by
  refine Or.inl ⟨⟨mid, hm, he, rfl⟩, ?_⟩
  intro j hj hej
  by_cases hmj : mid<j
  · have := strict_increasing_Znth_lt__query_forward_search map mid j hs (by omega) (by omega)
    omega
  · by_cases hjm : j<mid
    · have := strict_increasing_Znth_lt__query_forward_search map j mid hs (by omega) (by omega)
      omega
    · omega

end SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_lib

namespace SimpleC.EE.LLM_bench.Algorithms.discretize
export discretize_lib (permutation increasing_aux increasing same_outside_range partitioned_at partition_scan_inv sorted_range strict_increasing_prefix strict_increasing same_values_prefix dedup_scan_inv discretize_resultLegacy query_forward_resultLegacy query_forward_search_inv)
end SimpleC.EE.LLM_bench.Algorithms.discretize

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_lib
open AUXLib

def discretize_result (src out : List Int) (ret : Int) : Prop :=
  (0 ≤ ret ∧ ret ≤ Zlength out) ∧ strict_increasing_prefix out ret ∧
  ∀ x, In x (sublist 0 ret out) ↔ In x src
def query_forward_result (values : List Int) (target ret : Int) : Prop :=
  ((0 ≤ ret ∧ ret < Zlength values) ∧ Znth ret values 0 = target) ∨
    (ret = -1 ∧ ¬ In target values)

end SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_lib
namespace SimpleC.EE.LLM_bench.Algorithms.discretize
export discretize_lib (discretize_result query_forward_result)
end SimpleC.EE.LLM_bench.Algorithms.discretize
