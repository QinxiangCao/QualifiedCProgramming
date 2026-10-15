import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import ListLib.General.Length

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_lib
open AUXLib

def zrange (n : Int) : List Int := (List.range n.toNat).map Int.ofNat

def zrange_between (lo hi : Int) : List Int :=
  (List.range (hi - lo + 1).toNat).map (fun t : Nat => lo + (t : Int))

def affordable_betweenb (costs : List Int) (p lo hi : Int) : Bool :=
  (zrange_between lo hi).any (fun idx => decide (Znth idx costs 0 ≤ p))

def same_colorb (colors : List Int) (a b : Int) : Bool :=
  decide (Znth a colors 0 = Znth b colors 0)

def choosing_pairb (colors costs : List Int) (p : Int) (pair : Int × Int) : Bool :=
  same_colorb colors pair.1 pair.2 && affordable_betweenb costs p pair.1 pair.2

def choosing_pairs_up_to (n : Int) : List (Int × Int) :=
  (zrange n).flatMap (fun right => (zrange right).map (fun left => (left, right)))

def choosing_pair_count (colors costs : List Int) (p n : Int) : Int :=
  Int.ofNat ((choosing_pairs_up_to n).filter (choosing_pairb colors costs p)).length

def color_count (colors : List Int) (limit color : Int) : Int :=
  Int.ofNat ((zrange limit).filter (fun idx => decide (Znth idx colors 0 = color))).length

def good_color_count (colors costs : List Int) (limit p color : Int) : Int :=
  Int.ofNat ((zrange limit).filter (fun idx => decide (Znth idx colors 0 = color) &&
    affordable_betweenb costs p idx (limit - 1))).length

def ChoosingInputSafe (colors costs : List Int) (n k p : Int) : Prop :=
  (0 ≤ n ∧ n ≤ 200000) ∧ (1 ≤ k ∧ k ≤ 50) ∧ (0 ≤ p ∧ p ≤ 100) ∧
  Zlength colors = n ∧ Zlength costs = n ∧
  (∀ idx, (0 ≤ idx ∧ idx < n) → 0 ≤ Znth idx colors 0 ∧ Znth idx colors 0 < k) ∧
  (∀ idx, (0 ≤ idx ∧ idx < n) → 0 ≤ Znth idx costs 0 ∧ Znth idx costs 0 ≤ 100)

def CountArraySafe (xs : List Int) (k limit : Int) : Prop :=
  Zlength xs = k ∧ ∀ idx, (0 ≤ idx ∧ idx < k) → 0 ≤ Znth idx xs 0 ∧ Znth idx xs 0 ≤ limit

def CountsZeroPrefix (xs : List Int) (written : Int) : Prop :=
  Zlength xs = written ∧ ∀ idx, (0 ≤ idx ∧ idx < written) → Znth idx xs 0 = 0

def CountsZeroFull (k : Int) (xs : List Int) : Prop :=
  Zlength xs = k ∧ ∀ idx, (0 ≤ idx ∧ idx < k) → Znth idx xs 0 = 0

def CopyCountsPrefix (src old dst : List Int) (written k : Int) : Prop :=
  (∀ idx, (0 ≤ idx ∧ idx < written) → Znth idx dst 0 = Znth idx src 0) ∧
  (∀ idx, (written ≤ idx ∧ idx < k) → Znth idx dst 0 = Znth idx old 0)

def ChoosingPrefixDataSafe (colors costs : List Int) (limit k : Int) (seen good : List Int) : Prop :=
  (0 ≤ limit ∧ limit ≤ Zlength colors) ∧ Zlength costs = Zlength colors ∧
  CountArraySafe seen k limit ∧ CountArraySafe good k limit

def ChoosingPrefixState (colors costs : List Int) (limit k p answer : Int) (seen good : List Int) : Prop :=
  answer = choosing_pair_count colors costs p limit ∧
  (∀ color, (0 ≤ color ∧ color < k) → Znth color seen 0 = color_count colors limit color) ∧
  (∀ color, (0 ≤ color ∧ color < k) → Znth color good 0 = good_color_count colors costs limit p color)

def ChoosingInnsAnswer (colors costs : List Int) (n k p answer : Int) : Prop :=
  answer = choosing_pair_count colors costs p n

theorem CountsZeroPrefix_nil : CountsZeroPrefix [] 0 := by
  refine ⟨rfl, ?_⟩; intro idx h; omega

theorem CountsZeroPrefix_snoc_zero (xs : List Int) (i : Int)
    (h : CountsZeroPrefix xs i) (hi : 0 ≤ i) : CountsZeroPrefix (xs ++ [0]) (i + 1) := by
  refine ⟨by have := h.1; simp only [Zlength, Int.ofNat_eq_coe, List.length_append, List.length_cons, List.length_nil, Int.natCast_add] at *; omega, ?_⟩
  intro idx hidx
  by_cases hlt : idx < i
  · have he : Znth idx (xs ++ [0]) 0 = Znth idx xs 0 := ListLib.app_Znth1 0 xs [0] idx (by change 0 ≤ idx ∧ idx < Zlength xs; have := h.1; omega)
    rw [he]; exact h.2 idx (by omega)
  · have he : idx = i := by omega
    subst idx
    rw [app_Znth2 0 xs [0] i (by have := h.1; omega), h.1, Int.sub_self]
    rfl

theorem CountsZeroPrefix_to_full (xs : List Int) (k : Int) (h : CountsZeroPrefix xs k) :
    CountsZeroFull k xs := h

theorem CopyCountsPrefix_zero (src old : List Int) (k : Int)
    (hs : Zlength src = k) (ho : Zlength old = k) : CopyCountsPrefix src old old 0 k := by
  refine ⟨?_, ?_⟩
  · intro idx h; omega
  · intro idx h; rfl

theorem CopyCountsPrefix_step_replace (src old dst : List Int) (i k : Int)
    (h : CopyCountsPrefix src old dst i k) (hd : Zlength dst = k) (hi : 0 ≤ i ∧ i < k) :
    CopyCountsPrefix src old (replace_Znth i (Znth i src 0) dst) (i + 1) k := by
  refine ⟨?_, ?_⟩
  · intro idx hidx
    by_cases he : idx = i
    · subst idx; exact Znth_replace_Znth_Same 0 dst i _ (by omega)
    · rw [Znth_replace_Znth_Diff 0 dst i idx _ (by omega) (by omega) (Ne.symm he)]
      exact h.1 idx (by omega)
  · intro idx hidx
    rw [Znth_replace_Znth_Diff 0 dst i idx _ (by omega) (by omega) (by omega)]
    exact h.2 idx (by omega)

theorem CopyCountsPrefix_full_eq (src old dst : List Int) (i k : Int)
    (h : CopyCountsPrefix src old dst i k) (hs : Zlength src = k) (hd : Zlength dst = k)
    (hge : i ≥ k) (hle : i ≤ k) : dst = src := by
  apply (ListLib.list_eq_ext _ _ 0).mpr
  refine ⟨by change Zlength dst = Zlength src; omega, ?_⟩
  intro idx hidx
  exact h.1 idx (by change 0 ≤ idx ∧ idx < Zlength dst at hidx; omega)

theorem replace_Znth_preserves_bounds (xs : List Int) (i v k lo hi : Int)
    (hl : Zlength xs = k) (hir : 0 ≤ i ∧ i < k) (hv : lo ≤ v ∧ v ≤ hi)
    (hb : ∀ idx, (0 ≤ idx ∧ idx < k) → lo ≤ Znth idx xs 0 ∧ Znth idx xs 0 ≤ hi)
    (idx : Int) (hidx : 0 ≤ idx ∧ idx < k) :
    lo ≤ Znth idx (replace_Znth i v xs) 0 ∧ Znth idx (replace_Znth i v xs) 0 ≤ hi := by
  by_cases he : idx = i
  · subst idx; rw [Znth_replace_Znth_Same 0 xs i v (by omega)]; exact hv
  · rw [Znth_replace_Znth_Diff 0 xs i idx v (by omega) (by omega) (Ne.symm he)]; exact hb idx hidx

theorem CountArraySafe_weaken_limit (xs : List Int) (k old_limit new_limit : Int)
    (h : CountArraySafe xs k old_limit) (hle : old_limit ≤ new_limit) : CountArraySafe xs k new_limit := by
  refine ⟨h.1, ?_⟩; intro idx hidx; have := h.2 idx hidx; omega

theorem CountArraySafe_increment_at (xs : List Int) (k limit c : Int)
    (h : CountArraySafe xs k limit) (hc : 0 ≤ c ∧ c < k) :
    CountArraySafe (replace_Znth c (Znth c xs 0 + 1) xs) k (limit + 1) := by
  refine ⟨by simpa only [Zlength_replace_Znth] using h.1, ?_⟩
  apply replace_Znth_preserves_bounds xs c _ k 0 (limit + 1) h.1 hc
  · have := h.2 c hc; omega
  · intro idx hi; have := h.2 idx hi; omega

theorem ChoosingPrefixDataSafe_step_affordable_after_copy (colors costs : List Int) (i k : Int) (seen good : List Int) (c : Int)
    (h : ChoosingPrefixDataSafe colors costs i k seen good) (hi : i < Zlength colors) (hc : 0 ≤ c ∧ c < k) :
    ChoosingPrefixDataSafe colors costs (i + 1) k
      (replace_Znth c (Znth c seen 0 + 1) seen) (replace_Znth c (Znth c seen 0 + 1) seen) := by
  exact ⟨by have := h.1; omega, h.2.1, CountArraySafe_increment_at seen k i c h.2.2.1 hc,
    CountArraySafe_increment_at seen k i c h.2.2.1 hc⟩

theorem ChoosingPrefixDataSafe_step_expensive (colors costs : List Int) (i k : Int) (seen good : List Int) (c : Int)
    (h : ChoosingPrefixDataSafe colors costs i k seen good) (hi : i < Zlength colors) (hc : 0 ≤ c ∧ c < k) :
    ChoosingPrefixDataSafe colors costs (i + 1) k (replace_Znth c (Znth c seen 0 + 1) seen) good := by
  exact ⟨by have := h.1; omega, h.2.1, CountArraySafe_increment_at seen k i c h.2.2.1 hc,
    CountArraySafe_weaken_limit good k i (i + 1) h.2.2.2 (by omega)⟩

theorem choosing_pair_count_zero (colors costs : List Int) (p : Int) : choosing_pair_count colors costs p 0 = 0 := rfl

theorem color_count_zero (colors : List Int) (color : Int) : color_count colors 0 color = 0 := rfl

theorem good_color_count_zero (colors costs : List Int) (p color : Int) : good_color_count colors costs 0 p color = 0 := rfl

theorem CountsZeroFull_to_ChoosingPrefixState_zero (colors costs : List Int) (k p : Int) (seen good : List Int)
    (hs : CountsZeroFull k seen) (hg : CountsZeroFull k good) : ChoosingPrefixState colors costs 0 k p 0 seen good := by
  refine ⟨rfl, ?_, ?_⟩
  · intro c hc; rw [hs.2 c hc, color_count_zero]
  · intro c hc; rw [hg.2 c hc, good_color_count_zero]

theorem CountsZeroFull_to_CountArraySafe_zero (k : Int) (xs : List Int) (h : CountsZeroFull k xs) :
    CountArraySafe xs k 0 := by
  refine ⟨h.1, ?_⟩; intro idx hi; rw [h.2 idx hi]; omega

theorem CountsZeroFull_to_ChoosingPrefixDataSafe_zero (colors costs : List Int) (k : Int) (seen good : List Int)
    (hs : CountsZeroFull k seen) (hg : CountsZeroFull k good) (hcosts : Zlength costs = Zlength colors) :
    ChoosingPrefixDataSafe colors costs 0 k seen good := by
  exact ⟨by simp [Zlength], hcosts, CountsZeroFull_to_CountArraySafe_zero k seen hs,
    CountsZeroFull_to_CountArraySafe_zero k good hg⟩

theorem CountsZeroFull_bounds_zero (k : Int) (xs : List Int) (idx : Int)
    (h : CountsZeroFull k xs) (hi : 0 ≤ idx ∧ idx < k) : 0 ≤ Znth idx xs 0 ∧ Znth idx xs 0 ≤ 0 := by
  rw [h.2 idx hi]; omega

theorem ChoosingPrefixState_to_ChoosingInnsAnswer_full (colors costs : List Int) (n k p answer : Int) (seen good : List Int)
    (hc : Zlength colors = n) (h : ChoosingPrefixState colors costs n k p answer seen good) (hk : 1 ≤ k) :
    ChoosingInnsAnswer colors costs n k p answer := h.1

theorem zrange_length_nonneg (n : Int) (hn : 0 ≤ n) : Zlength (zrange n) = n := by
  simp only [Zlength, zrange, List.length_map, List.length_range, Int.ofNat_eq_coe]
  omega

theorem zrange_snoc (n : Int) (hn : 0 ≤ n) : zrange (n + 1) = zrange n ++ [n] := by
  unfold zrange
  have he : (n + 1).toNat = n.toNat + 1 := by omega
  rw [he, List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil]
  have hc : Int.ofNat n.toNat = n := by simpa only [Int.ofNat_eq_coe] using Int.toNat_of_nonneg hn
  rw [hc]

theorem zrange_In (x n : Int) (h : x ∈ zrange n) : 0 ≤ x ∧ x < n := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h
  have hm' := List.mem_range.mp hm
  simp only [Int.ofNat_eq_coe]
  omega

theorem zrange_between_snoc (lo hi : Int) (h : lo ≤ hi) :
    zrange_between lo hi = zrange_between lo (hi - 1) ++ [hi] := by
  unfold zrange_between
  have he : (hi - lo + 1).toNat = (hi - lo).toNat + 1 := by omega
  rw [he, List.range_succ, List.map_append]
  have he1 : hi - 1 - lo + 1 = hi - lo := by omega
  have he2 : lo + ((hi - lo).toNat : Int) = hi := by omega
  simp only [he1, List.map_cons, List.map_nil, he2]

theorem affordable_betweenb_hi_true (costs : List Int) (p lo hi : Int)
    (hl : lo ≤ hi) (hc : Znth hi costs 0 ≤ p) : affordable_betweenb costs p lo hi = true := by
  unfold affordable_betweenb
  rw [zrange_between_snoc lo hi hl]
  simp [hc]

theorem affordable_betweenb_extend_expensive (costs : List Int) (p lo hi : Int)
    (hl : lo ≤ hi) (hc : p < Znth hi costs 0) :
    affordable_betweenb costs p lo hi = affordable_betweenb costs p lo (hi - 1) := by
  unfold affordable_betweenb
  rw [zrange_between_snoc lo hi hl]
  simp [show ¬ Znth hi costs 0 ≤ p by omega]

theorem affordable_betweenb_single_expensive (costs : List Int) (p i : Int)
    (hc : p < Znth i costs 0) : affordable_betweenb costs p i i = false := by
  unfold affordable_betweenb zrange_between
  simp [show ¬ Znth i costs 0 ≤ p by omega]

theorem filter_length_le {A : Type} (f : A → Bool) (xs : List A) :
    (xs.filter f).length ≤ xs.length := List.length_filter_le f xs

theorem filter_map_ext_in {A B : Type} (f : A → B) (p : B → Bool) (q : A → Bool) (xs : List A)
    (h : ∀ x, x ∈ xs → p (f x) = q x) : (xs.map f).filter p = (xs.filter q).map f := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  exact h

theorem choosing_pairs_up_to_snoc (n : Int) (hn : 0 ≤ n) :
    choosing_pairs_up_to (n + 1) = choosing_pairs_up_to n ++ (zrange n).map (fun left => (left, n)) := by
  unfold choosing_pairs_up_to
  rw [zrange_snoc n hn]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem choosing_pairs_up_to_Zlength_twice (n : Int) (hn : 0 ≤ n) :
    2 * Zlength (choosing_pairs_up_to n) = n * (n - 1) := by
  have he : n = (n.toNat : Int) := by omega
  rw [he]
  generalize n.toNat = m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Int.natCast_succ, choosing_pairs_up_to_snoc _ (by omega), Zlength_app]
    have hm : Zlength ((zrange (m : Int)).map (fun left => (left, (m : Int)))) = (m : Int) := by
      simpa only [Zlength, List.length_map] using zrange_length_nonneg (m : Int) (by omega)
    rw [hm]
    simp only [Int.add_sub_cancel, Int.add_mul, Int.mul_add, Int.mul_sub, Int.one_mul, Int.mul_one] at *
    omega

theorem choosing_pair_count_prefix_bound (colors costs : List Int) (p limit n : Int)
    (hl : 0 ≤ limit ∧ limit ≤ n) (hn : n ≤ 200000) :
    0 ≤ choosing_pair_count colors costs p limit ∧ choosing_pair_count colors costs p limit ≤ 19999900000 := by
  have hf := filter_length_le (choosing_pairb colors costs p) (choosing_pairs_up_to limit)
  have hc : choosing_pair_count colors costs p limit ≤ Zlength (choosing_pairs_up_to limit) := by
    unfold choosing_pair_count Zlength
    simp only [Int.ofNat_eq_coe]
    omega
  have ht := choosing_pairs_up_to_Zlength_twice limit hl.1
  have hp : limit * (limit - 1) ≤ 39999800000 := by
    by_cases he : limit = 0
    · simp [he]
    · have hm := Int.mul_le_mul_of_nonneg_right (show limit ≤ 200000 by omega) (show 0 ≤ limit - 1 by omega)
      omega
  refine ⟨?_, by omega⟩
  unfold choosing_pair_count
  simp only [Int.ofNat_eq_coe]
  omega

theorem color_count_snoc (colors : List Int) (i color : Int) (hi : 0 ≤ i) :
    color_count colors (i + 1) color = color_count colors i color + (if decide (Znth i colors 0 = color) then 1 else 0) := by
  unfold color_count
  rw [zrange_snoc i hi, List.filter_append, List.length_append]
  by_cases he : Znth i colors 0 = color <;> simp [he]

theorem good_color_count_affordable_as_color_count (colors costs : List Int) (i p color : Int)
    (hi : 0 ≤ i) (hc : Znth i costs 0 ≤ p) :
    good_color_count colors costs (i + 1) p color = color_count colors (i + 1) color := by
  unfold good_color_count color_count
  congr 2
  apply List.filter_congr
  intro idx hidx
  have hr := zrange_In idx (i + 1) hidx
  rw [show i + 1 - 1 = i by omega, affordable_betweenb_hi_true costs p idx i (by omega) hc]
  simp

theorem good_color_count_snoc_expensive (colors costs : List Int) (i p color : Int)
    (hi : 0 ≤ i) (hc : p < Znth i costs 0) :
    good_color_count colors costs (i + 1) p color = good_color_count colors costs i p color := by
  unfold good_color_count
  rw [zrange_snoc i hi, List.filter_append, List.length_append]
  have hf : (zrange i).filter (fun idx => decide (Znth idx colors 0 = color) && affordable_betweenb costs p idx (i + 1 - 1)) =
      (zrange i).filter (fun idx => decide (Znth idx colors 0 = color) && affordable_betweenb costs p idx (i - 1)) := by
    apply List.filter_congr
    intro idx hidx
    have hr := zrange_In idx i hidx
    rw [show i + 1 - 1 = i by omega, affordable_betweenb_extend_expensive costs p idx i (by omega) hc]
  rw [hf]
  simp only [Int.add_sub_cancel, affordable_betweenb_single_expensive costs p i hc, Bool.and_false,
    List.filter_cons_of_neg, Bool.false_eq_true, not_false_eq_true, List.filter_nil, List.length_nil, Nat.add_zero]

theorem choosing_pair_count_snoc_affordable (colors costs : List Int) (p i c : Int)
    (hi : 0 ≤ i) (hcolor : c = Znth i colors 0) (hc : Znth i costs 0 ≤ p) :
    choosing_pair_count colors costs p (i + 1) = choosing_pair_count colors costs p i + color_count colors i c := by
  unfold choosing_pair_count
  rw [choosing_pairs_up_to_snoc i hi, List.filter_append, List.length_append]
  have hm : ((zrange i).map (fun left => (left, i))).filter (choosing_pairb colors costs p) =
      ((zrange i).filter (fun idx => decide (Znth idx colors 0 = c))).map (fun left => (left, i)) := by
    apply filter_map_ext_in
    intro left hleft
    have hr := zrange_In left i hleft
    unfold choosing_pairb same_colorb
    rw [← hcolor, affordable_betweenb_hi_true costs p left i (by omega) hc]
    simp
  rw [hm, List.length_map]
  rfl

theorem choosing_pair_count_snoc_expensive (colors costs : List Int) (p i c : Int)
    (hi : 0 ≤ i) (hcolor : c = Znth i colors 0) (hc : p < Znth i costs 0) :
    choosing_pair_count colors costs p (i + 1) = choosing_pair_count colors costs p i + good_color_count colors costs i p c := by
  unfold choosing_pair_count
  rw [choosing_pairs_up_to_snoc i hi, List.filter_append, List.length_append]
  have hm : ((zrange i).map (fun left => (left, i))).filter (choosing_pairb colors costs p) =
      ((zrange i).filter (fun idx => decide (Znth idx colors 0 = c) && affordable_betweenb costs p idx (i - 1))).map (fun left => (left, i)) := by
    apply filter_map_ext_in
    intro left hleft
    have hr := zrange_In left i hleft
    unfold choosing_pairb same_colorb
    rw [← hcolor, affordable_betweenb_extend_expensive costs p left i (by omega) hc]
  rw [hm, List.length_map]
  rfl

theorem ChoosingPrefixState_answer_bound (colors costs : List Int) (limit k p answer : Int) (seen good : List Int) (n : Int)
    (hs : ChoosingPrefixDataSafe colors costs limit k seen good) (hst : ChoosingPrefixState colors costs limit k p answer seen good)
    (hl : limit ≤ n) (hn : n ≤ 200000) : 0 ≤ answer ∧ answer ≤ 19999900000 := by
  rw [hst.1]
  exact choosing_pair_count_prefix_bound colors costs p limit n ⟨hs.1.1, hl⟩ hn

private theorem seen_count_step (colors seen : List Int) (i k c : Int)
    (hlen : Zlength seen = k) (hs : ∀ color, (0 ≤ color ∧ color < k) → Znth color seen 0 = color_count colors i color)
    (hi : 0 ≤ i) (hc : 0 ≤ c ∧ c < k) (he : c = Znth i colors 0) :
    ∀ color, (0 ≤ color ∧ color < k) →
      Znth color (replace_Znth c (Znth c seen 0 + 1) seen) 0 = color_count colors (i + 1) color := by
  intro color hcolor
  rw [color_count_snoc colors i color hi]
  by_cases h : color = c
  · subst color
    rw [Znth_replace_Znth_Same 0 seen c _ (by omega), hs c hc, ← he]
    simp
  · rw [Znth_replace_Znth_Diff 0 seen c color _ (by omega) (by omega) (Ne.symm h), hs color hcolor, ← he]
    simp [Ne.symm h]

theorem ChoosingPrefixState_step_affordable_after_copy (colors costs : List Int) (i k p old_answer answer : Int)
    (seen good seen_next : List Int) (c : Int)
    (hs : ChoosingPrefixDataSafe colors costs i k seen good)
    (hst : ChoosingPrefixState colors costs i k p old_answer seen good)
    (hi : 0 ≤ i ∧ i < Zlength colors) (hc : 0 ≤ c ∧ c < k) (he : c = Znth i colors 0)
    (hcost : Znth i costs 0 ≤ p) (ha : answer = old_answer + Znth c seen 0)
    (hn : seen_next = replace_Znth c (Znth c seen 0 + 1) seen) :
    ChoosingPrefixState colors costs (i + 1) k p answer seen_next seen_next := by
  subst answer seen_next
  have hstep := seen_count_step colors seen i k c hs.2.2.1.1 hst.2.1 hi.1 hc he
  refine ⟨?_, hstep, ?_⟩
  · rw [hst.1, hst.2.1 c hc, choosing_pair_count_snoc_affordable colors costs p i c hi.1 he hcost]
  · intro color hcolor
    rw [good_color_count_affordable_as_color_count colors costs i p color hi.1 hcost]
    exact hstep color hcolor

theorem ChoosingPrefixState_step_expensive (colors costs : List Int) (i k p old_answer answer : Int)
    (seen good seen_next : List Int) (c : Int)
    (hs : ChoosingPrefixDataSafe colors costs i k seen good)
    (hst : ChoosingPrefixState colors costs i k p old_answer seen good)
    (hi : 0 ≤ i ∧ i < Zlength colors) (hc : 0 ≤ c ∧ c < k) (he : c = Znth i colors 0)
    (hcost : p < Znth i costs 0) (ha : answer = old_answer + Znth c good 0)
    (hn : seen_next = replace_Znth c (Znth c seen 0 + 1) seen) :
    ChoosingPrefixState colors costs (i + 1) k p answer seen_next good := by
  subst answer seen_next
  refine ⟨?_, seen_count_step colors seen i k c hs.2.2.1.1 hst.2.1 hi.1 hc he, ?_⟩
  · rw [hst.1, hst.2.2 c hc, choosing_pair_count_snoc_expensive colors costs p i c hi.1 he hcost]
  · intro color hcolor
    rw [hst.2.2 color hcolor, good_color_count_snoc_expensive colors costs i p color hi.1 hcost]

end SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_lib

namespace SimpleC.EE.LLM_bench.Algorithms.choosing_inns
export choosing_inns_lib (ChoosingInputSafe CountArraySafe CountsZeroPrefix CountsZeroFull CopyCountsPrefix
  ChoosingPrefixDataSafe ChoosingPrefixState ChoosingInnsAnswer)
end SimpleC.EE.LLM_bench.Algorithms.choosing_inns

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_lib
open AUXLib

def InnsCopiedPrefix (src old dst : List Int) (written k : Int) : Prop :=
  Forall2 Eq (sublist 0 written dst) (sublist 0 written src) ∧
  Forall2 Eq (sublist written k dst) (sublist written k old)

-- The existing enumerations are Zrange 0 n and Zrange lo (hi + 1),
-- respectively; expose the names used by the current annotations.
abbrev InnsAffordable := affordable_betweenb
abbrev InnsPairAllowed := choosing_pairb
abbrev InnsPairs := choosing_pairs_up_to
abbrev InnsPairCount := choosing_pair_count
abbrev InnsColorCount := color_count
abbrev InnsGoodColorCount := good_color_count
abbrev InnsPrefixCounts := ChoosingPrefixState
def InnsPairAnswer (colors costs : List Int) (n p answer : Int) : Prop :=
  answer = InnsPairCount colors costs p n

end SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_lib
namespace SimpleC.EE.LLM_bench.Algorithms.choosing_inns
export choosing_inns_lib (InnsCopiedPrefix InnsAffordable InnsPairAllowed InnsPairs
  InnsPairCount InnsColorCount InnsGoodColorCount InnsPrefixCounts InnsPairAnswer)
end SimpleC.EE.LLM_bench.Algorithms.choosing_inns
