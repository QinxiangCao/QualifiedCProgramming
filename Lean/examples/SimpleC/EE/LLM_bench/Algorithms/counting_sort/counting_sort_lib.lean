import AUXLib.Sorting
import SimpleC.SL.SeparationLogic
import ListLib.General.Length
import Init.Data.List.Nat.Range

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.counting_sort.counting_sort_lib
open AUXLib
export AUXLib.Sorting (increasing increasing_aux)
abbrev Some {A : Type u} (x : A) : Option A := some x
abbrev None {A : Type u} : Option A := none
-- Type spelling emitted for the inferred Znth default in mixed-array VCs.
abbrev _App_option_Z := Option Int

def CountingZeroedPrefix (mixed_counts : List (Option Int)) (upto : Int) : Prop :=
  ∀ value, (0 ≤ value ∧ value < upto) → Znth value mixed_counts none = some 0

def CountingFrequency (values : List Int) (value : Int) : Int :=
  (values.count value : Int)

def CountingHistogramPrefix (input counts : List Int) (processed : Int) : Prop :=
  ∀ value, (0 ≤ value ∧ value < 100) →
    Znth value counts 0 = CountingFrequency (sublist 0 processed input) value

def CountingCumulativeEnd (input : List Int) (value : Int) : Int :=
  List.foldr (· + ·) 0 ((List.range (value + 1).toNat).map
    (fun index : Nat => CountingFrequency input ((index : Int))))

def CountingCumulativeState (input positions : List Int) (next_value : Int) : Prop :=
  ∀ value, (0 ≤ value ∧ value < 100) → Znth value positions 0 =
    if value < next_value then CountingCumulativeEnd input value else CountingFrequency input value

def CountingSorted (input sorted : List Int) : Prop :=
  Permutation input sorted ∧ increasing sorted

def CountingBucketStart (input : List Int) (value : Int) : Int :=
  if value ≤ 0 then 0 else CountingCumulativeEnd input (value - 1)

def CountingPlacementProgress (input positions bucket_ends : List Int)
    (mixed_output : List (Option Int)) (sorted : List Int) (next_index : Int) : Prop :=
  CountingSorted input sorted ∧
  (∀ value, (0 ≤ value ∧ value < 100) →
    Znth value bucket_ends 0 = CountingCumulativeEnd input value) ∧
  (∀ value, (0 ≤ value ∧ value < 100) →
    Znth value positions 0 = CountingBucketStart input value +
      CountingFrequency (sublist 0 (next_index + 1) input) value) ∧
  (∀ value index, (0 ≤ value ∧ value < 100) →
    (Znth value positions 0 ≤ index ∧ index < Znth value bucket_ends 0) →
    Znth index mixed_output none = some (Znth index sorted 0))

def CountingCopyProgress (before target live : List Int) (copied : Int) : Prop :=
  live = sublist 0 copied target ++ sublist copied (Zlength before) before

private theorem sublist_len {A : Type} (l : List A) (lo hi : Int)
    (h : 0 ≤ lo ∧ lo ≤ hi) (hb : hi ≤ Zlength l) :
    Zlength (sublist lo hi l) = hi - lo := ListLib.Zlength_sublist lo hi l h hb

private theorem nth_mem (l : List Int) (i : Int) (h : 0 ≤ i ∧ i < Zlength l) :
    Znth i l 0 ∈ l := by
  unfold Znth
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp only [Zlength, Int.ofNat_eq_coe] at h; omega)]
  simp only [Option.getD_some]
  exact List.getElem_mem _

private theorem mem_nth (l : List Int) (v : Int) (h : v ∈ l) :
    ∃ i : Int, (0 ≤ i ∧ i < Zlength l) ∧ Znth i l 0 = v := by
  obtain ⟨i, hi, hv⟩ := List.mem_iff_getElem.mp h
  refine ⟨i, ⟨by omega, by simp only [Zlength, Int.ofNat_eq_coe]; omega⟩, ?_⟩
  simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using hv

private theorem nth_map_some (l : List Int) (i : Int) (h : 0 ≤ i ∧ i < Zlength l) :
    Znth i (l.map some) none = some (Znth i l 0) := by
  have hi : i.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at h; omega
  simp only [Znth, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

private theorem list_ext {A : Type} (l r : List A) (d : A) (hl : Zlength l = Zlength r)
    (hn : ∀ i, (0 ≤ i ∧ i < Zlength l) → Znth i l d = Znth i r d) : l = r := by
  exact (ListLib.list_eq_ext l r d).mpr ⟨hl, hn⟩

theorem counting_zeroed_prefix_replace__initial_zeroing (mixed_counts : List (Option Int)) (upto : Int)
    (hl : Zlength mixed_counts = 100) (hu : 0 ≤ upto ∧ upto < 100)
    (hz : CountingZeroedPrefix mixed_counts upto) :
    CountingZeroedPrefix (replace_Znth upto (some 0) mixed_counts) (upto + 1) := by
  intro v hv
  by_cases he : v = upto
  · subst v; exact Znth_replace_Znth_Same none mixed_counts upto (some 0) (by omega)
  · rw [Znth_replace_Znth_Diff none mixed_counts upto v (some 0) (by omega) (by omega) (Ne.symm he)]
    exact hz v (by omega)

theorem counting_histogram_empty__initial_zeroing (input zeros : List Int)
    (hz : ∀ value, (0 ≤ value ∧ value < 100) → Znth value zeros 0 = 0) :
    CountingHistogramPrefix input zeros 0 := by
  intro v hv
  simpa [CountingFrequency, sublist] using hz v hv

theorem counting_all_zero_materialization__initial_zeroing (mixed_counts : List (Option Int))
    (hl : Zlength mixed_counts = 100)
    (hz : ∀ value, (0 ≤ value ∧ value < 100) → Znth value mixed_counts none = some 0) :
    mixed_counts = (List.replicate (100 : Int).toNat (0 : Int)).map some := by
  apply list_ext _ _ none (by simpa only [Zlength, List.length_map, List.length_replicate] using hl)
  intro i hi
  rw [hz i (by omega)]
  have hir : i.toNat < 100 := by omega
  simp only [Znth, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_replicate, show (100 : Int).toNat = 100 from rfl, if_pos hir, Option.map_some, Option.getD_some]

theorem counting_frequency_prefix_snoc__histogram_cumulative (input : List Int) (i value : Int)
    (hi : 0 ≤ i ∧ i < Zlength input) :
    CountingFrequency (sublist 0 (i + 1) input) value =
      CountingFrequency (sublist 0 i input) value + if Znth i input 0 = value then 1 else 0 := by
  rw [sublist_split 0 (i + 1) i input (by omega) (by omega), sublist_single 0 i input hi]
  by_cases he : Znth i input 0 = value <;>
    simp [CountingFrequency, List.count_cons, he, Int.natCast_add]

theorem counting_cumulative_end_step__histogram_cumulative (input : List Int) (value : Int)
    (hv : 0 ≤ value) : CountingCumulativeEnd input value =
    CountingCumulativeEnd input (value - 1) + CountingFrequency input value := by
  unfold CountingCumulativeEnd
  simp only [show value - 1 + 1 = value by omega]
  rw [show (value + 1).toNat = value.toNat + 1 by omega, List.range_succ, List.map_append, List.foldr_append]
  have hn : (value.toNat : Int) = value := by omega
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, hn, Int.add_zero]
  have hf : ∀ (l : List Int) (b : Int), List.foldr (· + ·) b l = List.foldr (· + ·) 0 l + b := by
    intro l b; induction l with
    | nil => simp
    | cons x l ih => simp only [List.foldr_cons, ih]; omega
  rw [hf]

theorem counting_frequency_cons__histogram_cumulative (input : List Int) (x value : Int) :
    CountingFrequency (x :: input) value = CountingFrequency input value + if x = value then 1 else 0 := by
  by_cases he : x = value <;> simp [CountingFrequency, List.count_cons, he, Int.natCast_add]

theorem counting_frequency_sum_cons_notin__histogram_cumulative (buckets input : List Int) (x : Int)
    (hx : x ∉ buckets) :
    sum (buckets.map (fun value => CountingFrequency (x :: input) value)) =
    sum (buckets.map (fun value => CountingFrequency input value)) := by
  induction buckets with
  | nil => rfl
  | cons b bs ih =>
    have h : x ≠ b ∧ x ∉ bs := by simpa using hx
    simp only [List.map_cons, sum, List.foldr_cons]
    rw [counting_frequency_cons__histogram_cumulative, if_neg h.1, Int.add_zero]
    exact congrArg (CountingFrequency input b + ·) (ih h.2)

theorem counting_frequency_sum_cons_bound__histogram_cumulative (buckets input : List Int) (x : Int)
    (hnd : NoDup buckets) :
    sum (buckets.map (fun value => CountingFrequency (x :: input) value)) ≤
    sum (buckets.map (fun value => CountingFrequency input value)) + 1 := by
  induction buckets with
  | nil => simp [sum]
  | cons b bs ih =>
    have hp : b ∉ bs ∧ bs.Nodup := List.nodup_cons.mp hnd
    have hi := ih hp.2
    simp only [List.map_cons, sum, List.foldr_cons] at hi ⊢
    rw [counting_frequency_cons__histogram_cumulative]
    by_cases he : x = b
    · subst x
      rw [if_pos rfl]
      have ht := counting_frequency_sum_cons_notin__histogram_cumulative bs input b hp.1
      unfold sum at ht
      omega
    · rw [if_neg he]; omega

theorem counting_frequency_range_sum_bound__histogram_cumulative (buckets input : List Int)
    (hnd : NoDup buckets) :
    sum (buckets.map (fun value => CountingFrequency input value)) ≤ Zlength input := by
  induction input with
  | nil =>
    clear hnd
    have : sum (buckets.map (fun value => CountingFrequency [] value)) = 0 := by
      induction buckets with
      | nil => rfl
      | cons b bs ih => simpa [sum, CountingFrequency] using ih
    rw [this]; exact Int.le_refl _
  | cons x xs ih =>
    have hs := counting_frequency_sum_cons_bound__histogram_cumulative buckets xs x hnd
    rw [Zlength_cons]; omega

theorem counting_nat_to_Z_map_nodup__histogram_cumulative (indices : List Nat)
    (hnd : NoDup indices) : NoDup (indices.map (fun n : Nat => (n : Int))) := by
  induction indices with
  | nil => exact List.nodup_nil
  | cons n ns ih =>
    have hp := List.nodup_cons.mp hnd
    apply List.nodup_cons.mpr
    refine ⟨?_, ih hp.2⟩
    intro h
    obtain ⟨m, hm, he⟩ := List.mem_map.mp h
    change (m : Int) = (n : Int) at he
    have : m = n := by omega
    exact hp.1 (this ▸ hm)

theorem counting_cumulative_end_bound__histogram_cumulative (input : List Int) (value : Int) :
    CountingCumulativeEnd input value ≤ Zlength input := by
  have h := counting_frequency_range_sum_bound__histogram_cumulative
    ((List.range (value+1).toNat).map (fun n : Nat => (n : Int))) input
    (counting_nat_to_Z_map_nodup__histogram_cumulative _ List.nodup_range)
  simpa [sum, List.map_map, CountingCumulativeEnd] using h

theorem counting_frequency_nonnegative__placement_boundaries (values : List Int) (value : Int) :
    0 ≤ CountingFrequency values value := by unfold CountingFrequency; omega

theorem counting_frequency_positive_In__placement_boundaries (values : List Int) (value : Int)
    (hi : In value values) : 1 ≤ CountingFrequency values value := by
  have := List.count_pos_iff.mpr hi
  unfold CountingFrequency; omega

theorem counting_cumulative_nonnegative__placement_boundaries (values : List Int) (value : Int) :
    0 ≤ CountingCumulativeEnd values value := by
  unfold CountingCumulativeEnd
  induction List.range (value + 1).toNat with
  | nil => exact Int.le_refl _
  | cons n ns ih =>
    have := counting_frequency_nonnegative__placement_boundaries values n
    simp only [List.map_cons, List.foldr_cons]; omega

theorem fold_right_Zadd_acc__placement_boundaries (values : List Int) (base : Int) :
    List.foldr (· + ·) base values = List.foldr (· + ·) 0 values + base := by
  induction values with
  | nil => simp
  | cons x xs ih => simp only [List.foldr_cons, ih]; omega

theorem counting_cumulative_bucket_identity__placement_boundaries (input : List Int) (value : Int)
    (hv : 0 ≤ value) : CountingCumulativeEnd input value =
    CountingBucketStart input value + CountingFrequency input value := by
  unfold CountingBucketStart
  split
  · have he : value = 0 := by omega
    subst value; simp [CountingCumulativeEnd]
  · exact counting_cumulative_end_step__histogram_cumulative input value hv

theorem counting_bucket_start_nonnegative__placement_boundaries (input : List Int) (value : Int) :
    0 ≤ CountingBucketStart input value := by
  unfold CountingBucketStart
  split
  · exact Int.le_refl _
  · exact counting_cumulative_nonnegative__placement_boundaries input (value - 1)

theorem counting_index_bounds_to_In_bounds__placement_boundaries (input : List Int)
    (hb : ∀ index, (0 ≤ index ∧ index < Zlength input) → (0 ≤ Znth index input 0 ∧ Znth index input 0 < 100))
    (value : Int) (hi : In value input) : 0 ≤ value ∧ value < 100 := by
  obtain ⟨i, hi, he⟩ := mem_nth input value hi
  simpa [he] using hb i hi

private theorem inc_aux_all (xs : List Int) (x : Int) (h : increasing_aux xs x) :
    ∀ y ∈ xs, x ≤ y := by
  induction xs generalizing x with
  | nil => simp
  | cons a xs ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h.1
    · exact Int.le_trans h.1 (ih a h.2 y hy)

private theorem inc_tail (x : Int) (xs : List Int) (h : increasing (x :: xs)) : increasing xs := by
  cases xs with
  | nil => trivial
  | cons y ys => exact h.2

private theorem inc_bridge (xs : List Int) (h : AUXLib.increasing xs) : increasing xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    cases xs with
    | nil => trivial
    | cons y ys => exact ⟨h.1, ih h.2⟩

theorem counting_canonical_sorted_exists__placement_boundaries (input : List Int)
    (hb : ∀ value, In value input → (0 ≤ value ∧ value < 100)) :
    ∃ sorted, Zlength sorted = Zlength input ∧
      (∀ index, (0 ≤ index ∧ index < Zlength input) → (0 ≤ Znth index sorted 0 ∧ Znth index sorted 0 < 100)) ∧
      CountingSorted input sorted := by
  have hp := AUXLib.sort_list_perm input
  have hl : Zlength (AUXLib.sort input) = Zlength input := by
    unfold Zlength; rw [hp.length_eq]
  refine ⟨AUXLib.sort input, hl, ?_, hp, inc_bridge _ (AUXLib.sort_list_increasing input)⟩
  intro i hi
  exact hb _ (hp.mem_iff.mpr (nth_mem _ i (by omega)))

theorem counting_frequency_cons_fold__placement_boundaries (indices : List Nat) (input : List Int) (head : Int) :
    List.foldr (· + ·) 0 (indices.map (fun index : Nat => CountingFrequency (head :: input) (index : Int))) =
    List.foldr (· + ·) 0 (indices.map (fun index : Nat => CountingFrequency input (index : Int))) +
      ((indices.map (fun n : Nat => (n : Int))).count head : Int) := by
  induction indices with
  | nil => simp
  | cons n ns ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [counting_frequency_cons__histogram_cumulative, ih]
    by_cases he : head = (n : Int)
    · subst head; simp only [List.count_cons_self, Int.natCast_add, Int.natCast_one]
      simp only [ite_true]
      omega
    · rw [if_neg he, List.count_cons_of_ne (Ne.symm he)]; omega

private theorem count_cast (indices : List Nat) (x : Int) (hx : 0 ≤ x) :
    (indices.map (fun n : Nat => (n : Int))).count x = indices.count x.toNat := by
  induction indices with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.map_cons]
    by_cases hn : n = x.toNat
    · have he : (n : Int) = x := by omega
      rw [he, List.count_cons_self, hn, List.count_cons_self, ih]
    · have he : (n : Int) ≠ x := by omega
      rw [List.count_cons_of_ne he, List.count_cons_of_ne hn, ih]

theorem counting_cumulative_cons_bounded__placement_boundaries (input : List Int) (head value : Int)
    (hh : 0 ≤ head ∧ head ≤ value) : CountingCumulativeEnd (head :: input) value =
      CountingCumulativeEnd input value + 1 := by
  unfold CountingCumulativeEnd
  rw [counting_frequency_cons_fold__placement_boundaries, count_cast _ head hh.1, List.count_range,
    if_pos (show head.toNat < (value + 1).toNat by omega)]
  rfl

theorem counting_cumulative_99_length__placement_boundaries (input : List Int)
    (hb : ∀ value, In value input → (0 ≤ value ∧ value < 100)) :
    CountingCumulativeEnd input 99 = Zlength input := by
  induction input with
  | nil =>
    have h : ∀ ns : List Nat, List.foldr (· + ·) 0 (ns.map (fun n : Nat => CountingFrequency [] (n : Int))) = 0 := by
      intro ns; induction ns with
      | nil => rfl
      | cons n ns ih => simpa [CountingFrequency] using ih
    exact h _
  | cons x xs ih =>
    have hx := hb x (by simp)
    rw [counting_cumulative_cons_bounded__placement_boundaries xs x 99 (by omega),
      ih (by intro v hv; exact hb v (by simp [hv])), Zlength_cons]

theorem counting_cumulative_positive_at_In__placement_boundaries (input : List Int) (value : Int)
    (hv : 0 ≤ value) (hi : In value input) : 1 ≤ CountingCumulativeEnd input value := by
  rw [counting_cumulative_bucket_identity__placement_boundaries input value hv]
  have := counting_bucket_start_nonnegative__placement_boundaries input value
  have := counting_frequency_positive_In__placement_boundaries input value hi
  omega

theorem counting_placement_initial__placement_boundaries (input positions : List Int)
    (output : List (Option Int)) (sorted : List Int) (hs : CountingSorted input sorted)
    (hc : CountingCumulativeState input positions 100) :
    CountingPlacementProgress input positions positions output sorted (Zlength input - 1) := by
  refine ⟨hs, ?_, ?_, ?_⟩
  · intro v hv
    rw [hc v hv, if_pos hv.2]
  · intro v hv
    rw [hc v hv, if_pos hv.2, show Zlength input - 1 + 1 = Zlength input by omega,
      sublist_self input (Zlength input) rfl]
    exact counting_cumulative_bucket_identity__placement_boundaries input v hv.1
  · intro v i hv hi; omega

theorem counting_bucket_start_nat__placement_boundaries (input : List Int) (n : Nat) :
    CountingBucketStart input (n : Int) = CountingCumulativeEnd input ((n : Int) - 1) := by
  cases n with
  | zero => rfl
  | succ n => rw [CountingBucketStart, if_neg (by omega)]

theorem counting_bucket_cover_upto__placement_boundaries (input : List Int) (limit : Nat) (index : Int)
    (hi : 0 ≤ index ∧ index < CountingCumulativeEnd input ((limit : Int) - 1)) :
    ∃ value, (0 ≤ value ∧ value < (limit : Int)) ∧
      (CountingBucketStart input value ≤ index ∧ index < CountingCumulativeEnd input value) := by
  induction limit with
  | zero => change 0 ≤ index ∧ index < 0 at hi; omega
  | succ n ih =>
    by_cases hh : index < CountingCumulativeEnd input ((n : Int) - 1)
    · obtain ⟨v, hv, hb⟩ := ih ⟨hi.1, hh⟩
      exact ⟨v, ⟨hv.1, by omega⟩, hb⟩
    · refine ⟨n, ⟨by omega, by omega⟩, ?_, ?_⟩
      · rw [counting_bucket_start_nat__placement_boundaries]; omega
      · have he : (↑(n + 1) : Int) - 1 = n := by omega
        simpa only [he] using hi.2

theorem counting_placement_complete__placement_boundaries (input positions bucket_ends : List Int)
    (output : List (Option Int)) (sorted : List Int)
    (hb : ∀ value, In value input → (0 ≤ value ∧ value < 100))
    (hp : CountingPlacementProgress input positions bucket_ends output sorted (-1))
    (index : Int) (hi : 0 ≤ index ∧ index < Zlength input) :
    Znth index output none = some (Znth index sorted 0) := by
  obtain ⟨v, hv, hbucket⟩ := counting_bucket_cover_upto__placement_boundaries input 100 index
    (by simpa only [show ((100 : Nat) : Int) - 1 = 99 from rfl,
      counting_cumulative_99_length__placement_boundaries input hb] using hi)
  have hpos := hp.2.2.1 v hv
  have hend := hp.2.1 v hv
  simp only [show (-1 : Int) + 1 = 0 from rfl, sublist, Int.toNat_zero, List.take_zero,
    List.drop_zero, CountingFrequency, List.count_nil, Int.natCast_zero, Int.add_zero] at hpos
  exact hp.2.2.2 v index hv ⟨by omega, by omega⟩

theorem counting_output_prefix__placement_boundaries (output : List (Option Int)) (sorted : List Int) (n : Int)
    (hn : 0 ≤ n ∧ n ≤ Zlength output) (hs : Zlength sorted = n)
    (hp : ∀ index, (0 ≤ index ∧ index < n) → Znth index output none = some (Znth index sorted 0)) :
    sublist 0 n output = sorted.map some := by
  have hl : Zlength (sublist 0 n output) = n := by rw [sublist_len _ 0 n (by omega) hn.2]; omega
  apply list_ext _ _ none (by simpa only [Zlength, List.length_map] using hl.trans hs.symm)
  intro i hi
  rw [Znth_sublist none 0 i n output (by omega) (by omega), Int.add_zero,
    nth_map_some sorted i (by omega)]
  exact hp i (by omega)

theorem counting_frequency_cons__placement_transition (x : Int) (xs : List Int) (value : Int) :
    CountingFrequency (x :: xs) value = CountingFrequency xs value + if x = value then 1 else 0 :=
  counting_frequency_cons__histogram_cumulative xs x value

theorem counting_frequency_sum_cons__placement_transition (indices : List Nat) (x : Int) (xs : List Int)
    (hx : 0 ≤ x) :
    List.foldr (· + ·) 0 (indices.map (fun index : Nat => CountingFrequency (x :: xs) (index : Int))) =
    List.foldr (· + ·) 0 (indices.map (fun index : Nat => CountingFrequency xs (index : Int))) +
      (indices.count x.toNat : Int) := by
  rw [counting_frequency_cons_fold__placement_boundaries, count_cast _ x hx]

theorem counting_cumulative_end_nil__placement_transition (value : Int) :
    CountingCumulativeEnd [] value = 0 := by
  unfold CountingCumulativeEnd
  induction List.range (value+1).toNat with
  | nil => rfl
  | cons n ns ih => simpa [CountingFrequency] using ih

theorem counting_cumulative_end_cons__placement_transition (x : Int) (xs : List Int) (value : Int)
    (hx : 0 ≤ x) (hv : 0 ≤ value) : CountingCumulativeEnd (x :: xs) value =
    CountingCumulativeEnd xs value + if x ≤ value then 1 else 0 := by
  unfold CountingCumulativeEnd
  rw [counting_frequency_sum_cons__placement_transition _ x xs hx, List.count_range]
  by_cases he : x ≤ value
  · rw [if_pos he, if_pos (show x.toNat < (value+1).toNat by omega)]
    rfl
  · rw [if_neg he, if_neg (show ¬ x.toNat < (value+1).toNat by omega)]
    rfl

theorem counting_cumulative_end_as_filter__placement_transition (values : List Int) (value : Int)
    (hn : Forall (fun x => 0 ≤ x) values) (hv : 0 ≤ value) :
    CountingCumulativeEnd values value = Zlength (values.filter (fun x => decide (x ≤ value))) := by
  induction hn with
  | nil => exact counting_cumulative_end_nil__placement_transition value
  | @cons x xs hx hxs ih =>
    rw [counting_cumulative_end_cons__placement_transition x xs value hx hv]
    by_cases he : x ≤ value
    · simp [he, Zlength_cons, ih]
    · simp [he, Zlength_cons, ih]

theorem counting_forall_nonnegative_from_Znth__placement_transition (values : List Int)
    (hp : ∀ index, (0 ≤ index ∧ index < Zlength values) → 0 ≤ Znth index values 0) :
    Forall (fun x => 0 ≤ x) values := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  obtain ⟨i, hi, he⟩ := mem_nth values x hx
  simpa [he] using hp i hi

theorem counting_increasing_filter_lower__placement_transition (values : List Int) (value index : Int)
    (hs : increasing values) (hi : 0 ≤ index ∧ index < Zlength values) (hv : Znth index values 0 ≤ value) :
    index < Zlength (values.filter (fun x => decide (x ≤ value))) := by
  induction values generalizing index with
  | nil => simp only [Zlength_nil] at hi; omega
  | cons x xs ih =>
    simp only [Zlength_cons] at hi
    by_cases he : index = 0
    · subst index
      have hx : x ≤ value := hv
      simp only [List.filter_cons, show decide (x ≤ value) = true from decide_eq_true hx, ite_true, Zlength_cons]
      have := Zlength_nonneg (xs.filter (fun x => decide (x ≤ value)))
      omega
    · have hp : 0 < index := by omega
      rw [Znth_cons 0 index x xs hp] at hv
      have hr : 0 ≤ index - 1 ∧ index - 1 < Zlength xs := by omega
      have hx := inc_aux_all xs x hs _ (nth_mem xs (index - 1) hr)
      have ih := ih (index - 1) (inc_tail x xs hs) hr hv
      have hxv : x ≤ value := by omega
      simp only [List.filter_cons, show decide (x ≤ value) = true from decide_eq_true hxv, ite_true, Zlength_cons]
      omega

theorem counting_filter_below_lower_empty__placement_transition (values : List Int) (lower value : Int)
    (hl : Forall (fun x => lower ≤ x) values) (hv : value < lower) :
    values.filter (fun x => decide (x ≤ value)) = [] := by
  induction hl with
  | nil => rfl
  | @cons x xs hx hxs ih =>
    have hn : ¬ x ≤ value := by omega
    simp [hn, ih]

theorem counting_increasing_filter_upper__placement_transition (values : List Int) (value index : Int)
    (hs : increasing values) (hi : 0 ≤ index ∧ index < Zlength values) (hv : value < Znth index values 0) :
    Zlength (values.filter (fun x => decide (x ≤ value))) ≤ index := by
  induction values generalizing index with
  | nil => simp only [Zlength_nil] at hi; omega
  | cons x xs ih =>
    simp only [Zlength_cons] at hi
    by_cases he : index = 0
    · subst index
      have hx : value < x := hv
      have hall : Forall (fun y => x ≤ y) (x :: xs) :=
        .cons (Int.le_refl x) (Forall.iff_forall_mem.mpr (inc_aux_all xs x hs))
      rw [counting_filter_below_lower_empty__placement_transition _ x value hall hx]
      exact Int.le_refl _
    · have hp : 0 < index := by omega
      rw [Znth_cons 0 index x xs hp] at hv
      have ih := ih (index - 1) (inc_tail x xs hs) (by omega) hv
      by_cases hx : x ≤ value
      · simp only [List.filter_cons, show decide (x ≤ value) = true from decide_eq_true hx, ite_true, Zlength_cons]
        omega
      · simp only [List.filter_cons, show decide (x ≤ value) = false from decide_eq_false hx, Bool.false_eq_true, ite_false]
        omega

theorem counting_cumulative_end_perm__placement_transition (values1 values2 : List Int) (value : Int)
    (hp : Permutation values1 values2) : CountingCumulativeEnd values1 value = CountingCumulativeEnd values2 value := by
  have hf : ∀ v, CountingFrequency values1 v = CountingFrequency values2 v := by
    intro v; unfold CountingFrequency; rw [hp.count_eq v]
  unfold CountingCumulativeEnd
  simp only [hf]

theorem counting_sorted_bucket_value__placement_transition (input sorted : List Int) (value index : Int)
    (hs : CountingSorted input sorted) (hn : Forall (fun x => 0 ≤ x) sorted) (hv : 0 ≤ value)
    (hi : 0 ≤ index ∧ index < Zlength sorted)
    (hb : CountingBucketStart input value ≤ index ∧ index < CountingCumulativeEnd input value) :
    Znth index sorted 0 = value := by
  have hend : CountingCumulativeEnd input value = Zlength (sorted.filter (fun x => decide (x ≤ value))) := by
    rw [counting_cumulative_end_perm__placement_transition input sorted value hs.1]
    exact counting_cumulative_end_as_filter__placement_transition sorted value hn hv
  have hnth : 0 ≤ Znth index sorted 0 := hn.mem (nth_mem sorted index hi)
  have hupper : ¬value < Znth index sorted 0 := by
    intro hg
    have hu := counting_increasing_filter_upper__placement_transition sorted value index hs.2 hi hg
    omega
  by_cases hz : value ≤ 0
  · omega
  · have hstart : CountingCumulativeEnd input (value-1) ≤ index := by
      simpa only [CountingBucketStart, if_neg hz] using hb.1
    have hprev : CountingCumulativeEnd input (value-1) = Zlength (sorted.filter (fun x => decide (x ≤ value-1))) := by
      rw [counting_cumulative_end_perm__placement_transition input sorted (value-1) hs.1]
      exact counting_cumulative_end_as_filter__placement_transition sorted (value-1) hn (by omega)
    have hlower : ¬ Znth index sorted 0 < value := by
      intro hl
      have hlo := counting_increasing_filter_lower__placement_transition sorted (value-1) index hs.2 hi (by omega)
      omega
    omega

theorem counting_frequency_prefix_drop_last__placement_transition (input : List Int) (processed value : Int)
    (hp : 0 ≤ processed ∧ processed < Zlength input) :
    CountingFrequency (sublist 0 (processed + 1) input) value =
      CountingFrequency (sublist 0 processed input) value + if Znth processed input 0 = value then 1 else 0 :=
  counting_frequency_prefix_snoc__histogram_cumulative input processed value hp

theorem counting_cumulative_end_step__placement_transition (input : List Int) (value : Int) (hv : 0 ≤ value) :
    CountingCumulativeEnd input value = CountingBucketStart input value + CountingFrequency input value :=
  counting_cumulative_bucket_identity__placement_boundaries input value hv

theorem counting_cumulative_end_nonnegative__placement_transition (input : List Int) (value : Int) :
    0 ≤ CountingCumulativeEnd input value := counting_cumulative_nonnegative__placement_boundaries input value

theorem counting_bucket_start_nonnegative__placement_transition (input : List Int) (value : Int) :
    0 ≤ CountingBucketStart input value := counting_bucket_start_nonnegative__placement_boundaries input value

theorem counting_frequency_prefix_le__placement_transition (input : List Int) (processed value : Int)
    (hp : 0 ≤ processed ∧ processed ≤ Zlength input) :
    CountingFrequency (sublist 0 processed input) value ≤ CountingFrequency input value := by
  have hs : input = sublist 0 processed input ++ sublist processed (Zlength input) input := by
    rw [← sublist_split 0 (Zlength input) processed input (by omega) (by omega), sublist_self input (Zlength input) rfl]
  have hf := congrArg (fun xs => CountingFrequency xs value) hs
  simp only [CountingFrequency, List.count_append, Int.natCast_add] at hf ⊢
  omega

theorem counting_cumulative_end_bound__placement_transition (input sorted : List Int) (value : Int)
    (hs : CountingSorted input sorted) (hn : Forall (fun x => 0 ≤ x) sorted) (hv : 0 ≤ value) :
    CountingCumulativeEnd input value ≤ Zlength sorted := by
  have hl : Zlength input = Zlength sorted := congrArg Int.ofNat hs.1.length_eq
  rw [← hl]
  exact counting_cumulative_end_bound__histogram_cumulative input value

theorem counting_copy_initial__copyback (before target : List Int) :
    CountingCopyProgress before target before 0 := by
  unfold CountingCopyProgress
  rw [sublist_self before (Zlength before) rfl]
  rfl

theorem counting_copy_step__copyback (before target live : List Int) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength before) (ht : Zlength target = Zlength before)
    (hc : CountingCopyProgress before target live i) :
    CountingCopyProgress before target (replace_Znth i (Znth i target 0) live) (i+1) := by
  have hlen : Zlength (sublist 0 i target) = i := by rw [sublist_len _ 0 i (by omega) (by omega)]; omega
  have hs : sublist i (Zlength before) before =
      [Znth i before 0] ++ sublist (i+1) (Zlength before) before := by
    rw [sublist_split i (Zlength before) (i+1) before (by omega) (by omega), sublist_single 0 i before hi]
  have hn := AUXLib.Sorting.replace_Znth_boundary_local
    (sublist 0 i target) (sublist (i+1) (Zlength before) before) (Znth i target 0) (Znth i before 0)
  unfold CountingCopyProgress at hc ⊢
  rw [hc, hs, show [Znth i before 0] ++ sublist (i+1) (Zlength before) before =
    Znth i before 0 :: sublist (i+1) (Zlength before) before from rfl]
  rw [hlen] at hn
  rw [hn, sublist_split 0 (i+1) i target (by omega) (by omega), sublist_single 0 i target (by omega)]
  simp only [List.append_assoc, List.singleton_append]

theorem counting_copy_complete__copyback (before target live : List Int)
    (ht : Zlength target = Zlength before) (hc : CountingCopyProgress before target live (Zlength before)) :
    live = target := by
  unfold CountingCopyProgress at hc
  rw [sublist_self target (Zlength before) ht.symm] at hc
  have hnil : sublist (Zlength before) (Zlength before) before = [] := by
    unfold sublist
    exact List.drop_eq_nil_of_le (by simp only [List.length_take]; omega)
  simpa only [hnil, List.append_nil] using hc

theorem counting_placement_step__placement_transition (n : Int) (input : List Int) (i : Int)
    (output : List (Option Int)) (bucket_ends sorted positions : List Int) (output_default : Option Int)
    (hn : 0 ≤ n ∧ n ≤ 100) (hli : Zlength input = n) (hls : Zlength sorted = n)
    (hlp : Zlength positions = 100) (hlo : Zlength output = 100) (hi : 0 ≤ i ∧ i < n)
    (hbi : ∀ index, (0 ≤ index ∧ index < n) → (0 ≤ Znth index input 0 ∧ Znth index input 0 < 100))
    (hbs : ∀ index, (0 ≤ index ∧ index < n) → (0 ≤ Znth index sorted 0 ∧ Znth index sorted 0 < 100))
    (hbp : ∀ bucket, (0 ≤ bucket ∧ bucket < 100) → (0 ≤ Znth bucket positions 0 ∧ Znth bucket positions 0 ≤ n))
    (hbo : ∀ index, (n ≤ index ∧ index < 100) → Znth index output output_default = none)
    (hpos : 1 ≤ Znth (Znth i input 0) positions 0)
    (hp : CountingPlacementProgress input positions bucket_ends output sorted i) :
    let value := Znth i input 0
    let positions' := replace_Znth value (Znth value positions 0 - 1) positions
    let write_index := Znth value positions' 0
    let output' := replace_Znth write_index (some value) output
    (∀ bucket, (0 ≤ bucket ∧ bucket < 100) → (0 ≤ Znth bucket positions' 0 ∧ Znth bucket positions' 0 ≤ n)) ∧
    (i - 1 ≥ 0 → 1 ≤ Znth (Znth (i - 1) input 0) positions' 0) ∧
    (∀ index, (n ≤ index ∧ index < 100) → Znth index output' output_default = none) ∧
    CountingPlacementProgress input positions' bucket_ends output' sorted (i - 1) := by
  let value := Znth i input 0
  let positions' := replace_Znth value (Znth value positions 0 - 1) positions
  let write_index := Znth value positions' 0
  let output' := replace_Znth write_index (some value) output
  change (∀ bucket, (0 ≤ bucket ∧ bucket < 100) → (0 ≤ Znth bucket positions' 0 ∧ Znth bucket positions' 0 ≤ n)) ∧
    (i - 1 ≥ 0 → 1 ≤ Znth (Znth (i - 1) input 0) positions' 0) ∧
    (∀ index, (n ≤ index ∧ index < 100) → Znth index output' output_default = none) ∧
    CountingPlacementProgress input positions' bucket_ends output' sorted (i - 1)
  have hv : 0 ≤ value ∧ value < 100 := hbi i hi
  have hvp : 0 ≤ value ∧ value < Zlength positions := by omega
  have hvpos := hbp value hv
  have hw : write_index = Znth value positions 0 - 1 :=
    Znth_replace_Znth_Same 0 positions value (Znth value positions 0 - 1) hvp
  have hwo : 0 ≤ write_index ∧ write_index < Zlength output := by
    change 1 ≤ Znth value positions 0 at hpos
    omega
  have hws : 0 ≤ write_index ∧ write_index < Zlength sorted := by omega
  have hnonneg : Forall (fun x => 0 ≤ x) sorted :=
    counting_forall_nonnegative_from_Znth__placement_transition sorted
      (by intro k hk; exact (hbs k (by omega)).1)
  have heq : ∀ bucket, (0 ≤ bucket ∧ bucket < 100) →
      Znth bucket positions' 0 = CountingBucketStart input bucket + CountingFrequency (sublist 0 i input) bucket := by
    intro b hb
    have hpb := hp.2.2.1 b hb
    have hf := counting_frequency_prefix_drop_last__placement_transition input i b (by omega)
    change CountingFrequency (sublist 0 (i+1) input) b =
      CountingFrequency (sublist 0 i input) b + if value = b then 1 else 0 at hf
    by_cases he : value = b
    · subst b
      change Znth value (replace_Znth value _ positions) 0 = _
      rw [Znth_replace_Znth_Same 0 positions value _ hvp]
      rw [if_pos rfl] at hf
      omega
    · change Znth b (replace_Znth value _ positions) 0 = _
      rw [Znth_replace_Znth_Diff 0 positions value b _ hvp (by omega) he]
      rw [if_neg he] at hf
      omega
  have hnewbounds : ∀ bucket, (0 ≤ bucket ∧ bucket < 100) →
      (0 ≤ Znth bucket positions' 0 ∧ Znth bucket positions' 0 ≤ n) := by
    intro b hb
    by_cases he : b = value
    · subst b
      change 0 ≤ write_index ∧ write_index ≤ n
      omega
    · change 0 ≤ Znth b (replace_Znth value _ positions) 0 ∧ Znth b (replace_Znth value _ positions) 0 ≤ n
      rw [Znth_replace_Znth_Diff 0 positions value b _ hvp (by omega) (Ne.symm he)]
      exact hbp b hb
  have hbucket : CountingBucketStart input value ≤ write_index ∧
      write_index < CountingCumulativeEnd input value := by
    have hpp := hp.2.2.1 value hv
    have hpn := heq value hv
    have hf := counting_frequency_prefix_le__placement_transition input (i+1) value (by omega)
    have hstep := counting_cumulative_end_step__placement_transition input value hv.1
    have hnonneg := counting_frequency_nonnegative__placement_boundaries (sublist 0 i input) value
    change write_index = _ at hpn
    omega
  have hwvalue : Znth write_index sorted 0 = value :=
    counting_sorted_bucket_value__placement_transition input sorted value write_index hp.1 hnonneg hv.1 hws hbucket
  have hfilled : ∀ bucket index, (0 ≤ bucket ∧ bucket < 100) →
      (Znth bucket positions' 0 ≤ index ∧ index < Znth bucket bucket_ends 0) →
      Znth index output' none = some (Znth index sorted 0) := by
    intro b k hb hk
    have hbound := counting_cumulative_end_bound__placement_transition input sorted b hp.1 hnonneg hb.1
    have hbend := hp.2.1 b hb
    have hbpos := hnewbounds b hb
    have hko : 0 ≤ k ∧ k < Zlength output := by omega
    by_cases he : k = write_index
    · subst k
      change Znth write_index (replace_Znth write_index (some value) output) none = _
      rw [Znth_replace_Znth_Same none output write_index (some value) hwo, hwvalue]
    · change Znth k (replace_Znth write_index (some value) output) none = _
      rw [Znth_replace_Znth_Diff none output write_index k (some value) hwo hko (Ne.symm he)]
      apply hp.2.2.2 b k hb
      refine ⟨?_, hk.2⟩
      by_cases hbe : b = value
      · subst b
        change write_index ≤ k ∧ k < Znth value bucket_ends 0 at hk
        omega
      · have hsame : Znth b positions' 0 = Znth b positions 0 :=
          Znth_replace_Znth_Diff 0 positions value b _ hvp (by omega) (Ne.symm hbe)
        omega
  refine ⟨hnewbounds, ?_, ?_, ?_⟩
  · intro hnext
    have hnextval := hbi (i-1) (by omega)
    have he := heq (Znth (i-1) input 0) hnextval
    have hf := counting_frequency_prefix_drop_last__placement_transition input (i-1) (Znth (i-1) input 0) (by omega)
    rw [show i - 1 + 1 = i by omega, if_pos rfl] at hf
    have := counting_bucket_start_nonnegative__placement_transition input (Znth (i-1) input 0)
    have := counting_frequency_nonnegative__placement_boundaries (sublist 0 (i-1) input) (Znth (i-1) input 0)
    omega
  · intro k hk
    change Znth k (replace_Znth write_index (some value) output) output_default = none
    rw [Znth_replace_Znth_Diff output_default output write_index k (some value) hwo (by omega) (by omega)]
    exact hbo k hk
  · refine ⟨hp.1, hp.2.1, ?_, hfilled⟩
    intro b hb
    rw [show i - 1 + 1 = i by omega]
    exact heq b hb

end SimpleC.EE.LLM_bench.Algorithms.counting_sort.counting_sort_lib

namespace SimpleC.EE.LLM_bench.Algorithms.counting_sort
export counting_sort_lib (CountingZeroedPrefix CountingFrequency CountingHistogramPrefix CountingCumulativeEnd CountingCumulativeState CountingSorted CountingBucketStart CountingPlacementProgress CountingCopyProgress Some None _App_option_Z increasing)
end SimpleC.EE.LLM_bench.Algorithms.counting_sort
