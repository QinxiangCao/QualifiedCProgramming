import SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_goal
import SimpleC.EE.LLM_bench.Algorithms.decimal_digits.decimal_digits_lib
import SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 5000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open concatenating_numbers_goal concatenating_numbers_lib
open scoped SimpleC.SL.SAC CoqZ
open SimpleC.EE.LLM_bench.Algorithms.decimal_digits
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev array2 := naive_C_Rules.IntArray2
local instance : SacContext := ⟨naive_C_Rules⟩
-- Keep array assertions symbolic during spatial tactic matching.
attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full





private theorem cell_upper (count width row col : Int) (hw : 0≤width) (hr : row<count) (hc : col<width) :
    row*width+col<count*width := by
  have hm := Int.mul_le_mul_of_nonneg_right (show row+1≤count by omega) hw
  have he : (row+1)*width=row*width+width := by grind
  rw [he] at hm
  omega

private theorem indexed_Forall {A : Type} (P : A → Prop) (l : List A) (d : A) :
    Forall P l ↔ ∀ i, 0 ≤ i ∧ i < Zlength l → P (Znth i l d) := by
  rw [Forall.iff_forall_mem]
  constructor
  · intro h i hi
    have hn : i.toNat < l.length := by change 0 ≤ i ∧ i < (l.length : Int) at hi; omega
    have hm := h l[i.toNat] (List.mem_iff_getElem.mpr ⟨i.toNat, hn, rfl⟩)
    simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some] using hm
  · intro h v hv
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hv
    have hi : 0 ≤ (n : Int) ∧ (n : Int) < Zlength l := by change 0 ≤ (n : Int) ∧ (n : Int) < (l.length : Int); omega
    have hh := h n hi
    simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some] using hh


private theorem nth_mem {A : Type} (l : List A) (i : Int) (d : A)
    (hi : 0 ≤ i ∧ i < Zlength l) : Znth i l d ∈ l := by
  have hn : i.toNat < l.length := by change 0 ≤ i ∧ i < (l.length : Int) at hi; omega
  have hm := List.getElem_mem (l := l) hn
  simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some] using hm

private theorem rows_from_annotation (rows : List (List Int)) (lens : List Int) (count width : Int)
    (hr : Zlength rows = count) (hl : Zlength lens = count)
    (hw : Forall (Eq width) (rows.map Zlength))
    (hl0 : Forall (LE.le (1 : Int)) lens) (hlu : Forall (GE.ge width) lens)
    (hh0 : Forall (LE.le (1 : Int)) (rows.map (hd (0 : Int))))
    (hhu : Forall (GE.ge (9 : Int)) (rows.map (hd (0 : Int))))
    (hd0 : Forall (LE.le (0 : Int)) (concatenate_rows rows lens))
    (hdu : Forall (GE.ge (9 : Int)) (concatenate_rows rows lens)) :
    RowsWellFormed rows lens count width := by
  refine ⟨hr, hl, ?_⟩
  intro i hi
  have hrowmem := nth_mem rows i [] (by rw [hr]; exact hi)
  have hwidth : Zlength (Znth i rows []) = width :=
    (hw.mem (List.mem_map.mpr ⟨Znth i rows [], hrowmem, rfl⟩)).symm
  have hlen0 := (indexed_Forall _ lens 0).mp hl0 i (by rw [hl]; exact hi)
  have hlenu := (indexed_Forall _ lens 0).mp hlu i (by rw [hl]; exact hi)
  have hhead : Znth 0 (Znth i rows []) 0 = hd 0 (Znth i rows []) := by
    cases Znth i rows [] <;> rfl
  refine ⟨hwidth, ⟨hlen0, hlenu⟩, ?_, ?_⟩
  · rw [hhead]
    exact ⟨hh0.mem (List.mem_map.mpr ⟨Znth i rows [], hrowmem, rfl⟩),
      hhu.mem (List.mem_map.mpr ⟨Znth i rows [], hrowmem, rfl⟩)⟩
  · intro j hj
    have he : Zlength rows = Zlength lens := by omega
    have hpairlen : Zlength (paired_items rows lens) = count := by
      change ((rows.zip lens).length : Int) = count
      rw [List.length_zip]
      change (rows.length : Int) = count at hr
      change (lens.length : Int) = count at hl
      omega
    have hitem : item_at rows lens i ∈ paired_items rows lens := by
      rw [←Znth_paired_items__pivot_finalization rows lens i he (by rw [hr]; exact hi)]
      exact nth_mem (paired_items rows lens) i ([], 0) (by rw [hpairlen]; exact hi)
    have hsubLen : Zlength (sublist 0 (Znth i lens 0) (Znth i rows [])) = Znth i lens 0 := by
      simpa only [Int.sub_zero] using ListLib.Zlength_sublist 0 (Znth i lens 0) (Znth i rows [])
        ⟨by omega, by omega⟩ (by change Znth i lens 0 ≤ Zlength (Znth i rows []); rw [hwidth]; exact hlenu)
    have hmember := nth_mem (sublist 0 (Znth i lens 0) (Znth i rows [])) j 0 (by rw [hsubLen]; exact hj)
    have hz := Znth_sublist 0 0 j (Znth i lens 0) (Znth i rows []) (by omega) (by simpa only [Int.sub_zero] using hj)
    simp only [Int.add_zero] at hz
    rw [hz] at hmember
    have hall : Znth j (Znth i rows []) 0 ∈ concatenate_rows rows lens := by
      exact List.mem_flatten.mpr ⟨item_digits (item_at rows lens i),
        List.mem_map.mpr ⟨item_at rows lens i, hitem, rfl⟩, hmember⟩
    exact ⟨hd0.mem hall, hdu.mem hall⟩



private theorem annotation_rows_length {rows : List (List Int)} {lens : List Int} {count width : Int}
    (h : RowsWellFormed rows lens count width) : Zlength rows = count := h.1
private theorem annotation_lens_length {rows : List (List Int)} {lens : List Int} {count width : Int}
    (h : RowsWellFormed rows lens count width) : Zlength lens = count := h.2.1
private theorem annotation_rows_map {rows : List (List Int)} {lens : List Int} {count width : Int}
    (h : RowsWellFormed rows lens count width) : Forall (Eq width) (rows.map Zlength) := by
  rw [Forall.iff_forall_mem]
  intro v hv
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hv
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hrow
  have hr := h.1
  have hb : 0 ≤ (i : Int) ∧ (i : Int) < count := by change (rows.length : Int) = count at hr; omega
  have hn : Znth (i : Int) rows [] = row := by
    simp only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact he
  exact (by simpa only [hn] using (h.2.2 i hb).1.symm)

private theorem annotation_digits {rows : List (List Int)} {lens : List Int} {count width : Int}
    (h : RowsWellFormed rows lens count width) :
    Forall (LE.le (0 : Int)) (concatenate_rows rows lens) ∧
    Forall (GE.ge (9 : Int)) (concatenate_rows rows lens) := by
  have he : Zlength rows = Zlength lens := h.1.trans h.2.1.symm
  have hl : Zlength (paired_items rows lens) = count := by
    change ((rows.zip lens).length : Int) = count
    rw [List.length_zip]
    have hr := h.1; have hn := h.2.1
    change (rows.length : Int) = count at hr
    change (lens.length : Int) = count at hn
    omega
  have hall : ∀ digit, digit ∈ concatenate_rows rows lens → 0 ≤ digit ∧ digit ≤ 9 := by
    intro digit hd
    obtain ⟨ds, hds, hd⟩ := List.mem_flatten.mp hd
    obtain ⟨item, hitem, rfl⟩ := List.mem_map.mp hds
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hitem
    have hb : 0 ≤ (i : Int) ∧ (i : Int) < count := by
      change ((paired_items rows lens).length : Int) = count at hl
      omega
    have hn : Znth (i : Int) (paired_items rows lens) ([], 0) = item := by
      simp only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact hget
    rw [Znth_paired_items__pivot_finalization rows lens i he (by rw [h.1]; exact hb)] at hn
    rw [←hn] at hd
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hd
    have hrow := h.2.2 i hb
    have hlen : Zlength (item_digits (item_at rows lens i)) = Znth i lens 0 := by
      change Zlength (sublist 0 (Znth i lens 0) (Znth i rows [])) = Znth i lens 0
      simpa only [Int.sub_zero] using ListLib.Zlength_sublist 0 (Znth i lens 0) (Znth i rows [])
        ⟨by omega, by omega⟩ (by change Znth (i : Int) lens 0 ≤ Zlength (Znth (i : Int) rows []); rw [hrow.1]; exact hrow.2.1.2)
    have hjb : 0 ≤ (j : Int) ∧ (j : Int) < Znth i lens 0 := by
      change ((item_digits (item_at rows lens i)).length : Int) = Znth i lens 0 at hlen
      omega
    have hz : Znth (j : Int) (item_digits (item_at rows lens i)) 0 = digit := by
      simp only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      exact hget
    have hsub := Znth_sublist 0 0 (j : Int) (Znth i lens 0) (Znth i rows []) (by omega) (by simpa only [Int.sub_zero] using hjb)
    simp only [Int.add_zero] at hsub
    change Znth (j : Int) (sublist 0 (Znth i lens 0) (Znth i rows [])) 0 = digit at hz
    rw [hsub] at hz
    simpa only [hz] using hrow.2.2.2 j hjb
  constructor <;> rw [Forall.iff_forall_mem]
  · exact fun d hd => (hall d hd).1
  · exact fun d hd => (hall d hd).2

private theorem annotation_lens_lower {rows : List (List Int)} {lens : List Int} {count width : Int}
    (h : RowsWellFormed rows lens count width) : Forall (LE.le (1 : Int)) lens := by
  apply (indexed_Forall _ lens 0).mpr
  intro i hi
  exact (h.2.2 i (by rw [h.2.1] at hi; exact hi)).2.1.1
private theorem annotation_lens_upper {rows : List (List Int)} {lens : List Int} {count width : Int}
    (h : RowsWellFormed rows lens count width) : Forall (GE.ge width) lens := by
  apply (indexed_Forall _ lens 0).mpr
  intro i hi
  exact (h.2.2 i (by rw [h.2.1] at hi; exact hi)).2.1.2
private theorem annotation_heads {rows : List (List Int)} {lens : List Int} {count width : Int}
    (h : RowsWellFormed rows lens count width) :
    Forall (LE.le (1 : Int)) (rows.map (hd 0)) ∧ Forall (GE.ge (9 : Int)) (rows.map (hd 0)) := by
  have hall : ∀ v, v ∈ rows.map (hd 0) → 1 ≤ v ∧ v ≤ 9 := by
    intro v hv
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hv
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hrow
    have hr := h.1
    have hb : 0 ≤ (i : Int) ∧ (i : Int) < count := by change (rows.length : Int) = count at hr; omega
    have hn : Znth (i : Int) rows [] = row := by
      simp only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact he
    have hh := (h.2.2 i hb).2.2.1
    rw [hn] at hh
    have hz : Znth 0 row 0 = hd 0 row := by cases row <;> rfl
    simpa only [hz] using hh
  constructor <;> rw [Forall.iff_forall_mem]
  · exact fun v hv => (hall v hv).1
  · exact fun v hv => (hall v hv).2
private theorem annotation_head_lower {rows : List (List Int)} {lens : List Int} {count width : Int}
    (h : RowsWellFormed rows lens count width) : Forall (LE.le (1 : Int)) (rows.map (hd 0)) := (annotation_heads h).1
private theorem annotation_head_upper {rows : List (List Int)} {lens : List Int} {count width : Int}
    (h : RowsWellFormed rows lens count width) : Forall (GE.ge (9 : Int)) (rows.map (hd 0)) := (annotation_heads h).2
private theorem annotation_digits_lower {rows : List (List Int)} {lens : List Int} {count width : Int}
    (h : RowsWellFormed rows lens count width) : Forall (LE.le (0 : Int)) (concatenate_rows rows lens) := (annotation_digits h).1
private theorem annotation_digits_upper {rows : List (List Int)} {lens : List Int} {count width : Int}
    (h : RowsWellFormed rows lens count width) : Forall (GE.ge (9 : Int)) (concatenate_rows rows lens) := (annotation_digits h).2

private theorem Forall_of_permutation {A : Type} {P : A → Prop} {xs ys : List A}
    (hp : xs.Perm ys) (h : Forall P xs) : Forall P ys := by
  rw [Forall.iff_forall_mem]
  exact fun x hx => h.mem (hp.mem_iff.mpr hx)

private theorem RowsWellFormed_permutation__annotation (rows0 rows1 : List (List Int))
    (lens0 lens1 : List Int) (count width : Int)
    (h : RowsWellFormed rows0 lens0 count width)
    (hp : PairedPermutation rows0 rows1 lens0 lens1) :
    RowsWellFormed rows1 lens1 count width ∧ sum lens1 = sum lens0 := by
  have he0 : rows0.length = lens0.length := by have := hp.1; change (rows0.length : Int) = (lens0.length : Int) at this; omega
  have he1 : rows1.length = lens1.length := by have := hp.2.1; change (rows1.length : Int) = (lens1.length : Int) at this; omega
  have hr : rows0.Perm rows1 := by
    have hm := hp.2.2.map Prod.fst
    simpa only [paired_items, List.map_fst_zip (show rows0.length ≤ lens0.length by omega),
      List.map_fst_zip (show rows1.length ≤ lens1.length by omega)] using hm
  have hl : lens0.Perm lens1 := by
    have hm := hp.2.2.map Prod.snd
    simpa only [paired_items, List.map_snd_zip (show lens0.length ≤ rows0.length by omega),
      List.map_snd_zip (show lens1.length ≤ rows1.length by omega)] using hm
  have hdperm : (concatenate_rows rows0 lens0).Perm (concatenate_rows rows1 lens1) :=
    (hp.2.2.map item_digits).flatten
  have hrl : Zlength rows1 = count := by
    change (rows1.length : Int) = count
    rw [←hr.length_eq]
    exact h.1
  have hll : Zlength lens1 = count := by
    change (lens1.length : Int) = count
    rw [←hl.length_eq]
    exact h.2.1
  refine ⟨rows_from_annotation rows1 lens1 count width hrl hll ?_ ?_ ?_ ?_ ?_ ?_ ?_,
    (sum_permutation__scan_advance lens0 lens1 hl).symm⟩
  · exact Forall_of_permutation (hr.map Zlength) (annotation_rows_map h)
  · exact Forall_of_permutation hl (annotation_lens_lower h)
  · exact Forall_of_permutation hl (annotation_lens_upper h)
  · exact Forall_of_permutation (hr.map (hd 0)) (annotation_head_lower h)
  · exact Forall_of_permutation (hr.map (hd 0)) (annotation_head_upper h)
  · exact Forall_of_permutation hdperm (annotation_digits_lower h)
  · exact Forall_of_permutation hdperm (annotation_digits_upper h)

private theorem row_span_bounds (row count width : Int)
    (hr : 0 ≤ row) (hc : row < count) (hw : 0 ≤ width) :
    0 ≤ row * width ∧ row * width + width ≤ count * width := by
  refine ⟨Int.mul_nonneg hr hw, ?_⟩
  have hm := Int.mul_le_mul_of_nonneg_right (show row + 1 ≤ count by omega) hw
  have he : (row + 1) * width = row * width + width := by ring
  rw [he] at hm
  exact hm

theorem proof_of_quicksort_numbers_entail_wit_1 : quicksort_numbers_entail_wit_1 := by
  unfold quicksort_numbers_entail_wit_1
  left
  intro flat lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23
  have hspan := row_span_bounds high_pre count_pre number_width_pre (by omega) (by omega) (by omega)
  have PreH14 : (RowsWellFormed rows lens count_pre number_width_pre) := rows_from_annotation rows lens count_pre number_width_pre NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22
  have hw := PreH14.2.2 high_pre ⟨by omega,by omega⟩
  have hlen : Zlength rows=Zlength lens := PreH14.1.trans PreH14.2.1.symm
  have hs := PartitionScanState_identity__partition_and_compare_init rows lens low_pre high_pre hlen
  Exists flat rows lens
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hs
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_entail_wit_2 : quicksort_numbers_entail_wit_2 := by
  unfold quicksort_numbers_entail_wit_2
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre flat1_2 rows1_2 lens1 pivot_length scan boundary NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31
  have hspan := row_span_bounds scan count_pre number_width_pre (by omega) (by omega) (by omega)
  have PreH18 : (RowsWellFormed rows1_2 lens1 count_pre number_width_pre) := rows_from_annotation rows1_2 lens1 count_pre number_width_pre NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28
  have hw := PreH18.2.2 scan ⟨by omega,by omega⟩
  Exists flat1_2 rows1_2 lens1
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact ConcatComparePrefix_zero__partition_and_compare_init rows1_2 lens1 scan high_pre
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_entail_wit_3_1 : quicksort_numbers_entail_wit_3_1 := by
  unfold quicksort_numbers_entail_wit_3_1
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre flat1 rows1_2 position comparison total_length current_length lens1_2 pivot_length boundary scan NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42
  have PreH48 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre) := rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38
  have PreH52 : (FlatRows flat1 rows1_2 count_pre number_width_pre) := NewPreH42
  have hd : Znth (scan*number_width_pre+position) flat1 0=ConcatLeftDigit rows1_2 lens1_2 scan high_pre position := by
    rw [FlatRows_Znth__compare_left_digit flat1 rows1_2 count_pre number_width_pre scan position PreH52 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
    exact (ConcatLeftDigit_first__compare_left_digit rows1_2 lens1_2 count_pre number_width_pre scan high_pre position PreH48 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩).symm
  Exists flat1 rows1_2 lens1_2
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hd
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_entail_wit_3_2 : quicksort_numbers_entail_wit_3_2 := by
  unfold quicksort_numbers_entail_wit_3_2
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre flat1 rows1_2 position comparison total_length current_length lens1_2 pivot_length boundary scan NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42
  have PreH37 : (current_length = (Znth (scan) (lens1_2) ((0 : Int)))) := NewPreH21
  have PreH46 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre) := rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38
  have PreH50 : (FlatRows flat1 rows1_2 count_pre number_width_pre) := NewPreH42
  have hd : Znth (high_pre*number_width_pre+(position-current_length)) flat1 0=ConcatLeftDigit rows1_2 lens1_2 scan high_pre position := by
    rw [FlatRows_Znth__compare_left_digit flat1 rows1_2 count_pre number_width_pre high_pre (position-current_length) PreH50 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩,PreH37]
    exact (ConcatLeftDigit_second__compare_left_digit rows1_2 lens1_2 count_pre number_width_pre scan high_pre position PreH46 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩).symm
  Exists flat1 rows1_2 lens1_2
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hd
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_entail_wit_4_1 : quicksort_numbers_entail_wit_4_1 := by
  unfold quicksort_numbers_entail_wit_4_1
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre rows1_2 lens1_2 flat1 scan boundary pivot_length current_length total_length comparison position left_digit NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42
  have PreH50 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre) := rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38
  have PreH54 : (FlatRows flat1 rows1_2 count_pre number_width_pre) := NewPreH42
  have hd := ConcatRightDigit_first_flat__compare_right_digit flat1 rows1_2 lens1_2 count_pre number_width_pre scan high_pre position PreH54 PreH50 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  Exists flat1 rows1_2 lens1_2
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hd
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_entail_wit_4_2 : quicksort_numbers_entail_wit_4_2 := by
  unfold quicksort_numbers_entail_wit_4_2
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre rows1_2 lens1_2 flat1 scan boundary pivot_length current_length total_length comparison position left_digit NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42
  have PreH37 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int)))) := NewPreH19
  have PreH48 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre) := rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38
  have PreH52 : (FlatRows flat1 rows1_2 count_pre number_width_pre) := NewPreH42
  have hd := ConcatRightDigit_second_flat__compare_right_digit flat1 rows1_2 lens1_2 count_pre number_width_pre scan high_pre position PreH52 PreH48 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega) (by omega)
  rw [←PreH37] at hd
  Exists flat1 rows1_2 lens1_2
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hd
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_entail_wit_5 : quicksort_numbers_entail_wit_5 := by
  unfold quicksort_numbers_entail_wit_5
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre rows1_2 lens1_2 flat1_2 scan boundary pivot_length current_length total_length comparison position left_digit right_digit NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42 NewPreH43
  have PreH1 : (left_digit = right_digit) := NewPreH1
  have PreH25 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position))) := NewPreH29
  have PreH26 : (right_digit = (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position))) := NewPreH30
  have PreH27 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre) := rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39
  have PreH29 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position) := NewPreH41
  have hlen := concat_item_digits_Zlength__compare_outcome rows1_2 lens1_2 count_pre number_width_pre scan high_pre PreH27 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hc := ConcatComparePrefix_step__compare_outcome rows1_2 lens1_2 scan high_pre position PreH29 (by rw [←PreH25,←PreH26]; exact PreH1) (by rw [hlen]; omega)
  Exists flat1_2 rows1_2 lens1_2
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hc
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_entail_wit_6_1 : quicksort_numbers_entail_wit_6_1 := by
  unfold quicksort_numbers_entail_wit_6_1
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre flat1_2 rows1_2 position comparison total_length current_length lens1_2 pivot_length boundary scan NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41
  have PreH22 : (comparison = (0 : Int)) := NewPreH26
  have PreH25 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre) := rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37
  have PreH27 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position) := NewPreH39
  have hc := ConcatCompareOutcome_zero__compare_outcome rows1_2 lens1_2 scan high_pre position PreH27 (by
    rw [concat_item_digits_Zlength__compare_outcome rows1_2 lens1_2 count_pre number_width_pre scan high_pre PreH25 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
    omega)
  sep_apply (store_int_undef_store_int naive_C_Rules (&("position")) position)
  Exists flat1_2 rows1_2 lens1_2
  Intros_p hvalid0
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hc
    | (rw [PreH22]; exact hc)
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_entail_wit_6_2 : quicksort_numbers_entail_wit_6_2 := by
  unfold quicksort_numbers_entail_wit_6_2
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre rows1_2 lens1_2 flat1_2 scan boundary pivot_length current_length total_length comparison position left_digit right_digit NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42 NewPreH43
  have PreH1 : (left_digit ≠ right_digit) := NewPreH1
  have PreH22 : (comparison = (0 : Int)) := NewPreH26
  have PreH25 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position))) := NewPreH29
  have PreH26 : (right_digit = (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position))) := NewPreH30
  have PreH27 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre) := rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39
  have PreH29 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position) := NewPreH41
  have hc := ConcatCompareOutcome_difference__compare_outcome rows1_2 lens1_2 scan high_pre position PreH29 (by
    rw [concat_item_digits_Zlength__compare_outcome rows1_2 lens1_2 count_pre number_width_pre scan high_pre PreH27 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
    omega) (by rw [←PreH25,←PreH26]; exact PreH1)
  rw [←PreH25,←PreH26] at hc
  sep_apply (store_int_undef_store_int naive_C_Rules (&("position")) position)
  Exists flat1_2 rows1_2 lens1_2
  Intros_p hvalid0
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hc
    | (rw [PreH22]; exact hc)
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_entail_wit_7 : quicksort_numbers_entail_wit_7 := by
  unfold quicksort_numbers_entail_wit_7
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre rows1 lens1_2 flat1 scan boundary pivot_length current_length total_length comparison NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38
  have hspan := row_span_bounds (boundary+1) count_pre number_width_pre (by omega) (by omega) (by omega)
  have PreH22 : (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) := rows_from_annotation rows1 lens1_2 count_pre number_width_pre NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34
  have PreH23 : (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) := NewPreH35
  have he : boundary+1-1=boundary := by omega
  have hs := SwapRowsPrefix_zero__scan_row_swap rows1 lens1_2 count_pre number_width_pre (boundary+1) scan PreH22 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  repeat sep_apply (store_int_undef_store_int naive_C_Rules _ _)
  Exists flat1 rows1 rows1 lens1_2
  Intros_p hvalid0
  Intros_p hvalid1
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hs
    | (rw [he]; exact PreH23)
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_entail_wit_8 : quicksort_numbers_entail_wit_8 := by
  unfold quicksort_numbers_entail_wit_8
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre flat_now_2 rows_now_2 comparison rows_before_2 lens1_2 pivot_length column scan boundary NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39
  have PreH35 : (RowsWellFormed rows_before_2 lens1_2 count_pre number_width_pre) := rows_from_annotation rows_before_2 lens1_2 count_pre number_width_pre NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33
  have PreH39 : (SwapRowsPrefix rows_before_2 rows_now_2 boundary scan column number_width_pre) := NewPreH37
  have PreH41 : (FlatRows flat_now_2 rows_now_2 count_pre number_width_pre) := NewPreH39
  have hb := PreH35.2.2 boundary ⟨by omega,by omega⟩
  have hs := PreH35.2.2 scan ⟨by omega,by omega⟩
  obtain ⟨rows_next,hflat,hswap⟩ := FlatRows_swap_progress_step__scan_row_swap flat_now_2 rows_before_2 rows_now_2 count_pre number_width_pre boundary scan column PreH41 PreH35.1 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ hb.1 hs.1 ⟨by omega,by omega⟩ PreH39
  Exists (replace_Znth (scan*number_width_pre+column) (Znth (boundary*number_width_pre+column) flat_now_2 0) (replace_Znth (boundary*number_width_pre+column) (Znth (scan*number_width_pre+column) flat_now_2 0) flat_now_2)) rows_next rows_before_2 lens1_2
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hflat
    | exact hswap
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_entail_wit_9_1 : quicksort_numbers_entail_wit_9_1 := by
  unfold quicksort_numbers_entail_wit_9_1
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre flat_now rows_now comparison rows_before lens1_2 pivot_length column scan boundary NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39
  have PreH16 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int)))) := NewPreH22
  have PreH19 : (RowsWellFormed rows_before lens1_2 count_pre number_width_pre) := rows_from_annotation rows_before lens1_2 count_pre number_width_pre NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33
  have PreH20 : (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (boundary - 1) scan) := NewPreH34
  have PreH21 : (ConcatCompareOutcome rows_before lens1_2 scan high_pre comparison) := NewPreH35
  have PreH22 : (comparison > (0 : Int)) := NewPreH36
  have PreH23 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre) := NewPreH37
  have PreH24 : ((sum (lens1_2)) = (sum (lens))) := NewPreH38
  have hr := PreH19.1
  have hl := PreH19.2.1
  have he := SwapRowsPrefix_complete__scan_advance rows_before rows_now lens1_2 count_pre number_width_pre boundary scan column PreH19 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega) PreH23
  have hp := PartitionScanState_swap_advance__scan_advance rows rows_before lens lens1_2 count_pre number_width_pre low_pre high_pre boundary scan comparison PreH19 PreH20 PreH21 PreH22 (by omega) (by omega) (by omega) (by omega) (by omega)
  have hw := RowsWellFormed_swap_Znth__scan_advance rows_before lens1_2 count_pre number_width_pre boundary scan PreH19 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  rw [←he] at hp hw
  have hsum : sum (swap_Znth 0 boundary scan lens1_2)=sum lens := by
    rw [sum_swap_Znth__pivot_finalization lens1_2 boundary scan ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
    exact PreH24
  have hpivot : pivot_length=Znth high_pre (swap_Znth 0 boundary scan lens1_2) 0 := by
    rw [Znth_swap_Znth_diff__scan_advance Int 0 boundary scan high_pre lens1_2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega) (by omega)]
    exact PreH16
  sep_apply (store_int_undef_store_int naive_C_Rules (&("comparison")) comparison)
  Exists flat_now rows_now (swap_Znth 0 boundary scan lens1_2)
  Intros_p hvalid0
  split_pure_spatial
  · unfold swap_Znth
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hp
    | exact hw
    | exact hsum
    | exact hpivot
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_entail_wit_9_2 : quicksort_numbers_entail_wit_9_2 := by
  unfold quicksort_numbers_entail_wit_9_2
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre rows1_2 lens1_2 flat1_2 scan boundary pivot_length current_length total_length comparison NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38
  have PreH1 : (comparison <= (0 : Int)) := NewPreH1
  have PreH23 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan) := NewPreH35
  have PreH24 : (ConcatCompareOutcome rows1_2 lens1_2 scan high_pre comparison) := NewPreH36
  have hnot := ConcatCompareOutcome_nonpositive_not_item_before__scan_advance rows1_2 lens1_2 scan high_pre comparison PreH24 PreH1
  have hs := PartitionScanState_advance_nonbefore__scan_advance rows rows1_2 lens lens1_2 low_pre high_pre boundary scan PreH23 hnot
  repeat sep_apply (store_int_undef_store_int naive_C_Rules _ _)
  Exists flat1_2 rows1_2 lens1_2
  Intros_p hvalid0
  Intros_p hvalid1
  Intros_p hvalid2
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hs
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_entail_wit_10 : quicksort_numbers_entail_wit_10 := by
  unfold quicksort_numbers_entail_wit_10
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre rows1_2 lens1_2 flat1_2 boundary scan pivot_length NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29
  Exists flat1_2 rows1_2 lens1_2
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_entail_wit_11 : quicksort_numbers_entail_wit_11 := by
  unfold quicksort_numbers_entail_wit_11
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre flat1 rows1 lens1_2 pivot_length scan boundary NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31
  have hspan := row_span_bounds (boundary+1) count_pre number_width_pre (by omega) (by omega) (by omega)
  have PreH18 : (RowsWellFormed rows1 lens1_2 count_pre number_width_pre) := rows_from_annotation rows1 lens1_2 count_pre number_width_pre NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28
  have PreH19 : (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan) := NewPreH29
  have hs : scan=high_pre := by omega
  subst scan
  have he : boundary+1-1=boundary := by omega
  have hz := SwapRowsPrefix_zero__scan_advance rows1 lens1_2 count_pre number_width_pre (boundary+1) high_pre PreH18 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  repeat sep_apply (store_int_undef_store_int naive_C_Rules _ _)
  Exists flat1 rows1 rows1 lens1_2
  Intros_p hvalid0
  Intros_p hvalid1
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hz
    | (rw [he]; exact PreH19)
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_entail_wit_12 : quicksort_numbers_entail_wit_12 := by
  unfold quicksort_numbers_entail_wit_12
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre flat_now_2 rows_now_2 rows_before_2 lens1_2 pivot_length column pivot NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34
  have PreH30 : (RowsWellFormed rows_before_2 lens1_2 count_pre number_width_pre) := rows_from_annotation rows_before_2 lens1_2 count_pre number_width_pre NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30
  have PreH32 : (SwapRowsPrefix rows_before_2 rows_now_2 pivot high_pre column number_width_pre) := NewPreH32
  have PreH34 : (FlatRows flat_now_2 rows_now_2 count_pre number_width_pre) := NewPreH34
  have hp := PreH30.2.2 pivot ⟨by omega,by omega⟩
  have hh := PreH30.2.2 high_pre ⟨by omega,by omega⟩
  obtain ⟨rows_next,hflat,hswap⟩ := FlatRows_swap_progress_step__scan_row_swap flat_now_2 rows_before_2 rows_now_2 count_pre number_width_pre pivot high_pre column PreH34 PreH30.1 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ hp.1 hh.1 ⟨by omega,by omega⟩ PreH32
  Exists (replace_Znth (high_pre*number_width_pre+column) (Znth (pivot*number_width_pre+column) flat_now_2 0) (replace_Znth (pivot*number_width_pre+column) (Znth (high_pre*number_width_pre+column) flat_now_2 0) flat_now_2)) rows_next rows_before_2 lens1_2
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hflat
    | exact hswap
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_entail_wit_13 : quicksort_numbers_entail_wit_13 := by
  unfold quicksort_numbers_entail_wit_13
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre flat_now rows_now rows_before lens1_2 pivot_length column pivot NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34
  have PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) ((0 : Int)))) := NewPreH19
  have PreH18 : (RowsWellFormed rows_before lens1_2 count_pre number_width_pre) := rows_from_annotation rows_before lens1_2 count_pre number_width_pre NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30
  have PreH19 : (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (pivot - 1) high_pre) := NewPreH31
  have PreH20 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre) := NewPreH32
  have PreH21 : ((sum (lens1_2)) = (sum (lens))) := NewPreH33
  have hr := PreH18.1
  have hl := PreH18.2.1
  have hc : column=number_width_pre := by omega
  subst column
  have hpw := PreH18.2.2 pivot ⟨by omega,by omega⟩
  have hhw := PreH18.2.2 high_pre ⟨by omega,by omega⟩
  have he := SwapRowsPrefix_complete__pivot_finalization rows_before rows_now pivot high_pre number_width_pre hpw.1 hhw.1 PreH20
  let after := replace_Znth pivot pivot_length (replace_Znth high_pre (Znth pivot lens1_2 0) lens1_2)
  have hea : after=swap_Znth 0 pivot high_pre lens1_2 := by
    dsimp only [after]
    rw [PreH15]
    exact swap_Znth_reverse__pivot_finalization 0 pivot high_pre lens1_2 (by omega) (by omega)
  have hw := RowsWellFormed_swap__pivot_finalization rows_before lens1_2 count_pre number_width_pre pivot high_pre PreH18 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hp := PairedPermutation_swap__pivot_finalization rows rows_before lens lens1_2 pivot high_pre PreH19.1 (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hs := SameOutsidePairedRange_swap_inside__pivot_finalization rows rows_before lens lens1_2 low_pre high_pre pivot high_pre PreH19.2.1 (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hpart := PartitionScanState_finalize__pivot_finalization rows rows_before lens lens1_2 count_pre number_width_pre low_pre high_pre pivot PreH18 PreH19 (by omega) (by omega) (by omega) ⟨by omega,by omega⟩
  rw [←he,←hea] at hw hp hs hpart
  have hsum : sum after=sum lens := by
    rw [hea,sum_swap_Znth__pivot_finalization lens1_2 pivot high_pre ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
    exact PreH21
  sep_apply (store_int_undef_store_int naive_C_Rules (&("pivot_length")) pivot_length)
  Exists flat_now (replace_Znth pivot pivot_length (replace_Znth high_pre (Znth pivot lens1_2 0) lens1_2)) rows_now
  Intros_p hvalid0
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hw
    | exact hp
    | exact hs
    | exact hpart
    | exact hsum
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_safety_wit_6_split_goal_1 : quicksort_numbers_safety_wit_6_split_goal_1 := by
  unfold quicksort_numbers_safety_wit_6_split_goal_1
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre flat1 rows1 lens1 pivot_length scan boundary NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31
  have PreH18 : (RowsWellFormed rows1 lens1 count_pre number_width_pre) := rows_from_annotation rows1 lens1 count_pre number_width_pre NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28
  have hb := PreH18.2.2 scan ⟨by omega,by omega⟩
  dump_pre_spatial
  change _≤2147483647
  omega


theorem proof_of_quicksort_numbers_safety_wit_6_split_goal_2 : quicksort_numbers_safety_wit_6_split_goal_2 := by
  unfold quicksort_numbers_safety_wit_6_split_goal_2
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre flat1 rows1 lens1 pivot_length scan boundary NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31
  have PreH18 : (RowsWellFormed rows1 lens1 count_pre number_width_pre) := rows_from_annotation rows1 lens1 count_pre number_width_pre NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28
  have hb := PreH18.2.2 scan ⟨by omega,by omega⟩
  dump_pre_spatial
  change (-2147483648:Int)≤_
  omega


theorem proof_of_quicksort_numbers_safety_wit_19_split_goal_1 : quicksort_numbers_safety_wit_19_split_goal_1 := by
  unfold quicksort_numbers_safety_wit_19_split_goal_1
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre rows1 lens1 flat1 scan boundary pivot_length current_length total_length comparison position left_digit right_digit NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42 NewPreH43
  have PreH27 : (RowsWellFormed rows1 lens1 count_pre number_width_pre) := rows_from_annotation rows1 lens1 count_pre number_width_pre NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39
  subst left_digit right_digit
  have hl := concat_left_digit_bounds__safety_arithmetic rows1 lens1 count_pre number_width_pre scan high_pre position PreH27 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hr := concat_right_digit_bounds__safety_arithmetic rows1 lens1 count_pre number_width_pre scan high_pre position PreH27 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  dump_pre_spatial
  change _≤2147483647
  omega


theorem proof_of_quicksort_numbers_safety_wit_19_split_goal_2 : quicksort_numbers_safety_wit_19_split_goal_2 := by
  unfold quicksort_numbers_safety_wit_19_split_goal_2
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre rows1 lens1 flat1 scan boundary pivot_length current_length total_length comparison position left_digit right_digit NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39 NewPreH40 NewPreH41 NewPreH42 NewPreH43
  have PreH27 : (RowsWellFormed rows1 lens1 count_pre number_width_pre) := rows_from_annotation rows1 lens1 count_pre number_width_pre NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39
  subst left_digit right_digit
  have hl := concat_left_digit_bounds__safety_arithmetic rows1 lens1 count_pre number_width_pre scan high_pre position PreH27 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hr := concat_right_digit_bounds__safety_arithmetic rows1 lens1 count_pre number_width_pre scan high_pre position PreH27 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  dump_pre_spatial
  change (-2147483648:Int)≤_
  omega


theorem proof_of_quicksort_numbers_return_wit_1 : quicksort_numbers_return_wit_1 := by
  unfold quicksort_numbers_return_wit_1
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre pivot rows1_2 lens1_2 flat1_2 rows2 lens2 flat2 lens1_3 flat1_3 rows1_3 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35 NewPreH36 NewPreH37 NewPreH38 NewPreH39
  have hTransport0 := RowsWellFormed_permutation__annotation rows2 rows1_3 lens2 lens1_3 count_pre number_width_pre ((RowsWellFormed_permutation__annotation rows1_2 rows2 lens1_2 lens2 count_pre number_width_pre (rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34) NewPreH7).1) NewPreH2
  have hTransportSum0 := hTransport0.2
  have hTransport1 := RowsWellFormed_permutation__annotation rows1_2 rows2 lens1_2 lens2 count_pre number_width_pre (rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34) NewPreH7
  have hTransportSum1 := hTransport1.2
  have PreH1 : (RowsWellFormed rows1_3 lens1_3 count_pre number_width_pre) := (RowsWellFormed_permutation__annotation rows2 rows1_3 lens2 lens1_3 count_pre number_width_pre ((RowsWellFormed_permutation__annotation rows1_2 rows2 lens1_2 lens2 count_pre number_width_pre (rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34) NewPreH7).1) NewPreH2).1
  have PreH3 : (PairedPermutation rows2 rows1_3 lens2 lens1_3) := NewPreH2
  have PreH4 : (SameOutsidePairedRange rows2 rows1_3 lens2 lens1_3 (pivot + 1) high_pre) := NewPreH3
  have PreH5 : (GreedySortedRange rows1_3 lens1_3 (pivot + 1) high_pre) := NewPreH4
  have PreH8 : (RowsWellFormed rows2 lens2 count_pre number_width_pre) := (RowsWellFormed_permutation__annotation rows1_2 rows2 lens1_2 lens2 count_pre number_width_pre (rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34) NewPreH7).1
  have PreH10 : (PairedPermutation rows1_2 rows2 lens1_2 lens2) := NewPreH7
  have PreH11 : (SameOutsidePairedRange rows1_2 rows2 lens1_2 lens2 low_pre (pivot - 1)) := NewPreH8
  have PreH12 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1)) := NewPreH9
  have PreH27 : (PairedPermutation rows rows1_2 lens lens1_2) := NewPreH35
  have PreH28 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre) := NewPreH36
  have PreH29 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot) := NewPreH37
  have hpart2 := greedy_partitioned_preserved_left__quicksort_range_composition rows1_2 rows2 lens1_2 lens2 count_pre number_width_pre low_pre high_pre pivot PreH8 PreH10 PreH11 (by omega) (by omega) PreH29
  have hpart3 := greedy_partitioned_preserved_right__quicksort_range_composition rows2 rows1_3 lens2 lens1_3 count_pre number_width_pre low_pre high_pre pivot PreH1 PreH3 PreH4 (by omega) (by omega) hpart2
  have hleft := greedy_sorted_range_preserved_outside__quicksort_range_composition rows2 rows1_3 lens2 lens1_3 (pivot+1) high_pre low_pre (pivot-1) PreH4 (by omega) (by have := PreH8.1; omega) (by intro k hk; exact Or.inl (by omega)) PreH12
  have hsorted := greedy_sorted_range_combine__quicksort_range_composition rows1_3 lens1_3 count_pre number_width_pre low_pre high_pre pivot PreH1 (by omega) (by omega) hpart3 hleft PreH5
  have hs12 := same_outside_paired_range_weaken__quicksort_range_composition rows1_2 rows2 lens1_2 lens2 low_pre (pivot-1) low_pre high_pre (by omega) (by omega) PreH11
  have hs23 := same_outside_paired_range_weaken__quicksort_range_composition rows2 rows1_3 lens2 lens1_3 (pivot+1) high_pre low_pre high_pre (by omega) (by omega) PreH4
  have hs := same_outside_paired_range_trans__quicksort_range_composition rows rows1_2 rows1_3 lens lens1_2 lens1_3 low_pre high_pre PreH28
    (same_outside_paired_range_trans__quicksort_range_composition rows1_2 rows2 rows1_3 lens1_2 lens2 lens1_3 low_pre high_pre hs12 hs23)
  have hp := paired_permutation_trans__quicksort_range_composition rows rows1_2 rows1_3 lens lens1_2 lens1_3 PreH27
    (paired_permutation_trans__quicksort_range_composition rows1_2 rows2 rows1_3 lens1_2 lens2 lens1_3 PreH10 PreH3)
  Exists lens1_3 flat1_3 rows1_3
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hsorted
    | exact hs
    | exact hp
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_return_wit_2 : quicksort_numbers_return_wit_2 := by
  unfold quicksort_numbers_return_wit_2
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre pivot rows1_2 lens1_2 flat1_2 rows2 lens2 flat2 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35
  have hTransport0 := RowsWellFormed_permutation__annotation rows1_2 rows2 lens1_2 lens2 count_pre number_width_pre (rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30) NewPreH3
  have hTransportSum0 := hTransport0.2
  have PreH2 : (RowsWellFormed rows2 lens2 count_pre number_width_pre) := (RowsWellFormed_permutation__annotation rows1_2 rows2 lens1_2 lens2 count_pre number_width_pre (rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30) NewPreH3).1
  have PreH4 : (PairedPermutation rows1_2 rows2 lens1_2 lens2) := NewPreH3
  have PreH5 : (SameOutsidePairedRange rows1_2 rows2 lens1_2 lens2 low_pre (pivot - 1)) := NewPreH4
  have PreH6 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1)) := NewPreH5
  have PreH21 : (PairedPermutation rows rows1_2 lens lens1_2) := NewPreH31
  have PreH22 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre) := NewPreH32
  have PreH23 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot) := NewPreH33
  have hpart := greedy_partitioned_preserved_left__quicksort_range_composition rows1_2 rows2 lens1_2 lens2 count_pre number_width_pre low_pre high_pre pivot PreH2 PreH4 PreH5 (by omega) (by omega) PreH23
  have hbase := greedy_sorted_range_base__quicksort_range_composition rows2 lens2 (pivot+1) high_pre (by omega)
  have hsorted := greedy_sorted_range_combine__quicksort_range_composition rows2 lens2 count_pre number_width_pre low_pre high_pre pivot PreH2 (by omega) (by omega) hpart PreH6 hbase
  have hchange := same_outside_paired_range_weaken__quicksort_range_composition rows1_2 rows2 lens1_2 lens2 low_pre (pivot-1) low_pre high_pre (by omega) (by omega) PreH5
  have hs := same_outside_paired_range_trans__quicksort_range_composition rows rows1_2 rows2 lens lens1_2 lens2 low_pre high_pre PreH22 hchange
  have hp := paired_permutation_trans__quicksort_range_composition rows rows1_2 rows2 lens lens1_2 lens2 PreH21 PreH4
  Exists lens2 flat2 rows2
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hsorted
    | exact hs
    | exact hp
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_return_wit_3 : quicksort_numbers_return_wit_3 := by
  unfold quicksort_numbers_return_wit_3
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre pivot rows1_2 lens1_2 flat1_2 lens1_3 flat1_3 rows1_3 NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33 NewPreH34 NewPreH35
  have hTransport0 := RowsWellFormed_permutation__annotation rows1_2 rows1_3 lens1_2 lens1_3 count_pre number_width_pre (rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30) NewPreH2
  have hTransportSum0 := hTransport0.2
  have PreH1 : (RowsWellFormed rows1_3 lens1_3 count_pre number_width_pre) := (RowsWellFormed_permutation__annotation rows1_2 rows1_3 lens1_2 lens1_3 count_pre number_width_pre (rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30) NewPreH2).1
  have PreH3 : (PairedPermutation rows1_2 rows1_3 lens1_2 lens1_3) := NewPreH2
  have PreH4 : (SameOutsidePairedRange rows1_2 rows1_3 lens1_2 lens1_3 (pivot + 1) high_pre) := NewPreH3
  have PreH5 : (GreedySortedRange rows1_3 lens1_3 (pivot + 1) high_pre) := NewPreH4
  have PreH21 : (PairedPermutation rows rows1_2 lens lens1_2) := NewPreH31
  have PreH22 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre) := NewPreH32
  have PreH23 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot) := NewPreH33
  have hpart := greedy_partitioned_preserved_right__quicksort_range_composition rows1_2 rows1_3 lens1_2 lens1_3 count_pre number_width_pre low_pre high_pre pivot PreH1 PreH3 PreH4 (by omega) (by omega) PreH23
  have hbase := greedy_sorted_range_base__quicksort_range_composition rows1_3 lens1_3 low_pre (pivot-1) (by omega)
  have hsorted := greedy_sorted_range_combine__quicksort_range_composition rows1_3 lens1_3 count_pre number_width_pre low_pre high_pre pivot PreH1 (by omega) (by omega) hpart hbase PreH5
  have hchange := same_outside_paired_range_weaken__quicksort_range_composition rows1_2 rows1_3 lens1_2 lens1_3 (pivot+1) high_pre low_pre high_pre (by omega) (by omega) PreH4
  have hs := same_outside_paired_range_trans__quicksort_range_composition rows rows1_2 rows1_3 lens lens1_2 lens1_3 low_pre high_pre PreH22 hchange
  have hp := paired_permutation_trans__quicksort_range_composition rows rows1_2 rows1_3 lens lens1_2 lens1_3 PreH21 PreH3
  Exists lens1_3 flat1_3 rows1_3
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact hsorted
    | exact hs
    | exact hp
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_return_wit_4 : quicksort_numbers_return_wit_4 := by
  unfold quicksort_numbers_return_wit_4
  left
  intro flat lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22
  have PreH13 : (RowsWellFormed rows lens count_pre number_width_pre) := rows_from_annotation rows lens count_pre number_width_pre NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21
  Exists lens flat rows
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | (apply greedy_sorted_range_base__quicksort_range_composition; omega)
    | exact same_outside_paired_range_refl__quicksort_range_composition rows lens low_pre high_pre
    | exact paired_permutation_refl__quicksort_range_composition rows lens (PreH13.1.trans PreH13.2.1.symm)
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_concatenating_numbers_entail_wit_3 : concatenating_numbers_entail_wit_3 := by
  unfold concatenating_numbers_entail_wit_3
  left
  intro lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre flat1_2 result_length output_2 lens1_2 rows1_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26
  have hspan := row_span_bounds i count_pre number_width_pre (by omega) (by omega) (by omega)
  have PreH10 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre) := rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18
  have PreH14 : (output_2 = (ConcatenatedPrefix (rows1_2) (lens1_2) (i))) := NewPreH22
  have hl := PreH10.2.2 i ⟨by omega,by omega⟩
  have ho : output_2=ConcatenatedOutputPrefix rows1_2 lens1_2 i 0 := by rw [ConcatenatedOutputPrefix_zero__output_setup]; exact PreH14
  have hcapacity : result_length < sum lens := by
    have hb := ConcatenatedOutputPrefix_lt_sum__output_inner_loop rows1_2 lens1_2 count_pre number_width_pre i 0 PreH10 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    rw [←ho] at hb
    omega
  Exists flat1_2 output_2 rows1_2 lens1_2
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact (fun _ => hcapacity)
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | exact ho
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_concatenating_numbers_entail_wit_4 : concatenating_numbers_entail_wit_4 := by
  unfold concatenating_numbers_entail_wit_4
  left
  intro lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre flat1_2 output_2 rows1_2 result_length lens1_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33
  have PreH28 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre) := rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25
  have PreH32 : (output_2 = (ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j))) := NewPreH29
  have PreH33 : (result_length = (Zlength (output_2))) := NewPreH30
  have PreH36 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre) := NewPreH33
  have hnext : output_2 ++ [Znth (i*number_width_pre+j) flat1_2 0] = ConcatenatedOutputPrefix rows1_2 lens1_2 i (j+1) := by
    rw [PreH32]
    exact ConcatenatedOutputPrefix_append__output_inner_loop flat1_2 rows1_2 lens1_2 count_pre number_width_pre i j PreH36 PreH28 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hcapacity : j+1 < Znth i lens1_2 0 → result_length+1 < sum lens := by
    intro hj
    have hb := ConcatenatedOutputPrefix_lt_sum__output_inner_loop rows1_2 lens1_2 count_pre number_width_pre i (j+1) PreH28 ⟨by omega,by omega⟩ ⟨by omega,hj⟩
    rw [←hnext, Zlength_app] at hb
    simp only [Zlength_cons, Zlength_nil] at hb
    omega
  Exists flat1_2 (output_2++[Znth (i*number_width_pre+j) flat1_2 0]) rows1_2 lens1_2
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | exact hcapacity
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | (rw [Zlength_app,←PreH33]; simp only [Zlength_cons,Zlength_nil]; omega)
    | (rw [PreH32]; exact ConcatenatedOutputPrefix_append__output_inner_loop flat1_2 rows1_2 lens1_2 count_pre number_width_pre i j PreH36 PreH28 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩)
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_concatenating_numbers_entail_wit_5 : concatenating_numbers_entail_wit_5 := by
  unfold concatenating_numbers_entail_wit_5
  left
  intro lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre flat1_2 output_2 rows1_2 result_length lens1_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25 NewPreH26 NewPreH27 NewPreH28 NewPreH29 NewPreH30 NewPreH31 NewPreH32 NewPreH33
  have PreH14 : (RowsWellFormed rows1_2 lens1_2 count_pre number_width_pre) := rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre NewPreH17 NewPreH18 NewPreH19 NewPreH20 NewPreH21 NewPreH22 NewPreH23 NewPreH24 NewPreH25
  have PreH18 : (output_2 = (ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j))) := NewPreH29
  Exists flat1_2 output_2 lens1_2 rows1_2
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | (rw [PreH18,show j=Znth i lens1_2 0 by omega]; exact ConcatenatedOutputPrefix_full_row__output_inner_loop rows1_2 lens1_2 count_pre number_width_pre i PreH14 ⟨by omega,by omega⟩)
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_concatenating_numbers_entail_wit_1 : concatenating_numbers_entail_wit_1 := by
  unfold concatenating_numbers_entail_wit_1
  left
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hwidth := decimal_rows_lengths_from_map rows number_width_pre PreH9
  have hflat : FlatRows flat rows count_pre number_width_pre := by
    refine ⟨?_, PreH7, ?_⟩
    · rw [PreH16, decimal_rows_flat_length rows number_width_pre hwidth, PreH7]
    · intro i hi
      rw [PreH16]
      exact decimal_rows_flat_row rows number_width_pre i (by omega) hwidth (by rw [PreH7]; exact hi)
  rw [PreH16]
  rw [PreH16] at hflat
  sep_apply (decimal_rows_flatten rows numbers_pre count_pre number_width_pre (by omega))
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_concatenating_numbers_entail_wit_2_1 : concatenating_numbers_entail_wit_2_1 := by
  unfold concatenating_numbers_entail_wit_2_1
  left
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre lens1_2 flat1_2 rows1_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hWF := rows_from_annotation rows lens count_pre number_width_pre PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  obtain ⟨hWF1, hsum⟩ := RowsWellFormed_permutation__annotation rows rows1_2 lens lens1_2 count_pre number_width_pre hWF PreH2
  have hsorted : GreedySorted rows1_2 lens1_2 := by
    intro i j hij
    apply PreH4 i j
    have hr := hWF1.1
    omega
  Exists flat1_2 ([] : List Int) lens1_2 rows1_2
  rw [ConcatenatedPrefix_zero__output_setup]
  sep_apply (intArray.undef_full_to_undef_seg result_pre (sum lens))
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (intArray.seg_empty result_pre 0 0)).2)
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_concatenating_numbers_entail_wit_2_2 : concatenating_numbers_entail_wit_2_2 := by
  unfold concatenating_numbers_entail_wit_2_2
  left
  intro flat lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hWF := rows_from_annotation rows lens count_pre number_width_pre PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hcount : count_pre = 1 := by omega
  have hperm := paired_permutation_refl__quicksort_range_composition rows lens (PreH8.trans PreH9.symm)
  have hsorted : GreedySorted rows lens := by
    intro i j hij
    have he : i = j := by omega
    subst j
    exact ⟨rfl, Or.inl rfl⟩
  Exists flat ([] : List Int) lens rows
  rw [ConcatenatedPrefix_zero__output_setup]
  sep_apply (intArray.undef_full_to_undef_seg result_pre (sum lens))
  sep_apply_right (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (intArray.seg_empty result_pre 0 0)).2)
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | assumption
    | omega
    | rfl
    | trivial


theorem proof_of_quicksort_numbers_partial_solve_wit_23_pure : quicksort_numbers_partial_solve_wit_23_pure := by
  unfold quicksort_numbers_partial_solve_wit_23_pure
  left
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre pivot rows1 lens1 flat1 rows2 lens2 flat2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35
  have hWF := rows_from_annotation rows1 lens1 count_pre number_width_pre PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  obtain ⟨hWF2, hsum⟩ := RowsWellFormed_permutation__annotation rows1 rows2 lens1 lens2 count_pre number_width_pre hWF PreH3
  split_pures <;> dump_pre_spatial
  all_goals first
  | (solve | apply annotation_rows_length; assumption)
  | (solve | apply annotation_lens_length; assumption)
  | (solve | apply annotation_rows_map; assumption)
  | (solve | apply annotation_lens_lower; assumption)
  | (solve | apply annotation_lens_upper; assumption)
  | (solve | apply annotation_head_lower; assumption)
  | (solve | apply annotation_head_upper; assumption)
  | (solve | apply annotation_digits_lower; assumption)
  | (solve | apply annotation_digits_upper; assumption)
  | assumption
  | omega


theorem proof_of_quicksort_numbers_safety_wit_6 : quicksort_numbers_safety_wit_6 := by
  unfold quicksort_numbers_safety_wit_6
  right
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre flat1 rows1 lens1 pivot_length scan boundary PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31
  have hw := rows_from_annotation rows1 lens1 count_pre number_width_pre PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  have hb := hw.2.2 scan ⟨by omega, by omega⟩
  split_pures <;> dump_pre_spatial
  all_goals first
  | (solve | change _ ≤ (2147483647 : Int); omega)
  | (solve | change (-2147483648 : Int) ≤ _; omega)


theorem proof_of_quicksort_numbers_safety_wit_19 : quicksort_numbers_safety_wit_19 := by
  unfold quicksort_numbers_safety_wit_19
  right
  intro lens rows numbers_pre lengths_pre count_pre number_width_pre low_pre high_pre rows1 lens1 flat1 scan boundary pivot_length current_length total_length comparison position left_digit right_digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43
  have hw := rows_from_annotation rows1 lens1 count_pre number_width_pre PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  subst left_digit right_digit
  have hleft := concat_left_digit_bounds__safety_arithmetic rows1 lens1 count_pre number_width_pre scan high_pre position hw ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  have hright := concat_right_digit_bounds__safety_arithmetic rows1 lens1 count_pre number_width_pre scan high_pre position hw ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  split_pures <;> dump_pre_spatial
  all_goals first
  | (solve | change _ ≤ (2147483647 : Int); omega)
  | (solve | change (-2147483648 : Int) ≤ _; omega)


theorem proof_of_concatenating_numbers_return_wit_1 : concatenating_numbers_return_wit_1 := by
  unfold concatenating_numbers_return_wit_1
  left
  intro lens rows numbers_pre count_pre number_width_pre lengths_pre result_pre flat1 result_length output_2 lens1_2 rows1_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  have hWF := rows_from_annotation rows1_2 lens1_2 count_pre number_width_pre PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hi : i = count_pre := by omega
  have hout : output_2 = concatenate_rows rows1_2 lens1_2 := by
    rw [PreH22, hi, ConcatenatedPrefix_full__largest_concatenation_final rows1_2 lens1_2 count_pre number_width_pre hWF]
  have hlen : Zlength output_2 = sum lens := by
    rw [hout, RowsWellFormed_concatenate_rows_length__largest_concatenation_final rows1_2 lens1_2 count_pre number_width_pre hWF]
    exact PreH21
  have hresult : result_length = sum lens := by omega
  have hmax : LargestConcatenation rows lens output_2 := by
    refine ⟨paired_items rows1_2 lens1_2, ⟨PreH19.2.2, ?_⟩, hout.symm⟩
    intro alternative hp
    exact ordered_items_maximize_concatenation__largest_concatenation_final _ _
      (greedy_sorted_orders_paired_items__largest_concatenation_final rows1_2 lens1_2 (PreH10.trans PreH11.symm) PreH20)
      (PreH19.2.2.symm.trans hp)
  have hwidth := decimal_rows_lengths_from_map rows1_2 number_width_pre PreH12
  have hdata := decimal_rows_concat_unique rows1_2 flat1 count_pre number_width_pre (by omega) hwidth PreH10 PreH26.1 PreH26.2.2
  Exists lens1_2 rows1_2 output_2
  rw [hresult]
  sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (intArray.undef_seg_empty result_pre (sum lens))).1)
  sep_apply (intArray.seg_to_full result_pre 0 (sum lens) output_2)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  rw [hdata]
  sep_apply (decimal_rows_unflatten rows1_2 numbers_pre count_pre number_width_pre (by omega) hwidth PreH10)
  split_pure_spatial
  · cancel
    try exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial
    all_goals first
    | (solve | apply annotation_rows_length; assumption)
    | (solve | apply annotation_lens_length; assumption)
    | (solve | apply annotation_rows_map; assumption)
    | (solve | apply annotation_lens_lower; assumption)
    | (solve | apply annotation_lens_upper; assumption)
    | (solve | apply annotation_head_lower; assumption)
    | (solve | apply annotation_head_upper; assumption)
    | (solve | apply annotation_digits_lower; assumption)
    | (solve | apply annotation_digits_upper; assumption)
    | assumption
    | omega
    | rfl
    | trivial


end SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_proof_manual
